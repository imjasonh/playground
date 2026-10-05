package config

import (
	"errors"
	"io"
	"maps"
	"os"
	"slices"
	"testing"

	"cel.dev/cel-go/cel"
	"cel.dev/cel-go/ext"
	"go.yaml.in/yaml/v3"
)

// manifest is a document in policy.yaml, with the fields of a
// ValidatingAdmissionPolicy or ValidatingAdmissionPolicyBinding that the
// tests read.
type manifest struct {
	Kind     string
	Metadata struct{ Name string }
	Spec     struct {
		FailurePolicy    string `yaml:"failurePolicy"`
		MatchConstraints struct {
			ResourceRules []struct{ Operations, Resources []string } `yaml:"resourceRules"`
		} `yaml:"matchConstraints"`
		MatchConditions []struct{ Name, Expression string } `yaml:"matchConditions"`
		Variables       []struct{ Name, Expression string }
		Validations     []struct {
			Expression, Message string
			MessageExpression   string `yaml:"messageExpression"`
		}
		PolicyName        string   `yaml:"policyName"`
		ValidationActions []string `yaml:"validationActions"`
		ParamRef          *struct {
			ParameterNotFoundAction string `yaml:"parameterNotFoundAction"`
		} `yaml:"paramRef"`
	}
}

func manifests(t *testing.T) []manifest {
	t.Helper()
	f, err := os.Open("policy.yaml")
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	dec := yaml.NewDecoder(f)
	var docs []manifest
	for {
		var m manifest
		err := dec.Decode(&m)
		if errors.Is(err, io.EOF) {
			return docs
		}
		if err != nil {
			t.Fatal(err)
		}
		docs = append(docs, m)
	}
}

func find(t *testing.T, kind, name string) manifest {
	t.Helper()
	for _, m := range manifests(t) {
		if m.Kind == kind && m.Metadata.Name == name {
			return m
		}
	}
	t.Fatalf("policy.yaml has no %s %s", kind, name)
	return manifest{}
}

// policy is a ValidatingAdmissionPolicy with its expressions compiled in the
// parts of the API server's CEL environment that the policies use.
type policy struct {
	m           manifest
	conditions  []cel.Program
	variables   []cel.Program
	validations []cel.Program
	messages    []cel.Program
}

func compile(t *testing.T, m manifest) *policy {
	t.Helper()
	env, err := cel.NewEnv(
		cel.Variable("object", cel.DynType),
		cel.Variable("oldObject", cel.DynType),
		cel.Variable("request", cel.DynType),
		cel.Variable("namespaceObject", cel.DynType),
		cel.Variable("params", cel.DynType),
		cel.Variable("variables", cel.MapType(cel.StringType, cel.DynType)),
		cel.HomogeneousAggregateLiterals(),
		ext.Strings(ext.StringsVersion(2)),
	)
	if err != nil {
		t.Fatal(err)
	}
	prg := func(expr string) cel.Program {
		ast, iss := env.Compile(expr)
		if iss.Err() != nil {
			t.Fatalf("compiling %q: %v", expr, iss.Err())
		}
		p, err := env.Program(ast)
		if err != nil {
			t.Fatal(err)
		}
		return p
	}
	p := &policy{m: m}
	for _, c := range m.Spec.MatchConditions {
		p.conditions = append(p.conditions, prg(c.Expression))
	}
	for _, v := range m.Spec.Variables {
		p.variables = append(p.variables, prg(v.Expression))
	}
	for _, v := range m.Spec.Validations {
		if v.MessageExpression == "" {
			t.Fatalf("validation %q has no messageExpression", v.Expression)
		}
		p.validations = append(p.validations, prg(v.Expression))
		p.messages = append(p.messages, prg(v.MessageExpression))
	}
	return p
}

// request is an admission request for a Pod or one of its subresources.
type request struct {
	user        string
	operation   string
	subresource string
	namespace   string
	nsLabels    map[string]string
	object      map[string]any
	oldObject   map[string]any
}

// admit evaluates the policy for r as the API server does: it skips requests
// that matchConstraints or matchConditions leave out, evaluates the
// variables in order, and returns the message of the first validation that
// fails, or "" if they all pass.
func (p *policy) admit(t *testing.T, r request) string {
	t.Helper()
	resource := "pods"
	if r.subresource != "" {
		resource += "/" + r.subresource
	}
	matched := false
	for _, rule := range p.m.Spec.MatchConstraints.ResourceRules {
		matched = matched || slices.Contains(rule.Operations, r.operation) && slices.Contains(rule.Resources, resource)
	}
	if !matched {
		return ""
	}
	ns := map[string]any{"name": r.namespace}
	if r.nsLabels != nil {
		ns["labels"] = r.nsLabels
	}
	vars := map[string]any{}
	activation := func() map[string]any {
		a := map[string]any{
			"object":    nil,
			"oldObject": nil,
			"params":    nil,
			"request": map[string]any{
				"operation":   r.operation,
				"namespace":   r.namespace,
				"subResource": r.subresource,
				"userInfo":    map[string]any{"username": r.user},
			},
			"namespaceObject": map[string]any{"metadata": ns},
			"variables":       maps.Clone(vars),
		}
		// A nil map would become an empty CEL map, not null.
		if r.object != nil {
			a["object"] = r.object
		}
		if r.oldObject != nil {
			a["oldObject"] = r.oldObject
		}
		return a
	}
	eval := func(prg cel.Program) any {
		out, _, err := prg.Eval(activation())
		if err != nil {
			t.Fatalf("evaluating the policy for %+v: %v", r, err)
		}
		return out.Value()
	}
	for _, c := range p.conditions {
		if !eval(c).(bool) {
			return ""
		}
	}
	for i, v := range p.variables {
		out, _, err := v.Eval(activation())
		if err != nil {
			t.Fatalf("evaluating variable %s for %+v: %v", p.m.Spec.Variables[i].Name, r, err)
		}
		vars[p.m.Spec.Variables[i].Name] = out
	}
	for i, v := range p.validations {
		if !eval(v).(bool) {
			return eval(p.messages[i]).(string)
		}
	}
	return ""
}

// pod returns a Pod that the controller named controller owns, or that no
// controller owns if it's "", running as serviceAccount, or as the
// namespace's default service account if it's "".
func pod(controller, serviceAccount string) map[string]any {
	meta := map[string]any{"name": "gotest-0123456789abcdef"}
	if controller != "" {
		meta["labels"] = map[string]any{"kube.imjasonh.github.io/controller": controller}
	}
	spec := map[string]any{"containers": []any{map[string]any{"name": "test", "image": "cgr.dev/chainguard/go"}}}
	if serviceAccount != "" {
		spec["serviceAccountName"] = serviceAccount
	}
	return map[string]any{"metadata": meta, "spec": spec}
}

// gotestPod returns a Pod that check-gotest owns, after edit changes its
// spec.
func gotestPod(edit func(spec map[string]any)) map[string]any {
	p := pod("check-gotest", "")
	edit(p["spec"].(map[string]any))
	return p
}

// withContext returns check-gotest's Pod whose test container has the
// security context sc.
func withContext(sc map[string]any) map[string]any {
	return gotestPod(func(spec map[string]any) {
		spec["containers"].([]any)[0].(map[string]any)["securityContext"] = sc
	})
}

// labels returns the labels of a namespace that runs check Pods, changed by
// kv, a list of keys and values. An empty value removes the key.
func labels(kv ...string) map[string]string {
	l := map[string]string{
		"git-k8s.imjasonh.com/check-pods":    "true",
		"pod-security.kubernetes.io/enforce": "restricted",
	}
	for i := 0; i < len(kv); i += 2 {
		if kv[i+1] == "" {
			delete(l, kv[i])
		} else {
			l[kv[i]] = kv[i+1]
		}
	}
	return l
}

func TestCheckPods(t *testing.T) {
	p := compile(t, find(t, "ValidatingAdmissionPolicy", "git-k8s-check-pods"))
	const (
		gotest = "system:serviceaccount:check-gotest:check-gotest"
		review = "system:serviceaccount:check-review:check-review"
	)
	ready := labels()
	own := pod("check-gotest", "default")
	deprecated := pod("check-gotest", "")
	deprecated["spec"].(map[string]any)["serviceAccount"] = "rogue"
	appLabel := pod("", "")
	appLabel["metadata"].(map[string]any)["labels"] = map[string]any{"app.kubernetes.io/name": "check-gotest"}
	scheduled := gotestPod(func(spec map[string]any) { spec["nodeName"] = "node-a" })
	escape := gotestPod(func(spec map[string]any) {
		spec["hostPID"], spec["hostNetwork"], spec["runtimeClassName"] = true, true, "gvisor"
		spec["volumes"] = []any{map[string]any{"name": "root", "hostPath": map[string]any{"path": "/"}}}
		spec["containers"].([]any)[0].(map[string]any)["securityContext"] = map[string]any{"privileged": true}
	})
	initContainer := func(sc map[string]any) map[string]any {
		return gotestPod(func(spec map[string]any) {
			spec["initContainers"] = []any{map[string]any{"name": "fetch", "image": "cgr.dev/chainguard/git", "securityContext": sc}}
		})
	}
	// withContexts returns check-gotest's Pod whose test container has the
	// security context first, and whose init container has second.
	withContexts := func(first, second map[string]any) map[string]any {
		p := initContainer(second)
		p["spec"].(map[string]any)["containers"].([]any)[0].(map[string]any)["securityContext"] = first
		return p
	}
	ephemeral := gotestPod(func(spec map[string]any) {
		spec["ephemeralContainers"] = []any{map[string]any{"name": "debug", "image": "busybox", "securityContext": map[string]any{"privileged": true}}}
	})
	// withFields returns check-gotest's Pod whose test container also has
	// fields.
	withFields := func(fields map[string]any) map[string]any {
		return gotestPod(func(spec map[string]any) {
			maps.Copy(spec["containers"].([]any)[0].(map[string]any), fields)
		})
	}
	metadataGet := map[string]any{"httpGet": map[string]any{"host": "169.254.169.254", "path": "/", "port": 80}}
	named := func(name string, p map[string]any) map[string]any {
		p["metadata"].(map[string]any)["name"] = name
		return p
	}
	const (
		programs    = "the gotest check can't change Pods in the namespaces of git-k8s programs"
		others      = "the gotest check can change or delete only its own Pods, which have the label kube.imjasonh.github.io/controller=check-gotest"
		label       = "the gotest check's Pods need the label kube.imjasonh.github.io/controller=check-gotest"
		podName     = "the gotest check's new Pods need a name of the form gotest-ID, where ID has no hyphens"
		optedOut    = "the gotest check can't create or change Pods in namespace repos, which doesn't have the label git-k8s.imjasonh.com/check-pods=true"
		unenforced  = "the gotest check can't create or change Pods in namespace repos, which doesn't enforce the restricted Pod Security Standard at the latest version"
		account     = "the gotest check's Pods must run as their namespace's default service account"
		node        = "the gotest check can't assign its Pods to a node"
		host        = "the gotest check's Pods can't use the node's network, PID, or IPC namespace, hostPath volumes, or host ports"
		privilege   = "the gotest check's containers can't be privileged, add capabilities, unmask /proc, use the Unconfined seccomp profile, or run as host processes"
		confinement = "the gotest check's containers can't turn off AppArmor or SELinux confinement, or set sysctls"
		probeHost   = "the gotest check's probes and lifecycle handlers can't set a host"
	)
	notCheck := func(user string) string { return user + " isn't a check's service account, so it can't write Pods" }
	for _, tt := range []struct {
		name string
		r    request
		want string
	}{{
		name: "creates its Pod in a namespace that opts in and enforces restricted",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: own},
	}, {
		name: "creates its Pod in a namespace that enforces the latest version of restricted",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: labels("pod-security.kubernetes.io/enforce-version", "latest"), object: own},
	}, {
		name: "creates its Pod without naming a service account",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: pod("check-gotest", "")},
	}, {
		name: "creates its Pod with an emptyDir volume, a container port, and the restricted security context",
		r: request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: gotestPod(func(spec map[string]any) {
			spec["hostNetwork"], spec["hostPID"], spec["hostIPC"] = false, false, false
			spec["volumes"] = []any{map[string]any{"name": "src", "emptyDir": map[string]any{}}}
			spec["securityContext"] = map[string]any{"runAsNonRoot": true, "seccompProfile": map[string]any{"type": "RuntimeDefault"}, "windowsOptions": map[string]any{"hostProcess": false}}
			c := spec["containers"].([]any)[0].(map[string]any)
			c["ports"] = []any{map[string]any{"containerPort": 8080}, map[string]any{"containerPort": 8081, "hostPort": 0}}
			c["securityContext"] = map[string]any{
				"privileged": false, "allowPrivilegeEscalation": false, "procMount": "Default",
				"capabilities":   map[string]any{"drop": []any{"ALL"}, "add": []any{}},
				"seccompProfile": map[string]any{"type": "RuntimeDefault"}, "windowsOptions": map[string]any{"hostProcess": false},
			}
		})},
	}, {
		name: "patches its scheduled Pod",
		r:    request{user: gotest, operation: "UPDATE", namespace: "repos", nsLabels: ready, object: scheduled, oldObject: scheduled},
	}, {
		name: "deletes its Pod",
		r:    request{user: gotest, operation: "DELETE", namespace: "repos", nsLabels: ready, oldObject: own},
	}, {
		name: "deletes its Pod after the namespace drops both labels",
		r:    request{user: gotest, operation: "DELETE", namespace: "repos", oldObject: own},
	}, {
		name: "another check creates its own Pod",
		r:    request{user: review, operation: "CREATE", namespace: "repos", nsLabels: ready, object: named("review-0123456789abcdef", pod("check-review", ""))},
	}, {
		name: "creates a Pod in its own namespace",
		r:    request{user: gotest, operation: "CREATE", namespace: "check-gotest", nsLabels: ready, object: own},
		want: programs,
	}, {
		name: "creates a Pod in another check's namespace",
		r:    request{user: gotest, operation: "CREATE", namespace: "check-gofmt", nsLabels: ready, object: pod("check-gotest", "check-gofmt")},
		want: programs,
	}, {
		name: "creates a Pod in the core program's namespace",
		r:    request{user: gotest, operation: "CREATE", namespace: "git-k8s", nsLabels: ready, object: pod("check-gotest", "git-k8s")},
		want: programs,
	}, {
		name: "deletes the core program's Pod",
		r:    request{user: gotest, operation: "DELETE", namespace: "git-k8s", oldObject: pod("", "git-k8s")},
		want: programs,
	}, {
		name: "creates a Pod without its label",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: pod("", "")},
		want: label,
	}, {
		name: "creates a Pod with only check-gotest's app label",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: appLabel},
		want: label,
	}, {
		name: "creates a Pod with another check's label",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: pod("check-gofmt", "")},
		want: label,
	}, {
		name: "another check creates a Pod with its own label under the gotest check's Pod name",
		r:    request{user: review, operation: "CREATE", namespace: "repos", nsLabels: ready, object: pod("check-review", "")},
		want: "the review check's new Pods need a name of the form review-ID, where ID has no hyphens",
	}, {
		name: "creates a Pod under another check's Pod name",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: named("review-0123456789abcdef", pod("check-gotest", ""))},
		want: podName,
	}, {
		name: "creates a Pod under the Pod name of a check whose name starts with its own",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: named("gotest-race-0123456789abcdef", pod("check-gotest", ""))},
		want: podName,
	}, {
		name: "creates a Pod whose name runs its check's name into the ID",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: named("gotest0123456789abcdef", pod("check-gotest", ""))},
		want: podName,
	}, {
		name: "patches its Pod whose name isn't gotest-ID",
		r:    request{user: gotest, operation: "UPDATE", namespace: "repos", nsLabels: ready, object: named("test-pod", pod("check-gotest", "")), oldObject: named("test-pod", pod("check-gotest", ""))},
	}, {
		name: "deletes its Pod whose name isn't gotest-ID",
		r:    request{user: gotest, operation: "DELETE", namespace: "repos", nsLabels: ready, oldObject: named("test-pod", pod("check-gotest", ""))},
	}, {
		name: "creates a Pod in a namespace without the opt-in label",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: labels("git-k8s.imjasonh.com/check-pods", ""), object: own},
		want: optedOut,
	}, {
		name: "creates a Pod in a namespace that opts out",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: labels("git-k8s.imjasonh.com/check-pods", "false"), object: own},
		want: optedOut,
	}, {
		name: "creates a Pod in a namespace without labels",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", object: own},
		want: optedOut,
	}, {
		name: "patches its Pod after the namespace drops the opt-in label",
		r:    request{user: gotest, operation: "UPDATE", namespace: "repos", nsLabels: labels("git-k8s.imjasonh.com/check-pods", ""), object: own, oldObject: own},
		want: optedOut,
	}, {
		name: "creates a Pod in a namespace without Pod Security labels",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: labels("pod-security.kubernetes.io/enforce", ""), object: own},
		want: unenforced,
	}, {
		name: "creates a Pod in a namespace that enforces baseline",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: labels("pod-security.kubernetes.io/enforce", "baseline"), object: own},
		want: unenforced,
	}, {
		name: "creates a Pod in a namespace that enforces privileged",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: labels("pod-security.kubernetes.io/enforce", "privileged"), object: own},
		want: unenforced,
	}, {
		name: "creates a Pod in a namespace that only warns",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: labels("pod-security.kubernetes.io/enforce", "", "pod-security.kubernetes.io/warn", "restricted"), object: own},
		want: unenforced,
	}, {
		name: "creates a Pod in a namespace that pins an old version of restricted",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: labels("pod-security.kubernetes.io/enforce-version", "v1.18"), object: own},
		want: unenforced,
	}, {
		name: "patches its Pod after the namespace stops enforcing Pod Security",
		r:    request{user: gotest, operation: "UPDATE", namespace: "repos", nsLabels: labels("pod-security.kubernetes.io/enforce", ""), object: own, oldObject: own},
		want: unenforced,
	}, {
		name: "creates a Pod that runs as another service account",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: pod("check-gotest", "rogue")},
		want: account,
	}, {
		name: "creates a Pod that names another service account in the deprecated field",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: deprecated},
		want: account,
	}, {
		name: "creates a Pod on a node that it names",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: scheduled},
		want: node,
	}, {
		name: "creates a Pod that shares the node's network",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: gotestPod(func(spec map[string]any) { spec["hostNetwork"] = true })},
		want: host,
	}, {
		name: "creates a Pod that shares the node's PID namespace",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: gotestPod(func(spec map[string]any) { spec["hostPID"] = true })},
		want: host,
	}, {
		name: "creates a Pod that shares the node's IPC namespace",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: gotestPod(func(spec map[string]any) { spec["hostIPC"] = true })},
		want: host,
	}, {
		name: "creates a Pod that mounts a hostPath volume",
		r: request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: gotestPod(func(spec map[string]any) {
			spec["volumes"] = []any{map[string]any{"name": "src", "emptyDir": map[string]any{}}, map[string]any{"name": "root", "hostPath": map[string]any{"path": "/"}}}
		})},
		want: host,
	}, {
		name: "creates a Pod with a host port",
		r: request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: gotestPod(func(spec map[string]any) {
			spec["containers"].([]any)[0].(map[string]any)["ports"] = []any{map[string]any{"containerPort": 8080, "hostPort": 8080}}
		})},
		want: host,
	}, {
		name: "creates a Pod with a host port on its container's second port",
		r: request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: gotestPod(func(spec map[string]any) {
			spec["containers"].([]any)[0].(map[string]any)["ports"] = []any{map[string]any{"containerPort": 8080}, map[string]any{"containerPort": 8081, "hostPort": 8081}}
		})},
		want: host,
	}, {
		name: "deletes the Pod of a check whose name starts with its own",
		r:    request{user: gotest, operation: "DELETE", namespace: "repos", nsLabels: ready, oldObject: pod("check-gotest-race", "")},
		want: others,
	}, {
		name: "creates a Pod with the label of a check whose name starts with its own",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: pod("check-gotest-race", "")},
		want: label,
	}, {
		name: "an account whose name contains check- after a prefix creates a Pod",
		r:    request{user: "system:serviceaccount:ci:precheck-runner", operation: "CREATE", namespace: "ci", object: pod("", "")},
	}, {
		name: "creates a Pod with a host port on an init container",
		r: request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: gotestPod(func(spec map[string]any) {
			spec["initContainers"] = []any{map[string]any{"name": "fetch", "image": "cgr.dev/chainguard/git", "ports": []any{map[string]any{"containerPort": 22, "hostPort": 2222}}}}
		})},
		want: host,
	}, {
		name: "creates a privileged Pod that a Pod Security exemption for its RuntimeClass would admit",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: escape},
		want: host,
	}, {
		name: "creates a Pod with a privileged container",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: withContext(map[string]any{"privileged": true})},
		want: privilege,
	}, {
		name: "creates a Pod with a privileged init container",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: initContainer(map[string]any{"privileged": true})},
		want: privilege,
	}, {
		name: "creates a Pod whose container isn't privileged and whose init container is",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: withContexts(map[string]any{"privileged": false}, map[string]any{"privileged": true})},
		want: privilege,
	}, {
		name: "creates a Pod whose second container is privileged",
		r: request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: gotestPod(func(spec map[string]any) {
			spec["containers"] = append(spec["containers"].([]any), map[string]any{"name": "sidecar", "image": "cgr.dev/chainguard/go", "securityContext": map[string]any{"privileged": true}})
		})},
		want: privilege,
	}, {
		name: "adds a privileged ephemeral container to its Pod",
		r:    request{user: gotest, operation: "UPDATE", subresource: "ephemeralcontainers", namespace: "repos", nsLabels: ready, object: ephemeral, oldObject: own},
		want: privilege,
	}, {
		name: "creates a Pod that adds a capability",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: withContext(map[string]any{"capabilities": map[string]any{"add": []any{"SYS_ADMIN"}}})},
		want: privilege,
	}, {
		name: "creates a Pod whose init container adds the capability that restricted allows",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: initContainer(map[string]any{"capabilities": map[string]any{"add": []any{"NET_BIND_SERVICE"}}})},
		want: privilege,
	}, {
		name: "creates a Pod with an unmasked /proc",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: withContext(map[string]any{"procMount": "Unmasked"})},
		want: privilege,
	}, {
		name: "creates a Pod with an unconfined container",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: withContext(map[string]any{"seccompProfile": map[string]any{"type": "Unconfined"}})},
		want: privilege,
	}, {
		name: "creates an unconfined Pod",
		r: request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: gotestPod(func(spec map[string]any) {
			spec["securityContext"] = map[string]any{"seccompProfile": map[string]any{"type": "Unconfined"}}
		})},
		want: privilege,
	}, {
		name: "creates a Pod with a host process container",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: withContext(map[string]any{"windowsOptions": map[string]any{"hostProcess": true}})},
		want: privilege,
	}, {
		name: "creates a host process Pod",
		r: request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: gotestPod(func(spec map[string]any) {
			spec["securityContext"] = map[string]any{"windowsOptions": map[string]any{"hostProcess": true}}
		})},
		want: privilege,
	}, {
		name: "creates its Pod with the container_t SELinux type, an MCS level, and the RuntimeDefault AppArmor profile",
		r: request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: gotestPod(func(spec map[string]any) {
			spec["securityContext"] = map[string]any{"seLinuxOptions": map[string]any{"type": "container_t", "level": "s0:c123,c456"}, "appArmorProfile": map[string]any{"type": "RuntimeDefault"}}
			spec["containers"].([]any)[0].(map[string]any)["securityContext"] = map[string]any{"seLinuxOptions": map[string]any{"level": "s0:c1,c2"}, "appArmorProfile": map[string]any{"type": "Localhost", "localhostProfile": "k8s-default"}}
		})},
	}, {
		name: "creates its Pod with the other SELinux types that baseline allows",
		r: request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: gotestPod(func(spec map[string]any) {
			spec["securityContext"] = map[string]any{"seLinuxOptions": map[string]any{"type": "container_init_t"}}
			spec["containers"].([]any)[0].(map[string]any)["securityContext"] = map[string]any{"seLinuxOptions": map[string]any{"type": "container_kvm_t"}}
			spec["initContainers"] = []any{map[string]any{"name": "fetch", "image": "cgr.dev/chainguard/git", "securityContext": map[string]any{"seLinuxOptions": map[string]any{"type": "container_engine_t"}}}}
		})},
	}, {
		name: "creates a Pod whose container runs as the spc_t SELinux type",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: withContext(map[string]any{"seLinuxOptions": map[string]any{"type": "spc_t"}})},
		want: confinement,
	}, {
		name: "creates a Pod that runs as the spc_t SELinux type",
		r: request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: gotestPod(func(spec map[string]any) {
			spec["securityContext"] = map[string]any{"seLinuxOptions": map[string]any{"type": "spc_t"}}
		})},
		want: confinement,
	}, {
		name: "creates a Pod whose init container sets an SELinux role",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: initContainer(map[string]any{"seLinuxOptions": map[string]any{"role": "system_r"}})},
		want: confinement,
	}, {
		name: "creates a Pod whose container runs as container_t and whose init container runs as spc_t",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: withContexts(map[string]any{"seLinuxOptions": map[string]any{"type": "container_t"}}, map[string]any{"seLinuxOptions": map[string]any{"type": "spc_t"}})},
		want: confinement,
	}, {
		name: "creates a Pod whose container sets an SELinux user",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: withContext(map[string]any{"seLinuxOptions": map[string]any{"user": "system_u"}})},
		want: confinement,
	}, {
		name: "creates a Pod that sets an SELinux user",
		r: request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: gotestPod(func(spec map[string]any) {
			spec["securityContext"] = map[string]any{"seLinuxOptions": map[string]any{"user": "system_u"}}
		})},
		want: confinement,
	}, {
		name: "creates a Pod that sets an SELinux role",
		r: request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: gotestPod(func(spec map[string]any) {
			spec["securityContext"] = map[string]any{"seLinuxOptions": map[string]any{"role": "system_r"}}
		})},
		want: confinement,
	}, {
		name: "creates a Pod with an AppArmor-unconfined container",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: withContext(map[string]any{"appArmorProfile": map[string]any{"type": "Unconfined"}})},
		want: confinement,
	}, {
		name: "creates an AppArmor-unconfined Pod",
		r: request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: gotestPod(func(spec map[string]any) {
			spec["securityContext"] = map[string]any{"appArmorProfile": map[string]any{"type": "Unconfined"}}
		})},
		want: confinement,
	}, {
		name: "creates a Pod that sets a sysctl",
		r: request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: gotestPod(func(spec map[string]any) {
			spec["securityContext"] = map[string]any{"sysctls": []any{map[string]any{"name": "kernel.msgmax", "value": "65536"}}}
		})},
		want: confinement,
	}, {
		name: "adds an ephemeral container that runs as the spc_t SELinux type to its Pod",
		r: request{user: gotest, operation: "UPDATE", subresource: "ephemeralcontainers", namespace: "repos", nsLabels: ready, object: gotestPod(func(spec map[string]any) {
			spec["ephemeralContainers"] = []any{map[string]any{"name": "debug", "image": "busybox", "securityContext": map[string]any{"seLinuxOptions": map[string]any{"type": "spc_t"}}}}
		}), oldObject: own},
		want: confinement,
	}, {
		name: "creates its Pod with probes and lifecycle handlers that don't set a host",
		r: request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: withFields(map[string]any{
			"livenessProbe":  map[string]any{"httpGet": map[string]any{"path": "/healthz", "port": 8080}},
			"readinessProbe": map[string]any{"tcpSocket": map[string]any{"host": "", "port": 8080}},
			"lifecycle":      map[string]any{"preStop": map[string]any{"exec": map[string]any{"command": []any{"true"}}}},
		})},
	}, {
		name: "creates a Pod whose liveness probe sets a host",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: withFields(map[string]any{"livenessProbe": metadataGet})},
		want: probeHost,
	}, {
		name: "creates a Pod whose readiness probe connects to another host's TCP port",
		r: request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: withFields(map[string]any{
			"readinessProbe": map[string]any{"tcpSocket": map[string]any{"host": "10.0.0.1", "port": 10250}},
		})},
		want: probeHost,
	}, {
		name: "creates a Pod whose startup probe sets a host",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: withFields(map[string]any{"startupProbe": metadataGet})},
		want: probeHost,
	}, {
		name: "creates a Pod whose postStart handler sets a host",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: withFields(map[string]any{"lifecycle": map[string]any{"postStart": metadataGet}})},
		want: probeHost,
	}, {
		name: "creates a Pod whose preStop handler sets a host",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: withFields(map[string]any{"lifecycle": map[string]any{"preStop": metadataGet}})},
		want: probeHost,
	}, {
		name: "creates a Pod whose sidecar's liveness probe sets a host",
		r: request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: gotestPod(func(spec map[string]any) {
			spec["initContainers"] = []any{map[string]any{"name": "proxy", "image": "cgr.dev/chainguard/go", "restartPolicy": "Always", "livenessProbe": metadataGet}}
		})},
		want: probeHost,
	}, {
		name: "creates a Pod whose container's liveness probe doesn't set a host and whose sidecar's does",
		r: request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: ready, object: gotestPod(func(spec map[string]any) {
			spec["containers"].([]any)[0].(map[string]any)["livenessProbe"] = map[string]any{"httpGet": map[string]any{"path": "/healthz", "port": 8080}}
			spec["initContainers"] = []any{map[string]any{"name": "proxy", "image": "cgr.dev/chainguard/go", "restartPolicy": "Always", "livenessProbe": metadataGet}}
		})},
		want: probeHost,
	}, {
		name: "patches another check's Pod",
		r:    request{user: gotest, operation: "UPDATE", namespace: "repos", nsLabels: ready, object: pod("check-review", ""), oldObject: pod("check-review", "")},
		want: others,
	}, {
		name: "patches a Pod that no check owns",
		r:    request{user: gotest, operation: "UPDATE", namespace: "repos", nsLabels: ready, object: pod("", ""), oldObject: pod("", "")},
		want: others,
	}, {
		name: "labels a Pod that it doesn't own as its own",
		r:    request{user: gotest, operation: "UPDATE", namespace: "repos", nsLabels: ready, object: own, oldObject: pod("", "")},
		want: others,
	}, {
		name: "gives its Pod another check's label",
		r:    request{user: gotest, operation: "UPDATE", namespace: "repos", nsLabels: ready, object: pod("check-review", ""), oldObject: own},
		want: label,
	}, {
		name: "removes its label from its Pod",
		r:    request{user: gotest, operation: "UPDATE", namespace: "repos", nsLabels: ready, object: pod("", ""), oldObject: own},
		want: label,
	}, {
		name: "deletes another check's Pod",
		r:    request{user: gotest, operation: "DELETE", namespace: "repos", nsLabels: ready, oldObject: pod("check-review", "")},
		want: others,
	}, {
		name: "deletes a Pod that no check owns",
		r:    request{user: gotest, operation: "DELETE", namespace: "repos", nsLabels: ready, oldObject: pod("", "")},
		want: others,
	}, {
		name: "adds an ephemeral container to another check's Pod",
		r:    request{user: gotest, operation: "UPDATE", subresource: "ephemeralcontainers", namespace: "repos", nsLabels: ready, object: pod("check-review", ""), oldObject: pod("check-review", "")},
		want: others,
	}, {
		name: "writes the status of another check's Pod",
		r:    request{user: gotest, operation: "UPDATE", subresource: "status", namespace: "repos", nsLabels: ready, object: pod("check-review", ""), oldObject: pod("check-review", "")},
		want: others,
	}, {
		name: "resizes another check's Pod",
		r:    request{user: gotest, operation: "UPDATE", subresource: "resize", namespace: "repos", nsLabels: ready, object: pod("check-review", ""), oldObject: pod("check-review", "")},
		want: others,
	}, {
		name: "an account named after the check in another check's namespace",
		r:    request{user: "system:serviceaccount:check-gofmt:check-gotest", operation: "CREATE", namespace: "repos", nsLabels: ready, object: own},
		want: notCheck("system:serviceaccount:check-gofmt:check-gotest"),
	}, {
		name: "an account named after the check in a namespace that isn't a check's",
		r:    request{user: "system:serviceaccount:ci:check-gotest", operation: "CREATE", namespace: "default", object: escape},
		want: notCheck("system:serviceaccount:ci:check-gotest"),
	}, {
		name: "an account named after the check in a shared check-* namespace",
		r:    request{user: "system:serviceaccount:check-shared:check-gotest", operation: "CREATE", namespace: "git-k8s", object: pod("", "git-k8s")},
		want: notCheck("system:serviceaccount:check-shared:check-gotest"),
	}, {
		name: "another account in a check's namespace",
		r:    request{user: "system:serviceaccount:check-gotest:default", operation: "CREATE", namespace: "check-gofmt", object: pod("", "check-gofmt")},
		want: notCheck("system:serviceaccount:check-gotest:default"),
	}, {
		name: "another account in a check's namespace deletes the check's Pod",
		r:    request{user: "system:serviceaccount:check-gotest:rogue", operation: "DELETE", namespace: "repos", nsLabels: ready, oldObject: own},
		want: notCheck("system:serviceaccount:check-gotest:rogue"),
	}, {
		name: "a username that only looks like a check's service account",
		r:    request{user: "system:serviceaccount:check-gotest", operation: "CREATE", namespace: "repos", nsLabels: ready, object: own},
		want: notCheck("system:serviceaccount:check-gotest"),
	}, {
		name: "the core program creates a Pod in its namespace",
		r:    request{user: "system:serviceaccount:git-k8s:git-k8s", operation: "CREATE", namespace: "git-k8s", object: pod("", "git-k8s")},
	}, {
		name: "an unrelated service account creates a privileged Pod",
		r:    request{user: "system:serviceaccount:payments:deployer", operation: "CREATE", namespace: "payments", object: escape},
	}, {
		name: "the ReplicaSet controller creates a Pod",
		r:    request{user: "system:serviceaccount:kube-system:replicaset-controller", operation: "CREATE", namespace: "repos", object: pod("", "")},
	}, {
		name: "a person creates a Pod with check-gotest's label in a check's namespace",
		r:    request{user: "alice@example.com", operation: "CREATE", namespace: "check-gofmt", object: pod("check-gotest", "check-gofmt")},
	}, {
		name: "a person whose name starts with check- creates a Pod",
		r:    request{user: "check-admin", operation: "CREATE", namespace: "check-gofmt", object: pod("check-gotest", "check-gofmt")},
	}, {
		name: "the garbage collector deletes a check's Pod",
		r:    request{user: "system:serviceaccount:kube-system:generic-garbage-collector", operation: "DELETE", namespace: "repos", oldObject: own},
	}} {
		t.Run(tt.name, func(t *testing.T) {
			if got := p.admit(t, tt.r); got != tt.want {
				t.Errorf("got %q, want %q", got, tt.want)
			}
		})
	}
}

// The policy matches every Pod write in the cluster, and the API server looks
// up a binding's params before it evaluates matchConditions. A binding that
// denies while its params are missing would then deny every Pod write.
func TestCheckPodsBinding(t *testing.T) {
	p := find(t, "ValidatingAdmissionPolicy", "git-k8s-check-pods")
	if p.Spec.FailurePolicy != "Fail" {
		t.Errorf("failurePolicy = %q, want Fail", p.Spec.FailurePolicy)
	}
	b := find(t, "ValidatingAdmissionPolicyBinding", "git-k8s-check-pods")
	if b.Spec.PolicyName != "git-k8s-check-pods" || !slices.Contains(b.Spec.ValidationActions, "Deny") {
		t.Errorf("binding = %+v, want one that denies for git-k8s-check-pods", b.Spec)
	}
	if r := b.Spec.ParamRef; r != nil && r.ParameterNotFoundAction != "Allow" {
		t.Errorf("paramRef.parameterNotFoundAction = %q, want Allow", r.ParameterNotFoundAction)
	}
}
