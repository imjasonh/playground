package config

import (
	"cmp"
	"errors"
	"io"
	"maps"
	"os"
	"reflect"
	"slices"
	"strings"
	"testing"

	"cel.dev/cel-go/cel"
	"cel.dev/cel-go/common/types"
	"cel.dev/cel-go/common/types/ref"
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
	// messages has each validation's messageExpression, or nil for a
	// validation that has only a message.
	messages []cel.Program
}

// authorizer is the part of the API server's CEL authorizer library that
// git-k8s-approvals uses. Each call appends its argument to path, and
// allowed reports whether path is allow, the one check that the user's
// RBAC allows.
type authorizer struct{ allow, path string }

var authorizerType = cel.OpaqueType("kubernetes.authorization.Authorizer")

func (a authorizer) ConvertToNative(reflect.Type) (any, error) {
	return nil, errors.New("an authorizer has no native value")
}

func (a authorizer) ConvertToType(t ref.Type) ref.Val {
	if t == types.TypeType {
		return authorizerType
	}
	return types.NewErr("can't convert an authorizer to %s", t.TypeName())
}

func (a authorizer) Equal(other ref.Val) ref.Val { return types.Bool(a == other) }
func (a authorizer) Type() ref.Type              { return authorizerType }
func (a authorizer) Value() any                  { return a }

// authorizerLib declares authorizer, and the calls that build and make a
// check, in a CEL environment.
func authorizerLib() []cel.EnvOption {
	opts := []cel.EnvOption{
		cel.Variable("authorizer", authorizerType),
		cel.Function("allowed", cel.MemberOverload("authorizer_allowed", []*cel.Type{authorizerType}, cel.BoolType,
			cel.UnaryBinding(func(a ref.Val) ref.Val { return types.Bool(a.(authorizer).path == a.(authorizer).allow) }))),
	}
	for _, call := range []string{"group", "resource", "namespace", "name", "check"} {
		opts = append(opts, cel.Function(call, cel.MemberOverload("authorizer_"+call, []*cel.Type{authorizerType, cel.StringType}, authorizerType,
			cel.BinaryBinding(func(a, arg ref.Val) ref.Val {
				return authorizer{allow: a.(authorizer).allow, path: a.(authorizer).path + "/" + string(arg.(types.String))}
			}))))
	}
	return opts
}

func compile(t *testing.T, m manifest) *policy {
	t.Helper()
	env, err := cel.NewEnv(append(authorizerLib(),
		cel.Variable("object", cel.DynType),
		cel.Variable("oldObject", cel.DynType),
		cel.Variable("request", cel.DynType),
		cel.Variable("namespaceObject", cel.DynType),
		cel.Variable("params", cel.DynType),
		cel.Variable("variables", cel.MapType(cel.StringType, cel.DynType)),
		cel.HomogeneousAggregateLiterals(),
		ext.Strings(ext.StringsVersion(2)),
	)...)
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
		var msg cel.Program
		switch {
		case v.MessageExpression != "":
			msg = prg(v.MessageExpression)
		case v.Message == "":
			t.Fatalf("validation %q has no message", v.Expression)
		}
		p.validations = append(p.validations, prg(v.Expression))
		p.messages = append(p.messages, msg)
	}
	return p
}

// request is an admission request for a Pod, or for the resource that
// resource names, or for one of its subresources. params is the ConfigMap
// that the binding names, or nil if there's none. canApprove reports
// whether user has the approve verb on the GitBranch named name.
type request struct {
	user        string
	operation   string
	resource    string
	subresource string
	namespace   string
	name        string
	canApprove  bool
	nsLabels    map[string]string
	params      map[string]any
	object      map[string]any
	oldObject   map[string]any
}

// admit evaluates the policy for r as the API server does: it skips requests
// that matchConstraints or matchConditions leave out, evaluates the
// variables in order, and returns the message of the first validation that
// fails, or "" if they all pass.
func (p *policy) admit(t *testing.T, r request) string {
	t.Helper()
	resource := cmp.Or(r.resource, "pods")
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
	var authz authorizer
	if r.canApprove {
		authz.allow = "/git-k8s.imjasonh.com/gitbranches/" + r.namespace + "/" + r.name + "/approve"
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
				"name":        r.name,
				"subResource": r.subresource,
				"userInfo":    map[string]any{"username": r.user},
			},
			"namespaceObject": map[string]any{"metadata": ns},
			"variables":       maps.Clone(vars),
			"authorizer":      authz,
		}
		// A nil map would become an empty CEL map, not null.
		if r.object != nil {
			a["object"] = r.object
		}
		if r.oldObject != nil {
			a["oldObject"] = r.oldObject
		}
		if r.params != nil {
			a["params"] = r.params
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
		switch {
		case eval(v).(bool):
		case p.messages[i] == nil:
			return p.m.Spec.Validations[i].Message
		default:
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

// checksConfigMap returns the git-k8s-checks ConfigMap with the entries kv, a
// list of keys and values.
func checksConfigMap(kv ...string) map[string]any {
	cm := map[string]any{"metadata": map[string]any{"name": "git-k8s-checks", "namespace": "git-k8s"}}
	if len(kv) > 0 {
		data := map[string]any{}
		for i := 0; i < len(kv); i += 2 {
			data[kv[i]] = kv[i+1]
		}
		cm["data"] = data
	}
	return cm
}

// gitBranch returns a GitBranch for the branch main, after edit changes its
// metadata and spec.
func gitBranch(edit func(meta, spec map[string]any)) map[string]any {
	meta := map[string]any{"name": "app-main"}
	spec := map[string]any{"branch": "main", "head": "0000000"}
	if edit != nil {
		edit(meta, spec)
	}
	return map[string]any{"metadata": meta, "spec": spec}
}

func TestCheckResults(t *testing.T) {
	p := compile(t, find(t, "ValidatingAdmissionPolicy", "git-k8s-check-results"))
	const (
		gotest   = "system:serviceaccount:check-gotest:check-gotest"
		bot      = "system:serviceaccount:checks:bot"
		core     = "system:serviceaccount:git-k8s:git-k8s"
		deployer = "system:serviceaccount:checks:deployer"
	)
	old := gitBranch(nil)
	withStatus := func(status map[string]any) map[string]any {
		b := gitBranch(nil)
		b["status"] = status
		return b
	}
	wrote := func(check string) map[string]any {
		return withStatus(map[string]any{"checks": map[string]any{check: map[string]any{"commit": "0000000", "state": "Passed"}}})
	}
	queued := withStatus(map[string]any{"queue": []any{"c/x"}})
	merged := withStatus(map[string]any{"state": "Merged"})
	diverged := withStatus(map[string]any{"diverged": map[string]any{"commit": "0000000", "ref": "refs/git-k8s/downstream/heads/main"}})
	update := func(user string, params, object map[string]any) request {
		return request{user: user, operation: "UPDATE", resource: "gitbranches", subresource: "status", namespace: "repos", params: params, object: object, oldObject: old}
	}
	sends := func(check string) string {
		return "the " + check + " check can't write GitBranch status; it sends its results to the core program"
	}
	emptied := func(user string) string {
		return user + ", a check whose entry in the git-k8s-checks ConfigMap is empty, can't write a GitBranch's status"
	}
	none := checksConfigMap()
	for _, tt := range []struct {
		name string
		r    request
		want string
	}{{
		name: "a check writes its result",
		r:    update(gotest, none, wrote("gotest")),
		want: sends("gotest"),
	}, {
		name: "a check writes another check's result",
		r:    update(gotest, none, wrote("race")),
		want: sends("gotest"),
	}, {
		name: "a check writes a merge queue",
		r:    update(gotest, none, queued),
		want: sends("gotest"),
	}, {
		name: "a check writes status.diverged",
		r:    update(gotest, none, diverged),
		want: sends("gotest"),
	}, {
		name: "a check writes a status without changes",
		r:    update(gotest, none, old),
		want: sends("gotest"),
	}, {
		name: "a check whose entry names another check writes that check's result",
		r:    update(gotest, checksConfigMap("check-gotest.check-gotest", "race"), wrote("race")),
		want: sends("race"),
	}, {
		name: "a check that only its entry names writes its result",
		r:    update(bot, checksConfigMap("checks.bot", "bot"), wrote("bot")),
		want: sends("bot"),
	}, {
		name: "a check that only its entry names writes a merge queue",
		r:    update(bot, checksConfigMap("checks.bot", "bot"), queued),
		want: sends("bot"),
	}, {
		name: "a check whose entry is empty writes its result",
		r:    update(gotest, checksConfigMap("check-gotest.check-gotest", ""), wrote("gotest")),
		want: emptied(gotest),
	}, {
		name: "a check whose entry is empty writes a merge queue",
		r:    update(bot, checksConfigMap("checks.bot", ""), queued),
		want: emptied(bot),
	}, {
		name: "a check whose entry is empty writes a branch's state",
		r:    update(gotest, checksConfigMap("check-gotest.check-gotest", ""), merged),
		want: emptied(gotest),
	}, {
		name: "the core program writes a result",
		r:    update(core, none, wrote("gofmt")),
	}, {
		name: "the core program writes status.diverged",
		r:    update(core, none, diverged),
	}, {
		name: "the core program writes a merge queue",
		r:    update(core, none, queued),
	}, {
		name: "the core program writes a merge queue despite an empty entry",
		r:    update(core, checksConfigMap("git-k8s.git-k8s", ""), queued),
	}, {
		name: "the core program writes a result despite an entry that names a check",
		r:    update(core, checksConfigMap("git-k8s.git-k8s", "gofmt"), wrote("gofmt")),
	}, {
		name: "another service account in a check's namespace writes a merge queue",
		r:    update(deployer, checksConfigMap("checks.bot", ""), queued),
	}, {
		name: "another service account in a check's namespace writes a result",
		r:    update(deployer, checksConfigMap("checks.bot", ""), wrote("bot")),
		want: deployer + " isn't the core program's service account, so it can't write status.checks",
	}, {
		name: "another service account writes status.diverged",
		r:    update(deployer, none, diverged),
		want: deployer + " isn't the core program's service account, so it can't write status.diverged",
	}, {
		name: "a person writes a result",
		r:    update("alice@example.com", none, wrote("gofmt")),
	}} {
		t.Run(tt.name, func(t *testing.T) {
			if got := p.admit(t, tt.r); got != tt.want {
				t.Errorf("got %q, want %q", got, tt.want)
			}
		})
	}
}

func TestBranches(t *testing.T) {
	p := compile(t, find(t, "ValidatingAdmissionPolicy", "git-k8s-branches"))
	const (
		gotest         = "system:serviceaccount:check-gotest:check-gotest"
		bot            = "system:serviceaccount:checks:bot"
		core           = "system:serviceaccount:git-k8s:git-k8s"
		deps           = "system:serviceaccount:git-k8s-deps:git-k8s-deps"
		otherDeps      = "system:serviceaccount:deps:git-k8s-deps"
		approve        = "git-k8s controllers can't approve branches"
		depsCantChange = "git-k8s-deps can't change GitBranch objects"
	)
	old := gitBranch(nil)
	labeled := gitBranch(func(meta, _ map[string]any) { meta["labels"] = map[string]any{"e2e": "changed"} })
	moved := gitBranch(func(_, spec map[string]any) { spec["head"] = "1111111" })
	// A finalizer that nobody removes keeps a deleted branch's GitBranch,
	// and its place in the merge queue, forever. An owner reference to an
	// object that doesn't exist makes garbage collection delete the
	// GitBranch, with its approval and its place in the queue.
	finalized := gitBranch(func(meta, _ map[string]any) { meta["finalizers"] = []any{"example.com/hold"} })
	reowned := gitBranch(func(meta, _ map[string]any) {
		meta["ownerReferences"] = []any{map[string]any{"apiVersion": "v1", "kind": "ConfigMap", "name": "gone", "uid": "6d9e4f0c-0000-4000-8000-000000000000"}}
	})
	// The core program's server-side applies remove only the fields that
	// its entries in managedFields list, such as status.queued.
	managed := gitBranch(func(meta, _ map[string]any) {
		meta["managedFields"] = []any{map[string]any{
			"manager": "repositories", "operation": "Apply", "apiVersion": "git-k8s.imjasonh.com/v1alpha1",
			"fieldsType": "FieldsV1", "fieldsV1": map[string]any{"f:spec": map[string]any{"f:head": map[string]any{}}},
		}, map[string]any{
			"manager": "merge", "operation": "Apply", "apiVersion": "git-k8s.imjasonh.com/v1alpha1", "subresource": "status",
			"fieldsType": "FieldsV1", "fieldsV1": map[string]any{"f:status": map[string]any{"f:queued": map[string]any{}}},
		}}
	})
	approvedBy := func(user string) map[string]any {
		return gitBranch(func(meta, _ map[string]any) {
			meta["annotations"] = map[string]any{"git-k8s.imjasonh.com/approve": "0000000", "git-k8s.imjasonh.com/approved-by": user}
		})
	}
	ungated := gitBranch(func(_, spec map[string]any) { spec["merge"] = map[string]any{"when": "true"} })
	cantCreate := func(user string) string {
		return user + " can't create GitBranch objects; only the core program creates them"
	}
	cantChangeSpec := func(user string) string {
		return user + " can't change a GitBranch's spec; the core program copies it from the GitRepository"
	}
	update := func(user string, params, object map[string]any) request {
		return request{user: user, operation: "UPDATE", resource: "gitbranches", namespace: "repos", params: params, object: object, oldObject: old}
	}
	updateManaged := func(user string, params, object map[string]any) request {
		return request{user: user, operation: "UPDATE", resource: "gitbranches", namespace: "repos", params: params, object: object, oldObject: managed}
	}
	cantChange := func(check string) string { return "the " + check + " check can't change GitBranch objects" }
	emptied := func(user string) string {
		return user + ", a check whose entry in the git-k8s-checks ConfigMap is empty, can't change GitBranch objects"
	}
	none := checksConfigMap()
	for _, tt := range []struct {
		name string
		r    request
		want string
	}{{
		name: "a check adds a label",
		r:    update(gotest, none, labeled),
		want: cantChange("gotest"),
	}, {
		name: "a check changes a branch's spec",
		r:    update(gotest, none, moved),
		want: cantChange("gotest"),
	}, {
		name: "a check adds a finalizer",
		r:    update(gotest, none, finalized),
		want: cantChange("gotest"),
	}, {
		name: "a check changes a branch's owner references",
		r:    update(gotest, none, reowned),
		want: cantChange("gotest"),
	}, {
		name: "a check updates a GitBranch without changing it",
		r:    updateManaged(gotest, none, managed),
	}, {
		name: "a check resets a branch's managedFields",
		r:    updateManaged(gotest, none, old),
		want: cantChange("gotest"),
	}, {
		name: "a check creates a GitBranch",
		r:    request{user: gotest, operation: "CREATE", resource: "gitbranches", namespace: "repos", params: none, object: old},
		want: cantChange("gotest"),
	}, {
		name: "a check approves a branch",
		r:    update(gotest, none, approvedBy(gotest)),
		want: approve,
	}, {
		name: "a check writes its result",
		r:    request{user: gotest, operation: "UPDATE", resource: "gitbranches", subresource: "status", namespace: "repos", params: none, object: labeled, oldObject: old},
	}, {
		name: "a check whose entry names another check adds a label",
		r:    update(gotest, checksConfigMap("check-gotest.check-gotest", "race"), labeled),
		want: cantChange("race"),
	}, {
		name: "a check that only its entry names adds a label",
		r:    update(bot, checksConfigMap("checks.bot", "bot"), labeled),
		want: cantChange("bot"),
	}, {
		name: "a check whose entry is empty adds a label",
		r:    update(gotest, checksConfigMap("check-gotest.check-gotest", ""), labeled),
		want: emptied(gotest),
	}, {
		name: "a check that only its entry names adds a label after the entry is emptied",
		r:    update(bot, checksConfigMap("checks.bot", ""), labeled),
		want: emptied(bot),
	}, {
		name: "a check whose entry is empty changes a branch's spec",
		r:    update(bot, checksConfigMap("checks.bot", ""), moved),
		want: emptied(bot),
	}, {
		name: "a check whose entry is empty approves a branch",
		r:    update(bot, checksConfigMap("checks.bot", ""), approvedBy(bot)),
		want: approve,
	}, {
		name: "the core program adds a label",
		r:    update(core, none, labeled),
	}, {
		name: "the core program adds a finalizer",
		r:    update(core, none, finalized),
	}, {
		name: "the core program adds a label despite an entry that names a check",
		r:    update(core, checksConfigMap("git-k8s.git-k8s", "gofmt"), labeled),
	}, {
		name: "the core program adds a label despite an empty entry",
		r:    update(core, checksConfigMap("git-k8s.git-k8s", ""), labeled),
	}, {
		name: "the core program approves a branch",
		r:    update(core, none, approvedBy(core)),
		want: approve,
	}, {
		name: "git-k8s-deps updates a GitBranch without changing it",
		r:    update(deps, none, old),
	}, {
		name: "git-k8s-deps adds a label",
		r:    update(deps, none, labeled),
		want: depsCantChange,
	}, {
		name: "git-k8s-deps changes a branch's spec",
		r:    update(deps, none, moved),
		want: depsCantChange,
	}, {
		name: "git-k8s-deps adds a finalizer",
		r:    update(deps, none, finalized),
		want: depsCantChange,
	}, {
		name: "git-k8s-deps changes a branch's owner references",
		r:    update(deps, none, reowned),
		want: depsCantChange,
	}, {
		name: "git-k8s-deps resets a branch's managedFields",
		r:    updateManaged(deps, none, old),
		want: depsCantChange,
	}, {
		name: "git-k8s-deps creates a GitBranch",
		r:    request{user: deps, operation: "CREATE", resource: "gitbranches", namespace: "repos", params: none, object: old},
		want: depsCantChange,
	}, {
		name: "git-k8s-deps approves a branch",
		r:    update(deps, none, approvedBy(deps)),
		want: depsCantChange,
	}, {
		name: "git-k8s-deps in another namespace adds a label",
		r:    update(otherDeps, none, labeled),
	}, {
		name: "git-k8s-deps in another namespace with an empty entry adds a label",
		r:    update(otherDeps, checksConfigMap("deps.git-k8s-deps", ""), labeled),
		want: emptied(otherDeps),
	}, {
		name: "another service account in a check's namespace adds a label",
		r:    update("system:serviceaccount:checks:deployer", checksConfigMap("checks.bot", ""), labeled),
	}, {
		name: "a person adds a label",
		r:    update("alice@example.com", checksConfigMap("checks.bot", ""), labeled),
	}, {
		name: "a person approves a branch",
		r:    update("alice@example.com", none, approvedBy("alice@example.com")),
	}, {
		name: "a person changes a branch's merge policy",
		r:    update("alice@example.com", none, ungated),
		want: cantChangeSpec("alice@example.com"),
	}, {
		name: "a person changes a branch's head",
		r:    update("alice@example.com", none, moved),
		want: cantChangeSpec("alice@example.com"),
	}, {
		name: "a person creates a GitBranch",
		r:    request{user: "alice@example.com", operation: "CREATE", resource: "gitbranches", namespace: "repos", params: none, object: ungated},
		want: cantCreate("alice@example.com"),
	}, {
		name: "a person whose username splits like the core program's changes a branch's merge policy",
		r:    update("a:b:git-k8s:git-k8s", none, ungated),
		want: cantChangeSpec("a:b:git-k8s:git-k8s"),
	}, {
		name: "another service account changes a branch's merge policy",
		r:    update("system:serviceaccount:checks:deployer", none, ungated),
		want: cantChangeSpec("system:serviceaccount:checks:deployer"),
	}, {
		name: "another service account creates a GitBranch",
		r:    request{user: "system:serviceaccount:checks:deployer", operation: "CREATE", resource: "gitbranches", namespace: "repos", params: none, object: old},
		want: cantCreate("system:serviceaccount:checks:deployer"),
	}, {
		name: "the core program changes a branch's spec",
		r:    update(core, none, moved),
	}, {
		name: "the core program creates a GitBranch",
		r:    request{user: core, operation: "CREATE", resource: "gitbranches", namespace: "repos", params: none, object: old},
	}} {
		t.Run(tt.name, func(t *testing.T) {
			if got := p.admit(t, tt.r); got != tt.want {
				t.Errorf("got %q, want %q", got, tt.want)
			}
		})
	}
}

func TestApprovals(t *testing.T) {
	p := compile(t, find(t, "ValidatingAdmissionPolicy", "git-k8s-approvals"))
	const (
		alice   = "alice@example.com"
		bob     = "bob@example.com"
		sha     = "0123456789abcdef0123456789abcdef01234567"
		fullSHA = "set git-k8s.imjasonh.com/approve to a commit's full SHA, in lowercase hexadecimal"
	)
	sha256 := strings.Repeat("0123456789abcdef", 4)
	// approved returns a GitBranch with the approve and approved-by
	// annotations that aren't "", and the label e2e if label isn't "".
	approved := func(approval, approver, label string) map[string]any {
		return gitBranch(func(meta, _ map[string]any) {
			annotations := map[string]any{}
			if approval != "" {
				annotations["git-k8s.imjasonh.com/approve"] = approval
			}
			if approver != "" {
				annotations["git-k8s.imjasonh.com/approved-by"] = approver
			}
			meta["annotations"] = annotations
			if label != "" {
				meta["labels"] = map[string]any{"e2e": label}
			}
		})
	}
	unapproved := approved("", "", "")
	update := func(user string, old, object map[string]any) request {
		return request{user: user, operation: "UPDATE", resource: "gitbranches", namespace: "repos", name: "app-main", canApprove: true, object: object, oldObject: old}
	}
	for _, tt := range []struct {
		name string
		r    request
		want string
	}{{
		name: "a person approves a commit",
		r:    update(alice, unapproved, approved(sha, alice, "")),
	}, {
		name: "a person approves a commit in a SHA-256 repository",
		r:    update(alice, unapproved, approved(sha256, alice, "")),
	}, {
		name: "a person approves a short prefix",
		r:    update(alice, unapproved, approved(sha[:7], alice, "")),
		want: fullSHA,
	}, {
		name: "a person approves a prefix one character short",
		r:    update(alice, unapproved, approved(sha[:39], alice, "")),
		want: fullSHA,
	}, {
		name: "a person approves a SHA in uppercase",
		r:    update(alice, unapproved, approved(strings.ToUpper(sha), alice, "")),
		want: fullSHA,
	}, {
		name: "a person changes an approval to a prefix",
		r:    update(alice, approved(sha, alice, ""), approved(sha[:12], alice, "")),
		want: fullSHA,
	}, {
		name: "a person creates a GitBranch with a prefix approved",
		r:    request{user: alice, operation: "CREATE", resource: "gitbranches", namespace: "repos", name: "app-main", canApprove: true, object: approved(sha[:7], alice, "")},
		want: fullSHA,
	}, {
		name: "a person removes an approval",
		r:    update(alice, approved(sha, alice, ""), unapproved),
	}, {
		name: "a person labels a branch whose approval names a prefix",
		r:    update(alice, approved(sha[:7], alice, ""), approved(sha[:7], alice, "changed")),
	}, {
		name: "a person takes over an approval",
		r:    update(bob, approved(sha, alice, ""), approved(sha, bob, "")),
	}, {
		name: "a person without the approve verb approves a commit",
		r:    request{user: alice, operation: "UPDATE", resource: "gitbranches", namespace: "repos", name: "app-main", object: approved(sha, alice, ""), oldObject: unapproved},
		want: "changing git-k8s.imjasonh.com/approve or git-k8s.imjasonh.com/approved-by requires the approve verb on gitbranches, " +
			"which alice@example.com doesn't have for repos/app-main",
	}} {
		t.Run(tt.name, func(t *testing.T) {
			if got := p.admit(t, tt.r); got != tt.want {
				t.Errorf("got %q, want %q", got, tt.want)
			}
		})
	}
}
