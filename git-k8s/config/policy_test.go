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

func TestCheckPods(t *testing.T) {
	p := compile(t, find(t, "ValidatingAdmissionPolicy", "git-k8s-check-pods"))
	const (
		gotest = "system:serviceaccount:check-gotest:check-gotest"
		review = "system:serviceaccount:check-review:check-review"
	)
	restricted := map[string]string{"pod-security.kubernetes.io/enforce": "restricted"}
	baseline := map[string]string{"pod-security.kubernetes.io/enforce": "baseline"}
	own := pod("check-gotest", "default")
	deprecated := pod("check-gotest", "")
	deprecated["spec"].(map[string]any)["serviceAccount"] = "rogue"
	appLabel := pod("", "")
	appLabel["metadata"].(map[string]any)["labels"] = map[string]any{"app.kubernetes.io/name": "check-gotest"}
	const (
		programs   = "the gotest check can't change Pods in the namespaces of git-k8s programs"
		others     = "the gotest check can change or delete only its own Pods, which have the label kube.imjasonh.github.io/controller=check-gotest"
		label      = "the gotest check's Pods need the label kube.imjasonh.github.io/controller=check-gotest"
		account    = "the gotest check's Pods must run as their namespace's default service account"
		unenforced = "the gotest check can't run Pods in namespace repos, which doesn't enforce the baseline or restricted Pod Security Standard"
	)
	for _, tt := range []struct {
		name string
		r    request
		want string
	}{{
		name: "creates its Pod in a namespace that enforces restricted",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: restricted, object: own},
	}, {
		name: "creates its Pod in a namespace that enforces baseline",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: baseline, object: own},
	}, {
		name: "creates its Pod without naming a service account",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: restricted, object: pod("check-gotest", "")},
	}, {
		name: "patches its Pod",
		r:    request{user: gotest, operation: "UPDATE", namespace: "repos", nsLabels: restricted, object: own, oldObject: own},
	}, {
		name: "deletes its Pod",
		r:    request{user: gotest, operation: "DELETE", namespace: "repos", nsLabels: restricted, oldObject: own},
	}, {
		name: "deletes its Pod after the namespace stops enforcing Pod Security",
		r:    request{user: gotest, operation: "DELETE", namespace: "repos", oldObject: own},
	}, {
		name: "another check creates its own Pod",
		r:    request{user: review, operation: "CREATE", namespace: "repos", nsLabels: restricted, object: pod("check-review", "")},
	}, {
		name: "creates a Pod in its own namespace",
		r:    request{user: gotest, operation: "CREATE", namespace: "check-gotest", nsLabels: restricted, object: own},
		want: programs,
	}, {
		name: "creates a Pod in another check's namespace",
		r:    request{user: gotest, operation: "CREATE", namespace: "check-gofmt", nsLabels: restricted, object: pod("check-gotest", "check-gofmt")},
		want: programs,
	}, {
		name: "creates a Pod in the core program's namespace",
		r:    request{user: gotest, operation: "CREATE", namespace: "git-k8s", nsLabels: restricted, object: pod("check-gotest", "git-k8s")},
		want: programs,
	}, {
		name: "deletes the core program's Pod",
		r:    request{user: gotest, operation: "DELETE", namespace: "git-k8s", oldObject: pod("", "git-k8s")},
		want: programs,
	}, {
		name: "creates a Pod without its label",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: restricted, object: pod("", "")},
		want: label,
	}, {
		name: "creates a Pod with only check-gotest's app label",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: restricted, object: appLabel},
		want: label,
	}, {
		name: "creates a Pod with another check's label",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: restricted, object: pod("check-gofmt", "")},
		want: label,
	}, {
		name: "creates a Pod that runs as another service account",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: restricted, object: pod("check-gotest", "rogue")},
		want: account,
	}, {
		name: "creates a Pod that names another service account in the deprecated field",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: restricted, object: deprecated},
		want: account,
	}, {
		name: "creates a Pod in a namespace without Pod Security labels",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", object: own},
		want: unenforced,
	}, {
		name: "creates a Pod in a namespace that enforces privileged",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: map[string]string{"pod-security.kubernetes.io/enforce": "privileged"}, object: own},
		want: unenforced,
	}, {
		name: "creates a Pod in a namespace that only warns",
		r:    request{user: gotest, operation: "CREATE", namespace: "repos", nsLabels: map[string]string{"pod-security.kubernetes.io/warn": "restricted"}, object: own},
		want: unenforced,
	}, {
		name: "patches its Pod after the namespace stops enforcing Pod Security",
		r:    request{user: gotest, operation: "UPDATE", namespace: "repos", object: own, oldObject: own},
		want: unenforced,
	}, {
		name: "patches another check's Pod",
		r:    request{user: gotest, operation: "UPDATE", namespace: "repos", nsLabels: restricted, object: pod("check-review", ""), oldObject: pod("check-review", "")},
		want: others,
	}, {
		name: "patches a Pod that no check owns",
		r:    request{user: gotest, operation: "UPDATE", namespace: "repos", nsLabels: restricted, object: pod("", ""), oldObject: pod("", "")},
		want: others,
	}, {
		name: "labels a Pod that it doesn't own as its own",
		r:    request{user: gotest, operation: "UPDATE", namespace: "repos", nsLabels: restricted, object: own, oldObject: pod("", "")},
		want: others,
	}, {
		name: "gives its Pod another check's label",
		r:    request{user: gotest, operation: "UPDATE", namespace: "repos", nsLabels: restricted, object: pod("check-review", ""), oldObject: own},
		want: label,
	}, {
		name: "removes its label from its Pod",
		r:    request{user: gotest, operation: "UPDATE", namespace: "repos", nsLabels: restricted, object: pod("", ""), oldObject: own},
		want: label,
	}, {
		name: "deletes another check's Pod",
		r:    request{user: gotest, operation: "DELETE", namespace: "repos", nsLabels: restricted, oldObject: pod("check-review", "")},
		want: others,
	}, {
		name: "deletes a Pod that no check owns",
		r:    request{user: gotest, operation: "DELETE", namespace: "repos", nsLabels: restricted, oldObject: pod("", "")},
		want: others,
	}, {
		name: "adds an ephemeral container to another check's Pod",
		r:    request{user: gotest, operation: "UPDATE", subresource: "ephemeralcontainers", namespace: "repos", nsLabels: restricted, object: pod("check-review", ""), oldObject: pod("check-review", "")},
		want: others,
	}, {
		name: "writes the status of another check's Pod",
		r:    request{user: gotest, operation: "UPDATE", subresource: "status", namespace: "repos", nsLabels: restricted, object: pod("check-review", ""), oldObject: pod("check-review", "")},
		want: others,
	}, {
		name: "resizes another check's Pod",
		r:    request{user: gotest, operation: "UPDATE", subresource: "resize", namespace: "repos", nsLabels: restricted, object: pod("check-review", ""), oldObject: pod("check-review", "")},
		want: others,
	}, {
		name: "the core program creates a Pod in its namespace",
		r:    request{user: "system:serviceaccount:git-k8s:git-k8s", operation: "CREATE", namespace: "git-k8s", object: pod("", "git-k8s")},
	}, {
		name: "a person creates a Pod with check-gotest's label in a check's namespace",
		r:    request{user: "alice@example.com", operation: "CREATE", namespace: "check-gofmt", object: pod("check-gotest", "check-gofmt")},
	}, {
		name: "the garbage collector deletes a check's Pod",
		r:    request{user: "system:serviceaccount:kube-system:generic-garbage-collector", operation: "DELETE", namespace: "repos", oldObject: own},
	}, {
		name: "another account in a check's namespace isn't the check",
		r:    request{user: "system:serviceaccount:check-gotest:default", operation: "CREATE", namespace: "check-gofmt", object: pod("", "check-gofmt")},
	}, {
		name: "an account named after a check in another namespace isn't the check",
		r:    request{user: "system:serviceaccount:repos:check-gotest", operation: "CREATE", namespace: "check-gofmt", object: pod("", "check-gofmt")},
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
