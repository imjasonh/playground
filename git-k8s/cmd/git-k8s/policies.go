package main

import (
	"context"
	"fmt"
	"slices"
	"strconv"
	"strings"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/kube"
)

// policies are the ValidatingAdmissionPolicies in config/policy.yaml, each
// with what goes wrong while no binding enforces it.
var policies = []struct {
	name      string
	exposures []string
}{
	{"git-k8s-check-results", []string{"any service account that can write GitBranch status can write check results and status.diverged", "checks that can write GitBranch status can change a branch's state and merge queue"}},
	{"git-k8s-branches", []string{"git-k8s service accounts with the approve verb can approve branches", "checks and git-k8s-deps can change GitBranch objects"}},
	{"git-k8s-check-pods", []string{"checks that own Pods can write any Pod in the cluster"}},
	{"git-k8s-approvals", []string{"anyone who can patch a GitBranch can approve it", "the approved-by annotation can name someone who didn't approve"}},
}

// Each policy in config/policy.yaml has policyVersionAnnotation set to
// policyVersion. Raise both when the core program needs a change to the
// policies, so that it reports the earlier policies as outdated.
const (
	policyVersionAnnotation = gitk8s.Group + "/policy-version"
	policyVersion           = 2
)

type admissionPolicy struct {
	kube.Object `kube:"apiVersion=admissionregistration.k8s.io/v1,kind=ValidatingAdmissionPolicy,plural=validatingadmissionpolicies,scope=Cluster"`
	Spec        struct {
		// ParamKind is set when the policy reads parameters. Only whether it's
		// set matters, so it reads as an empty struct.
		ParamKind *struct{} `json:"paramKind"`
	} `json:"spec"`
}

type admissionPolicyBinding struct {
	kube.Object `kube:"apiVersion=admissionregistration.k8s.io/v1,kind=ValidatingAdmissionPolicyBinding,plural=validatingadmissionpolicybindings,scope=Cluster"`
	Spec        struct {
		PolicyName        string          `json:"policyName"`
		ParamRef          *paramRef       `json:"paramRef"`
		MatchResources    *matchResources `json:"matchResources"`
		ValidationActions []string        `json:"validationActions"`
	} `json:"spec"`
}

type paramRef struct {
	Name      string `json:"name"`
	Namespace string `json:"namespace"`
	// Selector is set when the paramRef selects parameters by label. Only
	// whether it's set matters, so it reads as an empty struct.
	Selector                *struct{} `json:"selector"`
	ParameterNotFoundAction string    `json:"parameterNotFoundAction"`
}

// namesChecks reports whether r names the git-k8s-checks ConfigMap in the
// git-k8s namespace, as the paramRef in config/policy.yaml does.
func (r *paramRef) namesChecks() bool {
	return r != nil && r.Name == "git-k8s-checks" && r.Namespace == "git-k8s"
}

// matchResources holds the parts of a binding's matchResources that can keep
// it from requests that its policy matches. Only whether each part is set
// matters, so rules and expressions read as empty structs.
type matchResources struct {
	NamespaceSelector    *labelSelector `json:"namespaceSelector"`
	ObjectSelector       *labelSelector `json:"objectSelector"`
	ResourceRules        []struct{}     `json:"resourceRules"`
	ExcludeResourceRules []struct{}     `json:"excludeResourceRules"`
}

type labelSelector struct {
	MatchLabels      map[string]string `json:"matchLabels"`
	MatchExpressions []struct{}        `json:"matchExpressions"`
}

// limits reports whether m keeps a binding from some of the requests that its
// policy matches. When someone adds matchResources, the API server fills in
// matchPolicy and empty selectors, which match every request.
func (m *matchResources) limits() bool {
	return m != nil && (m.NamespaceSelector.selects() || m.ObjectSelector.selects() ||
		len(m.ResourceRules) > 0 || len(m.ExcludeResourceRules) > 0)
}

// selects reports whether s leaves out some objects.
func (s *labelSelector) selects() bool {
	return s != nil && (len(s.MatchLabels) > 0 || len(s.MatchExpressions) > 0)
}

// policiesCondition reports whether this release's admission policies in
// config/policy.yaml are installed, with bindings that deny the requests
// they reject, even while the bindings' parameters are missing. Reading them
// through the cache runs the reconcile again when they change. installs is
// set when the program installs the policies when it starts.
func policiesCondition(ctx context.Context, installs bool) kube.Condition {
	bindings := kube.List[admissionPolicyBinding](ctx)
	var missing, weak, noParamRef, otherParamRef, warns, outdated, newer, patches, exposures, ignores []string
	// ignoresAt is where the clause about the policies in ignores goes in
	// exposures, so that the clauses keep the order of the policies.
	ignoresAt := 0
	for _, p := range policies {
		policy := kube.Get[admissionPolicy](ctx, "", p.name)
		if policy != nil {
			switch v, err := strconv.Atoi(policy.Annotations[policyVersionAnnotation]); {
			case err != nil || v < policyVersion:
				outdated = append(outdated, p.name)
			case v > policyVersion:
				newer = append(newer, p.name)
			}
		}
		params := policy != nil && policy.Spec.ParamKind != nil
		var own *admissionPolicyBinding
		denies, ignoring := false, false
		for _, b := range bindings {
			if b.Spec.PolicyName == p.name {
				denies = denies || denyPatch(b, params) == ""
				ignoring = ignoring || lacksOnlyParamRef(b, params)
				if b.Name == p.name {
					own = b
				}
			}
		}
		// While its own binding warns, the core program stops the next time it
		// starts, even if another binding enforces the policy, because its apply
		// adds Deny next to the Warn.
		warn := installs && own != nil && slices.Contains(own.Spec.ValidationActions, "Warn")
		if warn {
			warns = append(warns, p.name)
		}
		if policy != nil && denies {
			if warn {
				patches = append(patches, patchCommand(own, params))
			}
			continue
		}
		// A binding that lacks only the paramRef from config/policy.yaml
		// enforces the policy, but the API server evaluates it without
		// parameters or with another ConfigMap, so the policy ignores the
		// entries in the git-k8s-checks ConfigMap.
		if ignoring {
			if len(ignores) == 0 {
				ignoresAt = len(exposures)
			}
			ignores = append(ignores, p.name)
		} else {
			exposures = append(exposures, p.exposures...)
		}
		if own != nil && denyPatch(own, params) != "" {
			switch {
			case !lacksOnlyParamRef(own, params):
				weak = append(weak, p.name)
			case own.Spec.ParamRef == nil:
				noParamRef = append(noParamRef, p.name)
			default:
				otherParamRef = append(otherParamRef, p.name)
			}
			patches = append(patches, patchCommand(own, params))
		}
		if policy == nil || own == nil {
			missing = append(missing, p.name)
		}
	}
	if len(missing) == 0 && len(weak) == 0 && len(noParamRef) == 0 && len(otherParamRef) == 0 && len(warns) == 0 && len(outdated) == 0 && len(newer) == 0 {
		return kube.Condition{
			Type: "PoliciesInstalled", Status: kube.True, Reason: "Installed",
			Message: "the admission policies keep git-k8s service accounts from approving branches, let no service account but the core program's write check results, keep checks to their own Pods, and check who approves branches",
		}
	}
	var problems, sentences, fixes []string
	reason := "Newer"
	if len(outdated) > 0 {
		reason = "Outdated"
	}
	if len(warns) > 0 {
		reason = "BindingWarns"
	}
	if len(weak) > 0 {
		reason = "NotDenying"
		problem := "the binding %s doesn't deny every request that its policy rejects"
		if len(weak) > 1 {
			problem = "the bindings %s don't deny every request that their policies reject"
		}
		problems = append(problems, fmt.Sprintf(problem, list(weak)))
	}
	if len(noParamRef) > 0 {
		reason = "NotDenying"
		problem := "the binding %s has no paramRef"
		if len(noParamRef) > 1 {
			problem = "the bindings %s have no paramRef"
		}
		problems = append(problems, fmt.Sprintf(problem, list(noParamRef)))
	}
	if len(otherParamRef) > 0 {
		reason = "NotDenying"
		problem := "the binding %s has a paramRef that doesn't name git-k8s/git-k8s-checks"
		if len(otherParamRef) > 1 {
			problem = "the bindings %s have paramRefs that don't name git-k8s/git-k8s-checks"
		}
		problems = append(problems, fmt.Sprintf(problem, list(otherParamRef)))
	}
	if len(missing) > 0 {
		reason = "Missing"
		problem := "%s isn't fully installed"
		if len(missing) > 1 {
			problem = "%s aren't fully installed"
		}
		problems = append(problems, fmt.Sprintf(problem, list(missing)))
	}
	if len(ignores) > 0 {
		ignore := "%s ignores the entries in the git-k8s-checks ConfigMap"
		if len(ignores) > 1 {
			ignore = "%s ignore the entries in the git-k8s-checks ConfigMap"
		}
		exposures = slices.Insert(exposures, ignoresAt, fmt.Sprintf(ignore, list(ignores)))
	}
	if len(problems) > 0 {
		sentences = append(sentences, strings.Join(problems, ", and ")+", so "+clauses(exposures))
	}
	if len(warns) > 0 {
		warn := "the binding %s warns"
		if len(warns) > 1 {
			warn = "the bindings %s warn"
		}
		sentences = append(sentences, fmt.Sprintf(warn, list(warns))+", so the core program stops the next time it starts")
	}
	if len(outdated) > 0 {
		problem := "%s doesn't have %s=%d"
		if len(outdated) > 1 {
			problem = "%s don't have %s=%d"
		}
		sentences = append(sentences, fmt.Sprintf(problem, list(outdated), policyVersionAnnotation, policyVersion))
	}
	if len(newer) > 0 {
		problem := "%s has a %s later than %d"
		if len(newer) > 1 {
			problem = "%s have a %s later than %d"
		}
		sentences = append(sentences, fmt.Sprintf(problem, list(newer), policyVersionAnnotation, policyVersion))
	}
	// The patches come before the restart, because restarting the core
	// program while a binding warns stops it. The binding's validationActions
	// would then hold both Warn and Deny, which the API server rejects.
	if len(patches) > 0 {
		fixes = append(fixes, "run "+list(patches))
	}
	install := "apply config/policy.yaml"
	if len(outdated) > 0 || len(newer) > 0 {
		install += " from this release"
	}
	if installs {
		install = "run kubectl -n git-k8s rollout restart deployment/git-k8s to install config/policy.yaml again"
	}
	switch {
	case len(newer) > 0:
		// An upgrade that applies the policies before the core program looks
		// the same as a rollback of the core program.
		fixes = append(fixes, "upgrade the core program, or, if you rolled it back, "+install)
	case len(missing) > 0 || len(outdated) > 0:
		fixes = append(fixes, install)
	}
	return kube.Condition{
		Type: "PoliciesInstalled", Status: kube.False, Reason: reason,
		Message: strings.Join(sentences, "; ") + "; " + strings.Join(fixes, ", then "),
	}
}

// patchCommand returns the kubectl command that applies b's denyPatch.
func patchCommand(b *admissionPolicyBinding, params bool) string {
	return fmt.Sprintf("kubectl patch validatingadmissionpolicybinding %s --type=merge -p '%s'", b.Name, denyPatch(b, params))
}

// clauses joins independent clauses as "a", "a, and b", or "a, b, and c".
func clauses(cs []string) string {
	if len(cs) < 2 {
		return strings.Join(cs, "")
	}
	return strings.Join(cs[:len(cs)-1], ", ") + ", and " + cs[len(cs)-1]
}

// list joins items as "a", "a and b", or "a, b, and c".
func list(items []string) string {
	if len(items) == 2 {
		return items[0] + " and " + items[1]
	}
	return clauses(items)
}

// denyPatch returns a merge patch that makes a binding deny every request that
// its policy rejects, or "" if it already does. config/policy.yaml sets no
// matchResources, so the core program's apply keeps any that someone adds, and
// the patch removes them. params is set when the binding's policy reads
// parameters. The API server ignores the paramRef of a binding whose policy
// doesn't. For a binding without a paramRef, the API server evaluates a policy
// that reads parameters without them, and for a binding whose paramRef doesn't
// name git-k8s/git-k8s-checks, it evaluates the policy with another ConfigMap.
// Either way, the policy ignores the entries in the git-k8s-checks ConfigMap,
// and the patch sets the paramRef from config/policy.yaml.
func denyPatch(b *admissionPolicyBinding, params bool) string {
	var fields []string
	if !slices.Contains(b.Spec.ValidationActions, "Deny") {
		fields = append(fields, `"validationActions":["Deny"]`)
	}
	if params {
		switch r := b.Spec.ParamRef; {
		case !r.namesChecks():
			ref := `"name":"git-k8s-checks","namespace":"git-k8s","parameterNotFoundAction":"Deny"`
			// The API server rejects a paramRef with both a name and a selector.
			if r != nil && r.Selector != nil {
				ref += `,"selector":null`
			}
			fields = append(fields, `"paramRef":{`+ref+`}`)
		case r.ParameterNotFoundAction != "Deny":
			fields = append(fields, `"paramRef":{"parameterNotFoundAction":"Deny"}`)
		}
	}
	if b.Spec.MatchResources.limits() {
		fields = append(fields, `"matchResources":null`)
	}
	if len(fields) == 0 {
		return ""
	}
	return `{"spec":{` + strings.Join(fields, ",") + `}}`
}

// lacksOnlyParamRef reports whether b's policy reads parameters, and b denies
// every request that the policy rejects without them, but has no paramRef or
// one that doesn't name git-k8s/git-k8s-checks. While the ConfigMap that b's
// paramRef names is missing, b lets every request through unless the
// paramRef's parameterNotFoundAction is Deny. An entry in the ConfigMap that
// the policy reads can only make a service account a check, so the policy
// ignores only the entries in the git-k8s-checks ConfigMap.
func lacksOnlyParamRef(b *admissionPolicyBinding, params bool) bool {
	r := b.Spec.ParamRef
	return params && !r.namesChecks() && (r == nil || r.ParameterNotFoundAction == "Deny") && denyPatch(b, false) == ""
}
