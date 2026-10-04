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

// policyNames are the ValidatingAdmissionPolicies in config/policy.yaml.
var policyNames = []string{"git-k8s-check-results", "git-k8s-branches"}

// Each policy in config/policy.yaml has policyVersionAnnotation set to
// policyVersion. Raise both when the core program needs a change to the
// policies, so that it reports the earlier policies as outdated.
const (
	policyVersionAnnotation = gitk8s.Group + "/policy-version"
	policyVersion           = 2
)

type admissionPolicy struct {
	kube.Object `kube:"apiVersion=admissionregistration.k8s.io/v1,kind=ValidatingAdmissionPolicy,plural=validatingadmissionpolicies,scope=Cluster"`
}

type admissionPolicyBinding struct {
	kube.Object `kube:"apiVersion=admissionregistration.k8s.io/v1,kind=ValidatingAdmissionPolicyBinding,plural=validatingadmissionpolicybindings,scope=Cluster"`
	Spec        struct {
		PolicyName        string   `json:"policyName"`
		ValidationActions []string `json:"validationActions"`
	} `json:"spec"`
}

// policiesCondition reports whether this release's admission policies are
// installed, with bindings that deny the requests they reject.
// Reading them through the cache runs the reconcile again when they change.
func policiesCondition(ctx context.Context) kube.Condition {
	bindings := kube.List[admissionPolicyBinding](ctx)
	var missing, outdated, newer []string
	for _, name := range policyNames {
		denies := func(b *admissionPolicyBinding) bool {
			return b.Spec.PolicyName == name && slices.Contains(b.Spec.ValidationActions, "Deny")
		}
		p := kube.Get[admissionPolicy](ctx, "", name)
		if p == nil || !slices.ContainsFunc(bindings, denies) {
			missing = append(missing, name)
			continue
		}
		switch v, err := strconv.Atoi(p.Annotations[policyVersionAnnotation]); {
		case err != nil || v < policyVersion:
			outdated = append(outdated, name)
		case v > policyVersion:
			newer = append(newer, name)
		}
	}
	switch {
	case len(missing) > 0:
		return kube.Condition{
			Type: "PoliciesInstalled", Status: kube.False, Reason: "Missing",
			Message: "apply config/policy.yaml: " + subject(missing, "isn't installed with a binding that denies", "aren't installed with bindings that deny"),
		}
	case len(outdated) > 0:
		return kube.Condition{
			Type: "PoliciesInstalled", Status: kube.False, Reason: "Outdated",
			Message: fmt.Sprintf("apply config/policy.yaml from this release: %s %s=%d", subject(outdated, "doesn't have", "don't have"), policyVersionAnnotation, policyVersion),
		}
	case len(newer) > 0:
		return kube.Condition{
			Type: "PoliciesInstalled", Status: kube.False, Reason: "Newer",
			Message: fmt.Sprintf("upgrade the core program: %s a %s later than %d", subject(newer, "has", "have"), policyVersionAnnotation, policyVersion),
		}
	}
	return kube.Condition{
		Type: "PoliciesInstalled", Status: kube.True, Reason: "Installed",
		Message: "the admission policies let no service account but the core program's write check results, and stop git-k8s controllers from approving branches",
	}
}

// subject joins names into the subject of a message, as in "a", "a and b",
// or "a, b, and c", followed by the verb one for a single name or many for
// more.
func subject(names []string, one, many string) string {
	if len(names) < 2 {
		return strings.Join(names, "") + " " + one
	}
	last, and := len(names)-1, " and "
	if len(names) > 2 {
		and = ", and "
	}
	return strings.Join(names[:last], ", ") + and + names[last] + " " + many
}
