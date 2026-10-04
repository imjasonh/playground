package main

import (
	"context"
	"fmt"
	"slices"
	"strings"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/kube"
)

// policyNames are the ValidatingAdmissionPolicies in config/policy.yaml.
var policyNames = []string{"git-k8s-check-results", "git-k8s-branches"}

// Each policy in config/policy.yaml has policyVersionAnnotation set to
// policyVersion. Change both when the core program needs a change to the
// policies, so that it reports the earlier policies as outdated.
const (
	policyVersionAnnotation = gitk8s.Group + "/policy-version"
	policyVersion           = "2"
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
	var missing, outdated []string
	for _, name := range policyNames {
		denies := func(b *admissionPolicyBinding) bool {
			return b.Spec.PolicyName == name && slices.Contains(b.Spec.ValidationActions, "Deny")
		}
		p := kube.Get[admissionPolicy](ctx, "", name)
		switch {
		case p == nil || !slices.ContainsFunc(bindings, denies):
			missing = append(missing, name)
		case p.Annotations[policyVersionAnnotation] != policyVersion:
			outdated = append(outdated, name)
		}
	}
	switch {
	case len(missing) > 0:
		return kube.Condition{
			Type: "PoliciesInstalled", Status: kube.False, Reason: "Missing",
			Message: fmt.Sprintf("apply config/policy.yaml: %s isn't installed with a binding that denies", strings.Join(missing, " and ")),
		}
	case len(outdated) > 0:
		return kube.Condition{
			Type: "PoliciesInstalled", Status: kube.False, Reason: "Outdated",
			Message: fmt.Sprintf("apply config/policy.yaml from this release: %s doesn't have %s=%s", strings.Join(outdated, " and "), policyVersionAnnotation, policyVersion),
		}
	}
	return kube.Condition{
		Type: "PoliciesInstalled", Status: kube.True, Reason: "Installed",
		Message: "the admission policies let no service account but the core program's write check results, and stop git-k8s controllers from approving branches",
	}
}
