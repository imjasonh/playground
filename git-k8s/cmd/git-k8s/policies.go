package main

import (
	"context"
	"fmt"
	"slices"
	"strings"

	"github.com/imjasonh/playground/kube"
)

// policyNames are the ValidatingAdmissionPolicies in config/policy.yaml.
var policyNames = []string{"git-k8s-check-results", "git-k8s-branches"}

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

// policiesCondition reports whether the admission policies that keep checks
// apart are installed, with bindings that deny the requests they reject.
// Reading them through the cache runs the reconcile again when they change.
// installs is set when the program installs the policies when it starts.
func policiesCondition(ctx context.Context, installs bool) kube.Condition {
	bindings := kube.List[admissionPolicyBinding](ctx)
	var missing []string
	for _, name := range policyNames {
		denies := func(b *admissionPolicyBinding) bool {
			return b.Spec.PolicyName == name && slices.Contains(b.Spec.ValidationActions, "Deny")
		}
		if kube.Get[admissionPolicy](ctx, "", name) == nil || !slices.ContainsFunc(bindings, denies) {
			missing = append(missing, name)
		}
	}
	if len(missing) > 0 {
		fix := "apply config/policy.yaml"
		if installs {
			fix = "restart the core program to install config/policy.yaml again"
		}
		return kube.Condition{
			Type: "PoliciesInstalled", Status: kube.False, Reason: "Missing",
			Message: fmt.Sprintf("%s: %s isn't installed with a binding that denies, so checks can write each other's results", fix, strings.Join(missing, " and ")),
		}
	}
	return kube.Condition{
		Type: "PoliciesInstalled", Status: kube.True, Reason: "Installed",
		Message: "the admission policies keep checks to their own results",
	}
}
