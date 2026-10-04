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
		PolicyName        string    `json:"policyName"`
		ParamRef          *paramRef `json:"paramRef"`
		ValidationActions []string  `json:"validationActions"`
	} `json:"spec"`
}

type paramRef struct {
	ParameterNotFoundAction string `json:"parameterNotFoundAction"`
}

// policiesCondition reports whether the admission policies that keep checks
// apart are installed, with bindings that deny the requests they reject,
// even while the bindings' parameters are missing. Reading them through the
// cache runs the reconcile again when they change. installs is set when the
// program installs the policies when it starts.
func policiesCondition(ctx context.Context, installs bool) kube.Condition {
	bindings := kube.List[admissionPolicyBinding](ctx)
	var missing, weak, patches []string
	for _, name := range policyNames {
		var own *admissionPolicyBinding
		denies := false
		for _, b := range bindings {
			if b.Spec.PolicyName == name {
				denies = denies || denyPatch(b) == ""
				if b.Name == name {
					own = b
				}
			}
		}
		policy := kube.Get[admissionPolicy](ctx, "", name)
		if policy != nil && denies {
			continue
		}
		if own != nil {
			if patch := denyPatch(own); patch != "" {
				weak = append(weak, name)
				patches = append(patches, fmt.Sprintf("kubectl patch validatingadmissionpolicybinding %s --type=merge -p '%s'", name, patch))
			}
		}
		if policy == nil || own == nil {
			missing = append(missing, name)
		}
	}
	if len(missing) == 0 && len(weak) == 0 {
		return kube.Condition{
			Type: "PoliciesInstalled", Status: kube.True, Reason: "Installed",
			Message: "the admission policies keep checks to their own results",
		}
	}
	// The patches come before the restart, because restarting the core
	// program while a binding warns stops it. The binding's validationActions
	// would then hold both Warn and Deny, which the API server rejects.
	var problems, fixes []string
	reason := "NotDenying"
	if len(weak) > 0 {
		problem := "the binding %s doesn't deny every request that its policy rejects"
		if len(weak) > 1 {
			problem = "the bindings %s don't deny every request that their policies reject"
		}
		problems = append(problems, fmt.Sprintf(problem, strings.Join(weak, " and ")))
		fixes = append(fixes, "run "+strings.Join(patches, " and "))
	}
	if len(missing) > 0 {
		reason = "Missing"
		problem := "%s isn't fully installed"
		if len(missing) > 1 {
			problem = "%s aren't fully installed"
		}
		problems = append(problems, fmt.Sprintf(problem, strings.Join(missing, " and ")))
		if installs {
			fixes = append(fixes, "run kubectl -n git-k8s rollout restart deployment/git-k8s to install config/policy.yaml again")
		} else {
			fixes = append(fixes, "apply config/policy.yaml")
		}
	}
	return kube.Condition{
		Type: "PoliciesInstalled", Status: kube.False, Reason: reason,
		Message: fmt.Sprintf("%s, so checks can write each other's results; %s", strings.Join(problems, ", and "), strings.Join(fixes, ", then ")),
	}
}

// denyPatch returns a merge patch that makes a binding deny every request that
// its policy rejects, or "" if it already does.
func denyPatch(b *admissionPolicyBinding) string {
	var fields []string
	if !slices.Contains(b.Spec.ValidationActions, "Deny") {
		fields = append(fields, `"validationActions":["Deny"]`)
	}
	if b.Spec.ParamRef != nil && b.Spec.ParamRef.ParameterNotFoundAction != "Deny" {
		fields = append(fields, `"paramRef":{"parameterNotFoundAction":"Deny"}`)
	}
	if len(fields) == 0 {
		return ""
	}
	return `{"spec":{` + strings.Join(fields, ",") + `}}`
}
