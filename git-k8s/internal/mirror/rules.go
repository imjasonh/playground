package mirror

import (
	"context"
	"fmt"
	"log/slog"
	"regexp"
	"slices"
	"strings"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/caller"
	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

// Prefix lets a controller start branches: its service account may fetch
// every repository, and create, update, and delete the branches whose names
// start with Prefix, except parents.
type Prefix struct {
	Namespace      string
	ServiceAccount string
	// Prefix ends with a slash, such as deps/.
	Prefix string
}

func (p Prefix) String() string { return p.Namespace + "/" + p.ServiceAccount + "=" + p.Prefix }

var (
	dnsLabel     = regexp.MustCompile(`^[a-z0-9]([-a-z0-9]{0,61}[a-z0-9])?$`)
	dnsSubdomain = regexp.MustCompile(`^[a-z0-9]([-a-z0-9.]{0,251}[a-z0-9])?$`)
	branchPrefix = regexp.MustCompile(`^([A-Za-z0-9_][-A-Za-z0-9_.]*/)+$`)
)

// ParsePrefix parses NAMESPACE/SERVICEACCOUNT=PREFIX, such as
// git-k8s-deps/git-k8s-deps=deps/.
func ParsePrefix(s string) (Prefix, error) {
	who, prefix, ok := strings.Cut(s, "=")
	ns, sa, ok2 := strings.Cut(who, "/")
	switch {
	case !ok || !ok2 || !dnsLabel.MatchString(ns) || !dnsSubdomain.MatchString(sa):
		return Prefix{}, fmt.Errorf("%q isn't NAMESPACE/SERVICEACCOUNT=PREFIX, such as git-k8s-deps/git-k8s-deps=deps/", s)
	case !branchPrefix.MatchString(prefix) || strings.Contains(prefix, "..") || strings.Contains(prefix, ".lock/"):
		return Prefix{}, fmt.Errorf("branch prefix %q must be one or more names that each end with a slash, such as deps/", prefix)
	}
	return Prefix{Namespace: ns, ServiceAccount: sa, Prefix: prefix}, nil
}

// prefixes returns the branch prefixes that who may push under.
func (m *Mirror) prefixes(who caller.Caller) []string {
	var out []string
	for _, p := range m.Prefixes {
		if p.Namespace == who.Namespace && p.ServiceAccount == who.Name {
			out = append(out, p.Prefix)
		}
	}
	return out
}

// mayFetch reports whether who, which runs check, or no check if check is
// "", may fetch repo: a controller with a branch prefix, a check that one of
// repo's merge policies lists, or a Pending Pod in repo's namespace that
// such a check runs on one of repo's branches. An error means that the
// mirror couldn't get the Pod.
func (m *Mirror) mayFetch(ctx context.Context, who caller.Caller, check string, repo *gitk8s.Repository) (bool, error) {
	if len(m.prefixes(who)) > 0 {
		return true, nil
	}
	if check != "" && listed(repo, check, false) {
		return true, nil
	}
	if who.Pod == "" || who.PodUID == "" || who.Namespace != repo.Namespace {
		return false, nil
	}
	checks := podChecks(ctx, repo, who.Pod)
	if len(checks) == 0 {
		return false, nil
	}
	return isCheckPod(ctx, who, checks)
}

// mayPushAny reports whether who, which runs check, may push some branch of
// repo.
func (m *Mirror) mayPushAny(who caller.Caller, check string, repo *gitk8s.Repository) bool {
	if len(m.prefixes(who)) > 0 {
		return true
	}
	return check != "" && listed(repo, check, true)
}

// listed reports whether a merge policy of repo lists check, and with
// mayPush, lets it push.
func listed(repo *gitk8s.Repository, check string, mayPush bool) bool {
	for _, rule := range repo.Spec.Branches {
		if p := rule.Merge.Check(check); p != nil && (p.MayPush || !mayPush) {
			return true
		}
	}
	return false
}

// podChecks returns the checks whose running results on branches of repo
// name pod as their Pod, which each check started to work on the branch. A result counts only on a branch whose merge policy lists the
// check, where the checks framework runs it, so a check's Pods can't fetch
// a repository that the check itself can't. Of the service accounts,
// config/policy.yaml lets only a check's own write its result, but a check
// can name its Pod before kube creates the Pod, so isCheckPod checks the
// Pod itself.
func podChecks(ctx context.Context, repo *gitk8s.Repository, pod string) []string {
	branches := kube.List[gitk8s.GitBranch](ctx, kube.InNamespace(repo.Namespace),
		kube.MatchingLabels(map[string]string{gitk8s.RepositoryLabel: repo.Name}))
	var checks []string
	for _, b := range branches {
		for check, r := range b.Status.Checks {
			if r.State == gitk8s.Running && r.Pod == pod && b.Spec.Merge.Check(check) != nil && !slices.Contains(checks, check) {
				checks = append(checks, check)
			}
		}
	}
	return checks
}

// isCheckPod reports whether who's token is bound to a Pending Pod of one
// of checks. The Pod must have the token's UID, so it isn't another Pod
// with the same name, and kube's controller label on it must name the
// controller of a check whose result names the Pod, so one check's result
// can't let another check's Pod fetch. The checks' Pods fetch only from an
// init container, and a Pod is Pending while its init containers run, so a
// token stops fetching once its Pod's main containers start.
func isCheckPod(ctx context.Context, who caller.Caller, checks []string) (bool, error) {
	pod, err := kube.Fetch[k8s.Pod](ctx, who.Namespace, who.Pod)
	if err != nil {
		return false, fmt.Errorf("getting Pod %s/%s: %w", who.Namespace, who.Pod, err)
	}
	var reason string
	switch {
	case pod == nil:
		reason = "the Pod doesn't exist"
	case pod.UID != who.PodUID:
		reason = "the token is bound to another Pod with the same name"
	case !slices.ContainsFunc(checks, func(check string) bool { return pod.Labels[gitk8s.ControllerLabel] == "check-"+check }):
		reason = fmt.Sprintf("the Pod's %s label isn't check- followed by the name of a check whose result names the Pod", gitk8s.ControllerLabel)
	case pod.Deleting():
		reason = "the Pod is being deleted"
	case pod.Status.Phase != "Pending":
		reason = fmt.Sprintf("the Pod is %s, not Pending", pod.Status.Phase)
	default:
		return true, nil
	}
	slog.Info("refused a Pod that a running result names", "pod", who.Namespace+"/"+who.Pod, "reason", reason)
	return false, nil
}

// refuse returns why who, which runs check, may not make update c to repo,
// or "" if it may.
func (m *Mirror) refuse(who caller.Caller, check string, repo *gitk8s.Repository, c command) string {
	branch, ok := strings.CutPrefix(c.Ref, headsPrefix)
	if !ok || branch == "" {
		return "the mirror takes only branches, under refs/heads/"
	}
	rules := repo.Spec.Branches
	for _, rule := range rules {
		if rule.Parent == branch {
			return fmt.Sprintf("%s is a parent branch, which only the merge controller updates", branch)
		}
	}
	prefixes := m.prefixes(who)
	for _, p := range prefixes {
		if strings.HasPrefix(branch, p) {
			return ""
		}
	}
	switch {
	case check == "" && len(prefixes) > 0:
		return fmt.Sprintf("%s may push only branches under %s", who, strings.Join(prefixes, ", "))
	case check == "":
		return fmt.Sprintf("%s may not push", who)
	case isZero(c.Old):
		return "checks may not create branches"
	case isZero(c.New):
		return "checks may not delete branches"
	}
	rule := gitk8s.FindRule(rules, branch)
	if rule == nil || rule.Parent == "" || rule.Parent == branch {
		return fmt.Sprintf("checks may push only to branches that have a parent, and %s has none", branch)
	}
	var policy *gitk8s.MergePolicy
	if pr := gitk8s.FindRule(rules, rule.Parent); pr != nil {
		policy = pr.Merge
	}
	if p := policy.Check(check); p == nil || !p.MayPush {
		return fmt.Sprintf("the merge policy of %s doesn't let the %s check push", rule.Parent, check)
	}
	return ""
}
