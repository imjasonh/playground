package mirror

import (
	"context"
	"fmt"
	"log/slog"
	"regexp"
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

// mayFetch reports whether who may fetch repo: a controller with a branch
// prefix, a check that one of repo's merge policies lists, or a Pending Pod
// in repo's namespace that the gotest check runs on one of repo's branches.
// An error means that the mirror couldn't get the Pod.
func (m *Mirror) mayFetch(ctx context.Context, who caller.Caller, repo *gitk8s.Repository) (bool, error) {
	if len(m.prefixes(who)) > 0 {
		return true, nil
	}
	if check, ok := who.Check(); ok && listed(repo, check, false) {
		return true, nil
	}
	if who.Pod == "" || who.PodUID == "" || who.Namespace != repo.Namespace || !runsPod(ctx, repo, who.Pod) {
		return false, nil
	}
	return isTestPod(ctx, who)
}

// mayPushAny reports whether who may push some branch of repo.
func (m *Mirror) mayPushAny(who caller.Caller, repo *gitk8s.Repository) bool {
	if len(m.prefixes(who)) > 0 {
		return true
	}
	check, ok := who.Check()
	return ok && listed(repo, check, true)
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

// runsPod reports whether the gotest check's running result on a branch of
// repo names pod, which the check started to work on the branch. Of the
// service accounts, config/policy.yaml lets only the check's write that
// result, but the check names its Pod before it creates the Pod, so
// isTestPod checks the Pod itself.
func runsPod(ctx context.Context, repo *gitk8s.Repository, pod string) bool {
	branches := kube.List[gitk8s.GitBranch](ctx, kube.InNamespace(repo.Namespace),
		kube.MatchingLabels(map[string]string{gitk8s.RepositoryLabel: repo.Name}))
	for _, b := range branches {
		if r, ok := b.Status.Checks[gitk8s.GoTestCheck]; ok && r.State == gitk8s.Running && r.Outputs["pod"] == pod {
			return true
		}
	}
	return false
}

// isTestPod reports whether who's token is bound to a Pod of the gotest
// check that is Pending. The Pod must have the token's UID, so it isn't
// another Pod with the same name, and kube's controller label on it must
// name the check's controller. The check's Pods fetch only from an init
// container, and a Pod is Pending while its init containers run, so a token
// stops fetching once its Pod's tests start.
func isTestPod(ctx context.Context, who caller.Caller) (bool, error) {
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
	case pod.Labels[gitk8s.ControllerLabel] != gitk8s.GoTestController:
		reason = fmt.Sprintf("the Pod's %s label isn't %s", gitk8s.ControllerLabel, gitk8s.GoTestController)
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

// refuse returns why who may not make update c to repo, or "" if it may.
func (m *Mirror) refuse(who caller.Caller, repo *gitk8s.Repository, c command) string {
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
	check, ok := who.Check()
	switch {
	case !ok && len(prefixes) > 0:
		return fmt.Sprintf("%s may push only branches under %s", who, strings.Join(prefixes, ", "))
	case !ok:
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
