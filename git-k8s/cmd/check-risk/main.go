// Command check-risk rates how risky a branch's change is.
//
// The risk check compares the branch's head with its merge base on the
// parent. A change is high risk when it changes more lines than -max-lines,
// or touches a path that matches a -sensitive glob; otherwise it's low risk.
// The check always passes and reports the rating in its outputs, so a merge
// gate decides what to do with it:
//
//	when: checks.risk.outputs.level == "low" || checks.approval.passed
package main

import (
	"context"
	"flag"
	"fmt"
	"strconv"
	"strings"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/mirror"
	"github.com/imjasonh/playground/kube"
)

// Branch is this check's view of a GitBranch.
type Branch struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=GitBranch,plural=gitbranches,scope=Namespaced"`
	Spec        gitk8s.GitBranchSpec `json:"spec"`
	Status      struct {
		Checks struct {
			Result *gitk8s.CheckResult `json:"risk,omitempty"`
		} `json:"checks,omitzero"`
	} `json:"status,omitzero"`
}

func (b *Branch) Parts() (*kube.ObjectMeta, *gitk8s.GitBranchSpec, **gitk8s.CheckResult) {
	return &b.ObjectMeta, &b.Spec, &b.Status.Checks.Result
}

var (
	maxLines  = flag.Int("max-lines", 200, "changed lines above which a change is high risk")
	sensitive = flag.String("sensitive", "", "comma-separated globs of paths that make a change high risk, such as auth/**,**/*.pem")
)

var check = checks.Check{Name: "risk", UsesParent: true, FilesOnly: true, Remote: mirror.Remote, Run: run}

func run(ctx context.Context, in *checks.Input) (checks.Verdict, error) {
	repo, err := in.Repo(ctx)
	if err != nil {
		return checks.Verdict{}, err
	}
	base, err := in.MergeBase(ctx)
	if err != nil {
		return checks.Verdict{}, err
	}
	if base == "" {
		v := checks.Pass("risk is high: %s has no history in common with %s", in.Spec.Branch, in.Spec.Parent)
		v.Outputs = map[string]string{"level": "high"}
		return v, nil
	}
	stats, err := repo.Numstat(ctx, base, in.Spec.Head)
	if err != nil {
		return checks.Verdict{}, err
	}
	lines := 0
	var hits []string
	for _, s := range stats {
		lines += max(s.Added, 0) + max(s.Removed, 0)
		for p := range strings.SplitSeq(*sensitive, ",") {
			if p = strings.TrimSpace(p); p != "" && gitk8s.Match(p, s.Path) {
				hits = append(hits, s.Path)
				break
			}
		}
	}
	var reasons []string
	if lines > *maxLines {
		reasons = append(reasons, fmt.Sprintf("changes %d lines, more than %d", lines, *maxLines))
	}
	if len(hits) > 0 {
		reasons = append(reasons, "touches "+strings.Join(hits, ", "))
	}
	level := "low"
	if len(reasons) > 0 {
		level = "high"
	} else {
		reasons = []string{fmt.Sprintf("changes %d lines in %d files", lines, len(stats))}
	}
	v := checks.Pass("risk is %s: %s", level, strings.Join(reasons, "; "))
	v.Outputs = map[string]string{"level": level, "lines": strconv.Itoa(lines), "files": strconv.Itoa(len(stats))}
	return v, nil
}

func main() { checks.Main[Branch](check) }
