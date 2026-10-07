// Command check-review reviews a branch's change with an AI agent.
//
// For each branch head, the review check runs a Cursor agent in a sandboxed
// Pod with the agent package. The agent reads the change from the merge
// base with the parent, and the files around it, and answers pass or fail.
// The check reports the agent's reasoning as its message, and its summary,
// model, and token usage as notes. When the merge policy lets the check
// push, the agent can also fix what it finds, and the check pushes the fix.
package main

import (
	"context"
	"flag"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/agent"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/mirror"
	"github.com/imjasonh/playground/git-k8s/signing"
	"github.com/imjasonh/playground/kube"
)

// Branch is this check's view of a GitBranch.
type Branch struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=GitBranch,plural=gitbranches,scope=Namespaced"`
	Spec        gitk8s.GitBranchSpec `json:"spec"`
	Status      struct {
		Checks struct {
			Result *gitk8s.CheckResult `json:"review,omitempty"`
		} `json:"checks,omitzero"`
	} `json:"status,omitzero"`
}

func (b *Branch) Parts() (*kube.ObjectMeta, *gitk8s.GitBranchSpec, **gitk8s.CheckResult) {
	return &b.ObjectMeta, &b.Spec, &b.Status.Checks.Result
}

const instructions = `Review the change for problems that keep it from being ready to land: bugs, security problems, lost data, and code that doesn't do what the commit messages say. Read the changed files and the code that they use, not only the diff.

Answer fail only for problems that you can point to in the code, and name the file and line of each one in your reasoning. Don't fail the change for style, naming, or other matters of taste.`

var runner = &agent.Runner{Name: "review"}

// The agent reads the subjects of the branch's commits, so the check isn't
// FilesOnly.
var check = checks.Check{Name: "review", Remote: mirror.Remote, SigningKey: signing.Key, Run: run}

func run(ctx context.Context, in *checks.Input) (checks.Verdict, error) {
	v, _ := runner.Run(ctx, in, agent.Task{Instructions: instructions, Edit: in.Policy.MayPush})
	return v, nil
}

func main() {
	runner.AddFlags(flag.CommandLine)
	checks.Main[Branch](check)
}
