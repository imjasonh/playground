// Package gitk8s defines the git-k8s API and the code that its controllers
// share.
//
// People write GitRepository objects. The repository controller lists each
// repository's branches and owns one GitBranch object for every branch that
// the repository's rules select. Check controllers each write their own
// entry in a GitBranch's status, and the merge controller fast-forwards a
// branch's parent when the parent's merge policy allows.
package gitk8s

import (
	"crypto/sha256"
	"encoding/hex"
	"strings"

	"github.com/imjasonh/playground/kube"
)

// Group is the API group of every git-k8s type.
const Group = "git-k8s.imjasonh.com"

// APIVersion is the apiVersion of every git-k8s type.
const APIVersion = Group + "/v1alpha1"

// RepositoryLabel is the label on each GitBranch that names the
// GitRepository it belongs to.
const RepositoryLabel = Group + "/repository"

// ApproveAnnotation on a GitBranch approves one commit for the approval
// check. Its value is the commit's SHA, or a prefix of at least seven
// characters.
const ApproveAnnotation = Group + "/approve"

// FixerTrailer is the commit trailer on every commit that a check pushes.
// Its value is the check's name. MergePolicy.MaxAutomatedCommits limits how
// many commits with this trailer a branch can have.
const FixerTrailer = "Git-K8s-Fixer"

// GitRepository is a remote git repository and the rules that select which
// of its branches to track.
type GitRepository struct {
	kube.Object `kube:"group=git-k8s.imjasonh.com,version=v1alpha1,shortName=gitrepo,category=git-k8s"`
	Spec        GitRepositorySpec   `json:"spec"`
	Status      GitRepositoryStatus `json:"status,omitzero"`
}

// GitRepositorySpec says where a repository is and which branches to track.
type GitRepositorySpec struct {
	URL       string     `json:"url" kube:"minLength=1,column=URL" doc:"Remote URL. Controllers pass it to git, so https, http, git, and file URLs work."`
	SecretRef *SecretRef `json:"secretRef,omitempty" doc:"Secret in the same namespace with username and password keys for HTTP basic authentication, such as a kubernetes.io/basic-auth Secret. Without a username, controllers send git."`
	// PollInterval is a Go duration.
	PollInterval string       `json:"pollInterval,omitempty" kube:"default=30s" pattern:"^([0-9]+(ms|s|m|h))+$" doc:"How often to list the remote's branches, such as 30s or 5m."`
	Branches     []BranchRule `json:"branches,omitempty" doc:"Rules that select branches to track. For each remote branch, the first rule whose match pattern matches applies. Branches that match no rule aren't tracked."`
}

// SecretRef names a Secret in the same namespace.
type SecretRef struct {
	Name string `json:"name" kube:"minLength=1"`
}

// BranchRule selects branches by name and says what they propose changes
// to.
type BranchRule struct {
	Match  string       `json:"match" kube:"minLength=1" doc:"Glob matched against branch names without refs/heads/. A * matches any characters except /, ? matches one character except /, and a ** path segment matches zero or more segments."`
	Parent string       `json:"parent,omitempty" doc:"Branch that matching branches propose changes to. Checks run on each matching branch, and the merge controller fast-forwards the parent to it when the parent's merge policy allows."`
	Merge  *MergePolicy `json:"merge,omitempty" doc:"What a branch needs before it lands on a branch that this rule matches. Without a merge policy, nothing lands on matching branches."`
}

// MergePolicy is what a branch needs before it lands on its parent.
type MergePolicy struct {
	Checks              []CheckPolicy `json:"checks,omitempty" doc:"Checks that run on every branch proposed to this one."`
	When                string        `json:"when,omitempty" doc:"CEL expression that must be true to land a branch. The checks variable maps each check name to an object with passed (bool), state (string), and outputs (map of strings). A check with no result for the branch's current commits has state Pending. Without an expression, every listed check must pass."`
	Landing             string        `json:"landing,omitempty" kube:"enum=FastForward,default=FastForward" doc:"How to land a branch. FastForward moves the parent to the branch's head, so the parent ends up at the commit that the checks saw."`
	MaxAutomatedCommits *int32        `json:"maxAutomatedCommits,omitempty" kube:"min=0,max=100,default=5" doc:"Most commits that checks can push to one branch, counted by the Git-K8s-Fixer trailer. The limit stops two checks that disagree from pushing forever."`
	MaxAgentRuns        *int32        `json:"maxAgentRuns,omitempty" kube:"min=0,max=1000,default=10" doc:"Most agent runs that each agentic check, such as review, can start on one branch. Each new head needs a run, so the limit caps what one branch can cost."`
	// DeleteMergedBranches deletes a branch from the remote after it lands.
	DeleteMergedBranches bool `json:"deleteMergedBranches,omitempty" doc:"Delete a branch from the remote after it lands."`
}

// Check returns the policy for the named check, or nil if the policy doesn't
// list it.
func (p *MergePolicy) Check(name string) *CheckPolicy {
	if p == nil {
		return nil
	}
	for i := range p.Checks {
		if p.Checks[i].Name == name {
			return &p.Checks[i]
		}
	}
	return nil
}

// MaxCommits returns MaxAutomatedCommits, or its default of 5 when unset.
func (p *MergePolicy) MaxCommits() int {
	if p == nil || p.MaxAutomatedCommits == nil {
		return 5
	}
	return int(*p.MaxAutomatedCommits)
}

// MaxRuns returns MaxAgentRuns, or its default of 10 when unset.
func (p *MergePolicy) MaxRuns() int {
	if p == nil || p.MaxAgentRuns == nil {
		return 10
	}
	return int(*p.MaxAgentRuns)
}

// CheckPolicy names a check that runs on branches.
type CheckPolicy struct {
	Name    string `json:"name" pattern:"^[a-z]([-a-z0-9]*[a-z0-9])?$" kube:"maxLength=40" doc:"Check name. The check controller with this name handles it."`
	MayPush bool   `json:"mayPush,omitempty" doc:"Let the check push commits that fix what it finds, such as formatting, or merging the parent in."`
}

// GitRepositoryStatus is what the repository controller observed.
type GitRepositoryStatus struct {
	Branches           int32            `json:"branches" kube:"column=Branches" doc:"Number of tracked branches."`
	ObservedGeneration int64            `json:"observedGeneration,omitempty"`
	Conditions         []kube.Condition `json:"conditions,omitempty"`
}

// Repository is a GitRepository without its status. Controllers that fetch
// from and push to a repository read this type, so that the repository
// controller's status writes don't run them again.
type Repository struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=GitRepository,plural=gitrepositories,scope=Namespaced"`
	Spec        GitRepositorySpec `json:"spec"`
}

// GitBranch is one branch that a GitRepository tracks. The repository
// controller owns these objects and writes their spec from what it lists on
// the remote, so don't edit them by hand.
//
// Several controllers write a GitBranch's status, each a different part:
// every check controller writes its own entry in Status.Checks, and the
// merge controller writes the rest. Server-side apply keeps their writes
// apart.
type GitBranch struct {
	kube.Object `kube:"group=git-k8s.imjasonh.com,version=v1alpha1,shortName=gitbr,category=git-k8s"`
	Spec        GitBranchSpec   `json:"spec"`
	Status      GitBranchStatus `json:"status,omitzero"`
}

// GitBranchSpec is a branch as the repository controller last listed it.
type GitBranchSpec struct {
	Repository string       `json:"repository" doc:"Name of the GitRepository in the same namespace."`
	Branch     string       `json:"branch" kube:"column=Branch" doc:"Branch name without refs/heads/."`
	Head       string       `json:"head" kube:"column=Head" doc:"Commit that the branch points to on the remote."`
	Parent     string       `json:"parent,omitempty" kube:"column=Parent" doc:"Branch that this branch proposes changes to."`
	ParentHead string       `json:"parentHead,omitempty" doc:"Commit that the parent points to on the remote, listed at the same time as head."`
	Merge      *MergePolicy `json:"merge,omitempty" doc:"The parent's merge policy, copied from the repository rule that matches the parent."`
}

// GitBranchStatus holds check results and the merge controller's state.
type GitBranchStatus struct {
	Checks             map[string]CheckResult `json:"checks,omitempty" doc:"Check results by check name. Each check controller writes only its own entry."`
	State              string                 `json:"state,omitempty" kube:"column=State" doc:"Why the branch has or hasn't landed on its parent, the same as the Merged condition's reason."`
	ObservedGeneration int64                  `json:"observedGeneration,omitempty"`
	Conditions         []kube.Condition       `json:"conditions,omitempty"`
}

// Check result states.
const (
	// Running means the check started work that hasn't finished, such as a
	// Pod.
	Running = "Running"
	Passed  = "Passed"
	Failed  = "Failed"
	// Fixed means the check pushed a commit that fixes what it found. The
	// branch's head moves, and the check runs again on the new head.
	Fixed = "Fixed"
	// Error means the check couldn't run. Its controller retries.
	Error = "Error"
	// Pending is the state that merge gates see for a check with no result
	// for the branch's current commits. Check controllers don't write it.
	Pending = "Pending"
)

// CheckResult is one check's result for one commit.
type CheckResult struct {
	Commit       string            `json:"commit" doc:"Branch head that the result is for."`
	ParentCommit string            `json:"parentCommit,omitempty" doc:"Parent head that the result is for, for checks whose results depend on the parent."`
	State        string            `json:"state" kube:"enum=Running|Passed|Failed|Fixed|Error"`
	Message      string            `json:"message,omitempty"`
	Outputs      map[string]string `json:"outputs,omitempty" doc:"Values that merge gates can read, such as a risk level."`
}

// Fresh reports whether r is for these branch and parent heads. A result
// without a parent commit is for any parent head.
func (r *CheckResult) Fresh(head, parentHead string) bool {
	return r != nil && r.Commit == head && (r.ParentCommit == "" || r.ParentCommit == parentHead)
}

// Final reports whether r's state won't change for its commits.
func (r *CheckResult) Final() bool {
	return r != nil && (r.State == Passed || r.State == Failed || r.State == Fixed)
}

// Short returns the first 12 characters of a commit SHA, for messages.
func Short(sha string) string {
	if len(sha) > 12 {
		return sha[:12]
	}
	return sha
}

// BranchObjectName returns the name of the GitBranch for a branch of a
// repository.
//
// Branch names can hold characters that object names can't, and two branch
// names can reduce to the same letters, so the name ends with a hash of the
// repository and branch names. The name is at most 63 characters, so it's
// also a valid label value.
func BranchObjectName(repository, branch string) string {
	sum := sha256.Sum256([]byte(repository + "\x00" + branch))
	hash := hex.EncodeToString(sum[:5])

	var b strings.Builder
	for _, r := range strings.ToLower(repository + "-" + branch) {
		switch {
		case r >= 'a' && r <= 'z', r >= '0' && r <= '9':
			b.WriteRune(r)
		case !strings.HasSuffix(b.String(), "-"):
			b.WriteByte('-')
		}
	}
	slug := strings.Trim(b.String(), "-")
	if limit := 63 - 1 - len(hash); len(slug) > limit {
		slug = strings.TrimRight(slug[:limit], "-")
	}
	if slug == "" {
		return "b-" + hash
	}
	return slug + "-" + hash
}
