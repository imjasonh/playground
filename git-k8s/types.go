// Package gitk8s defines the git-k8s API and the code that its controllers
// share.
//
// People write GitRepository objects. The mirror in the core program keeps a
// copy of each repository, and the repository controller syncs the copy with
// the external repository and owns one GitBranch object for every branch
// that the repository's rules select. Check controllers send their results
// to the core program, which writes them to each GitBranch's status, and
// the merge controller lands a branch on its parent when the parent's merge
// policy allows.
package gitk8s

import (
	"crypto/sha256"
	"encoding/hex"
	"maps"
	"strings"
	"time"

	"github.com/imjasonh/playground/kube"
)

// Group is the API group of every git-k8s type.
const Group = "git-k8s.imjasonh.com"

// APIVersion is the apiVersion of every git-k8s type.
const APIVersion = Group + "/v1alpha1"

// RepositoryLabel is the label on each GitBranch that names the
// GitRepository it belongs to.
const RepositoryLabel = Group + "/repository"

// ApproveAnnotation on a GitBranch approves one commit's change for the
// approval check. Its value is the commit's full SHA, which approves any
// head that makes the same change, or a prefix of at least seven
// characters, which approves only that commit.
const ApproveAnnotation = Group + "/approve"

// ApprovedByAnnotation on a GitBranch is the username of whoever approved
// the commit in its ApproveAnnotation. The git-k8s-approvals admission
// policy in config/policy.yaml makes it match the request that set the
// approval or took it over.
const ApprovedByAnnotation = Group + "/approved-by"

// FixerTrailer is the commit trailer on every commit that a check pushes,
// except a replay of another commit, which keeps that commit's message.
// Its value is the check's name. MergePolicy.MaxAutomatedCommits limits how
// many commits with this trailer a branch can have.
const FixerTrailer = "Git-K8s-Fixer"

// ControllerLabel is the label that kube puts on each object that a
// controller declares with kube.Own. Its value is the controller's name,
// which for a check is check- followed by the check's name.
const ControllerLabel = "kube.imjasonh.github.io/controller"

// GoTestCheck is the name of the check that runs a branch's tests in Pods
// in the repository's namespace, and GoTestController is the name of its
// controller. The mirror lets those Pods fetch the repository, and the core
// program limits their network access.
const (
	GoTestCheck      = "gotest"
	GoTestController = "check-" + GoTestCheck
)

// MirrorAudience is the audience of the service account tokens that
// programs send to the mirror, the git server in the core program.
const MirrorAudience = "git-k8s-mirror"

// MirrorURL is the mirror's base URL when kube's generate installs the core
// program, as the Service git-k8s in the namespace git-k8s.
const MirrorURL = "http://git-k8s.git-k8s.svc"

// MirrorPath returns the path of a GitRepository's copy on the mirror,
// below the mirror's base URL.
func MirrorPath(namespace, name string) string {
	return "/" + namespace + "/" + name + ".git"
}

// GitRepository is an external git repository, which the mirror keeps a copy
// of, and the rules that select which of its branches to track.
type GitRepository struct {
	kube.Object `kube:"group=git-k8s.imjasonh.com,version=v1alpha1,shortName=gitrepo,category=git-k8s"`
	Spec        GitRepositorySpec   `json:"spec"`
	Status      GitRepositoryStatus `json:"status,omitzero"`
}

// GitRepositorySpec says where a repository is and which branches to track.
type GitRepositorySpec struct {
	// git decodes %XX in a URL and strips brackets from its user and host
	// before it passes them to ssh, so either could hide a leading "-". The
	// pattern allows no "%" before the path, and brackets there only around
	// an IP address or around an scp-like address's host:port. An scp-like
	// address needs a user, because "@" is what tells it apart from git's
	// <transport>::<address> syntax.
	URL       string     `json:"url" kube:"minLength=1,column=URL" pattern:"^((https?|git|ssh)://([^-@/%\\[\\]\\x00-\\x1f\\x7f][^@/%\\[\\]\\x00-\\x1f\\x7f]*@)?([A-Za-z0-9_][A-Za-z0-9_.-]*|\\[[0-9A-Fa-f:.]+\\])(:[0-9]+)?/|[^-@/:%\\[\\]\\x00-\\x1f\\x7f][^@/:%\\[\\]\\x00-\\x1f\\x7f]*@([A-Za-z0-9_][A-Za-z0-9_.-]*|\\[([A-Za-z0-9_][A-Za-z0-9_.-]*(:[0-9]+)?|[0-9A-Fa-f:.]+)\\]):[^-\\x00-\\x1f\\x7f])[^\\x00-\\x1f\\x7f]*$" doc:"URL of the external repository, which the mirror reaches with git: an https, http, git, or ssh URL, or an scp-like address with a user name, such as git@example.com:app.git. Without a user name, write an ssh:// URL, such as ssh://example.com/~/app.git."`
	SecretRef *SecretRef `json:"secretRef,omitempty" doc:"Secret in the same namespace with username and password keys for HTTP basic authentication, such as a kubernetes.io/basic-auth Secret. Without a username, the mirror sends git."`
	// PollInterval is a Go duration.
	PollInterval string       `json:"pollInterval,omitempty" kube:"default=30s" pattern:"^([0-9]+(ms|s|m|h))+$" doc:"How often the mirror fetches the external repository's branches, such as 30s or 5m."`
	OctoSTS      *OctoSTS     `json:"octoSTS,omitempty" doc:"Trust policies that the core program uses to exchange its service account tokens for GitHub tokens with Octo STS. The URL must be the https URL of a github.com repository, such as https://github.com/OWNER/REPO.git."`
	Branches     []BranchRule `json:"branches,omitempty" doc:"Rules that select branches to track. For each branch, the first rule whose match pattern matches applies. Branches that match no rule aren't tracked."`
	// Only the programs that make commits read the Secret that SigningKeyRef
	// names, through package signing.
	SigningKeyRef *SecretRef `json:"signingKeyRef,omitempty" doc:"Secret in the same namespace with an ssh-privatekey key that holds an unencrypted private key in OpenSSH format, such as a kubernetes.io/ssh-auth Secret. It must name a different Secret from secretRef, so that the checks that sign commits never hold the external repository's credentials. Checks use it to sign the commits that they push, the merge controller to sign the commits of squash and rebase landings, and git-k8s-deps to sign its dependency updates. Without it, those commits aren't signed."`
}

// SecretRef names a Secret in the same namespace.
type SecretRef struct {
	Name string `json:"name" kube:"minLength=1"`
}

// OctoSTS names trust policies in a GitHub repository. Each identity is the
// name of a trust policy file, .github/chainguard/IDENTITY.sts.yaml, on the
// repository's default branch.
type OctoSTS struct {
	GitIdentity       string `json:"gitIdentity,omitempty" pattern:"^[A-Za-z0-9][-A-Za-z0-9_.]*$" kube:"maxLength=100" doc:"Identity whose token the mirror fetches and pushes with, instead of a Secret, so secretRef must be empty. Its trust policy needs contents: write."`
	CheckRunsIdentity string `json:"checkRunsIdentity,omitempty" pattern:"^[A-Za-z0-9][-A-Za-z0-9_.]*$" kube:"maxLength=100" doc:"Identity whose token publishes check results as GitHub check runs. Its trust policy needs checks: write. Without it, git-k8s doesn't publish check runs."`
}

// BranchRule selects branches by name and says what they propose changes
// to.
type BranchRule struct {
	Match  string       `json:"match" kube:"minLength=1" doc:"Glob matched against branch names without refs/heads/. A * matches any characters except /, ? matches one character except /, and a ** path segment matches zero or more segments."`
	Parent string       `json:"parent,omitempty" doc:"Branch that matching branches propose changes to. Checks run on each matching branch, and the merge controller lands it on the parent when the parent's merge policy allows."`
	Merge  *MergePolicy `json:"merge,omitempty" doc:"What a branch needs before it lands on a branch that this rule matches. Without a merge policy, nothing lands on matching branches."`
}

// MergePolicy is what a branch needs before it lands on its parent.
type MergePolicy struct {
	Checks              []CheckPolicy `json:"checks,omitempty" doc:"Checks that run on every branch proposed to this one."`
	When                string        `json:"when,omitempty" doc:"CEL expression that must be true to land a branch. The checks variable maps each check name to an object with passed (bool), state (string), and outputs (map of strings). A check with no result for the branch's current commits has state Pending. Without an expression, every listed check must pass."`
	Landing             string        `json:"landing,omitempty" kube:"enum=FastForward|Squash|Rebase,default=FastForward" doc:"How to land a branch, which must contain the parent's head. FastForward moves the parent to the branch's head. Squash makes one commit with the head's files on top of the parent's head, and Rebase copies each of the branch's commits that isn't a merge onto it. The squashed commit, or the last rebased commit, has the files that the checks saw and builds on the parent head that they saw, so results with filesOnly count for it. When the gate needs other results, the merge controller moves the branch to the new commits for the checks to run on."`
	MaxAutomatedCommits *int32        `json:"maxAutomatedCommits,omitempty" kube:"min=0,max=100,default=5" doc:"Most commits that checks can push to one branch, counted by the Git-K8s-Fixer trailer of the branch's commits that the parent doesn't have. The limit stops two checks that disagree from pushing forever. A squashed commit that the merge controller moves the branch to leaves out the fixes before it, so the count starts again after it. The merge controller doesn't squash the fixes after its own commit again."`
	MaxAgentRuns        *int32        `json:"maxAgentRuns,omitempty" kube:"min=0,max=1000,default=10" doc:"Most agent runs that each agentic check, such as review, can start on one branch. Each new head needs a run, so the limit caps the runs that one branch can start, not what they cost."`
	// DeleteMergedBranches deletes a branch after it lands.
	DeleteMergedBranches bool `json:"deleteMergedBranches,omitempty" doc:"Delete a branch after it lands."`
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

// Landing methods, the values of MergePolicy.Landing.
const (
	FastForward = "FastForward"
	Squash      = "Squash"
	Rebase      = "Rebase"
)

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
// controller owns these objects and writes their spec from the mirror's copy
// of the repository, so don't edit them by hand.
//
// Two controllers write a GitBranch's status, each a different part: the
// core program's results controller writes Status.Checks with the results
// that checks send it, and the merge controller writes the rest.
// Server-side apply keeps their writes apart.
type GitBranch struct {
	kube.Object `kube:"group=git-k8s.imjasonh.com,version=v1alpha1,shortName=gitbr,category=git-k8s"`
	Spec        GitBranchSpec   `json:"spec"`
	Status      GitBranchStatus `json:"status,omitzero"`
}

// GitBranchSpec is a branch as the repository controller last listed it.
type GitBranchSpec struct {
	Repository string       `json:"repository" doc:"Name of the GitRepository in the same namespace."`
	Branch     string       `json:"branch" kube:"column=Branch" doc:"Branch name without refs/heads/."`
	Head       string       `json:"head" kube:"column=Head" doc:"Commit that the branch points to in the mirror."`
	Parent     string       `json:"parent,omitempty" kube:"column=Parent" doc:"Branch that this branch proposes changes to."`
	ParentHead string       `json:"parentHead,omitempty" doc:"Commit that the parent points to in the mirror, listed at the same time as head."`
	Merge      *MergePolicy `json:"merge,omitempty" doc:"The parent's merge policy, copied from the repository rule that matches the parent."`
}

// GitBranchStatus holds check results and the merge controller's state.
type GitBranchStatus struct {
	Checks             map[string]CheckResult `json:"checks,omitempty" kube:"mapType=atomic" doc:"Check results by check name. Checks send their results to the core program, which writes each one to the entry of the check that sent it."`
	State              string                 `json:"state,omitempty" kube:"column=State" doc:"Why the branch has or hasn't landed on its parent, the same as the Merged condition's reason."`
	Queued             *Queued                `json:"queued,omitempty" doc:"The branch's place in its parent's merge queue, while it waits to land."`
	Queue              []string               `json:"queue,omitempty" doc:"Branches in this branch's merge queue, front first. The front branch is the only one that merges this branch in and lands."`
	ObservedGeneration int64                  `json:"observedGeneration,omitempty"`
	Conditions         []kube.Condition       `json:"conditions,omitempty"`
	Diverged           *Divergence            `json:"diverged,omitempty" doc:"How the branch diverged between the mirror and the external repository, set only while it's diverged. The core program writes it."`
}

// Divergence says how a branch diverged between the mirror and the
// external repository: each side changed the branch since they last
// synced, and neither side's head keeps the other side's changes.
type Divergence struct {
	Commit string `json:"commit" doc:"External repository's head of the branch, or empty if the external repository deleted the branch."`
	Ref    string `json:"ref" doc:"Ref in the mirror that holds commit, or empty if commit is."`
	Base   string `json:"base,omitempty" doc:"Head of the branch where the mirror and the external repository last synced, which the mirror keeps under refs/git-k8s/synced/heads/. Empty if they never synced."`
}

// Queued is a branch's place in its parent's merge queue.
type Queued struct {
	Since    time.Time `json:"since" doc:"When the branch joined the queue. Branches that join together land in this order, then by name."`
	Head     string    `json:"head" doc:"Branch head when the merge controller last kept the branch in the queue. A later push that adds a commit without the Git-K8s-Fixer trailer, or that removes commits, takes the branch out of the queue."`
	Position int32     `json:"position,omitempty" kube:"column=Queue" doc:"Place in the parent's queue, from 1 at the front. Unset until the parent's queue includes the branch."`
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
	// for the branch's current commits. Checks can't send it.
	Pending = "Pending"
)

// ResultsAudience is the audience of the service account tokens that checks
// send with their results. The core program's results endpoint accepts
// tokens only for this audience, and its mirror only for MirrorAudience.
// Because it's a constant, generate mounts a token for it in each check's
// Pod, and checks need no permission to create one.
const ResultsAudience = "git-k8s-results"

// Result scopes, which say what a result is for besides the branch head.
const (
	// ScopeHead means that the result is for the branch head with any
	// parent head.
	ScopeHead = "Head"
	// ScopeParent means that the result is for the branch head with only
	// the parent head in its ParentCommit, such as a merge of the parent.
	ScopeParent = "Parent"
	// ScopeChange means that the result is for what the branch head
	// changes on top of its MergeBase, with any parent head, such as an
	// approval of the change. A landing applies the change on top of the
	// parent's head, so the result counts for a landing only when its
	// MergeBase is the parent's head.
	ScopeChange = "Change"
)

// Limits on a result that the core program accepts from a check. The checks
// package shortens messages, output values, and note values to fit.
const (
	MaxMessageLength     = 1024
	MaxOutputs           = 16
	MaxOutputNameLength  = 63
	MaxOutputValueLength = 1024
	MaxNotes             = 32
	MaxNoteNameLength    = 63
	MaxNoteValueLength   = 1024
	// MaxPodNameLength is the longest name that a Pod can have.
	MaxPodNameLength = 253
)

// CheckResult is one check's result for one commit. OpenAPISchema
// describes its fields.
type CheckResult struct {
	Commit       string            `json:"commit"`
	Scope        string            `json:"scope"`
	ParentCommit string            `json:"parentCommit,omitempty"`
	MergeBase    string            `json:"mergeBase,omitempty"`
	State        string            `json:"state"`
	Message      string            `json:"message,omitempty"`
	Outputs      map[string]string `json:"outputs,omitempty"`
	Notes        map[string]string `json:"notes,omitempty"`
	Pod          string            `json:"pod,omitempty"`
	Fix          string            `json:"fix,omitempty"`
	FilesOnly    bool              `json:"filesOnly,omitempty"`
}

// OpenAPISchema returns the schema of a result in the GitBranch
// CustomResourceDefinition. Its rules check the fields that each scope
// needs, as Validate does.
func (CheckResult) OpenAPISchema() map[string]any {
	str := func(doc string) map[string]any {
		s := map[string]any{"type": "string"}
		if doc != "" {
			s["description"] = doc
		}
		return s
	}
	commit := func(doc string) map[string]any {
		s := str(doc)
		s["minLength"] = 1
		return s
	}
	values := func(doc string) map[string]any {
		return map[string]any{"type": "object", "additionalProperties": str(""), "description": doc}
	}
	rule := func(rule, message string) map[string]any {
		return map[string]any{"rule": rule, "message": message}
	}
	scope := str("What the result is for besides the branch head: Head for the branch head with any parent head, Parent for the branch head with the parent head in parentCommit, or Change for what the branch head changes on top of the merge base in mergeBase, with any parent head.")
	// The rules compare scope, so its length bounds their estimated cost,
	// which the API server multiplies by how many entries status.checks
	// can hold.
	scope["enum"] = []any{ScopeHead, ScopeParent, ScopeChange}
	scope["maxLength"] = max(len(ScopeHead), len(ScopeParent), len(ScopeChange))
	state := str("")
	state["enum"] = []any{Running, Passed, Failed, Fixed, Error}
	return map[string]any{
		"type":     "object",
		"required": []string{"commit", "scope", "state"},
		"properties": map[string]any{
			"commit":       commit("Branch head that the result is for."),
			"scope":        scope,
			"parentCommit": commit("Parent head that a result with the scope Parent is for."),
			"mergeBase":    commit("Merge base of the branch head and the parent's head that a result with the scope Change is for. Such a result counts for a landing only when the merge base is the parent's head."),
			"state":        state,
			"message":      str(""),
			"outputs":      values("Values that merge gates can read, such as a risk level."),
			"notes":        values("Other values that the check records, such as what its next run needs or what an agent's run used. Merge gates don't see them."),
			"pod":          str("Pod that does the check's work, such as one that runs tests. While the result is Running, the mirror lets the Pod fetch the repository."),
			"fix":          str("Commit that the check pushed to the branch to fix what it found, for a Fixed result."),
			"filesOnly":    map[string]any{"type": "boolean", "description": "The result also holds for any commit with the same files that builds on the same parent head, because it doesn't depend on the branch's commits, such as their messages or authors. Only such results count for a commit that a squash or rebase landing makes."},
		},
		"x-kubernetes-validations": []any{
			rule("self.scope != 'Head' || !has(self.parentCommit) && !has(self.mergeBase)", "a result with the scope Head has neither parentCommit nor mergeBase"),
			rule("self.scope != 'Parent' || has(self.parentCommit) && !has(self.mergeBase)", "a result with the scope Parent has parentCommit and not mergeBase"),
			rule("self.scope != 'Change' || has(self.mergeBase) && !has(self.parentCommit)", "a result with the scope Change has mergeBase and not parentCommit"),
		},
	}
}

// Fresh reports whether r is for these branch and parent heads. A result
// with a scope that Fresh doesn't know is for no heads, so that a later
// release can add scopes that this one reads as Pending.
func (r *CheckResult) Fresh(head, parentHead string) bool {
	if r == nil || r.Commit != head {
		return false
	}
	switch r.Scope {
	case ScopeHead, ScopeChange:
		return true
	case ScopeParent:
		return r.ParentCommit == parentHead
	}
	return false
}

// Final reports whether r's state won't change for its commits.
func (r *CheckResult) Final() bool {
	return r != nil && (r.State == Passed || r.State == Failed || r.State == Fixed)
}

// Equal reports whether r and o are the same result. A nil result equals
// only nil, and empty outputs or notes equal none.
func (r *CheckResult) Equal(o *CheckResult) bool {
	if r == nil || o == nil {
		return r == o
	}
	return r.Commit == o.Commit && r.Scope == o.Scope && r.ParentCommit == o.ParentCommit && r.MergeBase == o.MergeBase &&
		r.State == o.State && r.Message == o.Message && maps.Equal(r.Outputs, o.Outputs) && maps.Equal(r.Notes, o.Notes) &&
		r.Pod == o.Pod && r.Fix == o.Fix && r.FilesOnly == o.FilesOnly
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
