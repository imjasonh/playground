package main

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
)

// landedFrom matches the parent's head before a landing in a Landed
// event's note, such as "fast-forwarded main from 895bcccc82cc to c/f008
// at 38aa2c8720c2" or "squashed c/f008 at b4ac75650e7b onto main, which
// moved from 2921ea622144 to 5e77e8a2861d".
var landedFrom = regexp.MustCompile(`\bfrom ([0-9a-f]{7,40}) to `)

// verifyResult is what the harness checked after a scenario.
type verifyResult struct {
	MainHead map[string]string `json:"mainHead"`
	Landed   int               `json:"landed"`
	Unlanded []string          `json:"unlanded,omitempty"`
	// MissingChanges lists files that main lacks or has with other
	// contents than a landed branch's change.
	MissingChanges []string `json:"missingChanges,omitempty"`
	Gofmt          []string `json:"gofmt,omitempty"`
	GoTest         []string `json:"goTest,omitempty"`
	// GateViolations lists landings whose recorded check results don't
	// satisfy the merge gate for the landed head.
	GateViolations []string `json:"gateViolations,omitempty"`
	// FixProblems lists failing branches that landed without their fix.
	FixProblems []string `json:"fixProblems,omitempty"`
	// ApprovalProblems lists high-risk branches that landed without an
	// approval of the landed head or of a commit whose change it makes.
	ApprovalProblems []string `json:"approvalProblems,omitempty"`
	// DirectApprovals counts high-risk branches that landed at the commit
	// that the harness approved, and CarriedApprovals those that landed at
	// another commit that makes the approved commit's change.
	DirectApprovals  int `json:"directApprovals"`
	CarriedApprovals int `json:"carriedApprovals"`
	// FixerTrailers counts the commits on main by their Git-K8s-Fixer
	// trailer, and PushedFixes counts every commit that a check pushed, from
	// its PushedFix event, by trailer.
	FixerTrailers   map[string]int `json:"fixerTrailers"`
	PushedFixes     map[string]int `json:"pushedFixes"`
	TrailerProblems []string       `json:"trailerProblems,omitempty"`
	Checked         []string       `json:"checked"`
}

func (v *verifyResult) err() error {
	var errs []error
	for name, list := range map[string][]string{
		"unlanded branches": v.Unlanded, "missing changes": v.MissingChanges, "gofmt": v.Gofmt, "go test": v.GoTest,
		"gate violations": v.GateViolations, "fix problems": v.FixProblems, "approval problems": v.ApprovalProblems,
		"trailer problems": v.TrailerProblems,
	} {
		if len(list) > 0 {
			errs = append(errs, fmt.Errorf("%s: %s", name, strings.Join(list, "; ")))
		}
	}
	return errors.Join(errs...)
}

func (rn *runner) verify(ctx context.Context) *verifyResult {
	v := &verifyResult{MainHead: map[string]string{}, FixerTrailers: map[string]int{}, PushedFixes: map[string]int{}}
	if rn.r != nil {
		rn.r.flush()
	}
	run, err := loadRun(rn.out)
	if err != nil {
		v.Unlanded = append(v.Unlanded, "can't read the log: "+err.Error())
		return v
	}
	landings := map[string]*branchRec{}
	landedAt := map[string]time.Time{}
	parentAt := map[string]string{}
	for _, rc := range run.recs {
		switch rc.Kind {
		case "branch":
			b := rc.branch
			key := b.Repo + "/" + b.Branch
			if b.Landed != nil && b.Landed.Reason == "Landed" && landings[key] == nil {
				landings[key] = b
			}
		case "event":
			if e := rc.event; e.Reason == "Landed" {
				if br := rn.byObj[e.Object]; br != nil {
					key := br.plan.Repo + "/" + br.plan.Name
					landedAt[key] = e.EventTime
					if m := landedFrom.FindStringSubmatch(e.Note); m != nil {
						parentAt[key] = m[1]
					}
				}
			}
		}
	}
	for _, rp := range rn.plan.Repos {
		g := rn.repos[rp.Name]
		heads, err := g.fetch()
		if err != nil {
			v.MissingChanges = append(v.MissingChanges, rp.Name+": "+err.Error())
			continue
		}
		main := heads["main"]
		v.MainHead[rp.Name] = main
		rn.verifyTree(ctx, v, rp, g, main)
		rn.verifyTrailers(v, rp, g, main, run)
		// Each line ends with the check that pushed the commit, if one did.
		if graph, err := g.git(nil, "log", "--graph", "--format=%h %s %(trailers:key=Git-K8s-Fixer,valueonly,separator=%x2c)", main); err == nil {
			_ = os.WriteFile(filepath.Join(rn.out, "graph-"+rp.Name+".txt"), []byte(graph+"\n"), 0o644)
		}
	}
	for _, br := range rn.runs {
		key := br.plan.Repo + "/" + br.plan.Name
		at, ok := landedAt[key]
		if !ok {
			v.Unlanded = append(v.Unlanded, key)
			continue
		}
		v.Landed++
		lr := landings[key]
		if lr == nil {
			v.GateViolations = append(v.GateViolations, key+": no Branch object record with Landed reason Landed")
			continue
		}
		if problems := gateProblems(lr, rn.plan.repo(br.plan.Repo).Gotest, parentAt[key]); len(problems) > 0 {
			v.GateViolations = append(v.GateViolations, fmt.Sprintf("%s at %s: %s", key, short(lr.Head), strings.Join(problems, ", ")))
		}
		switch br.plan.Kind {
		case kindFailing:
			fix := ""
			for _, a := range run.actions {
				if a.Action == "fix" && a.Repo == br.plan.Repo && a.Branch == br.plan.Name && a.Err == "" {
					fix = a.Head
				}
			}
			g := rn.repos[br.plan.Repo]
			if fix == "" {
				v.FixProblems = append(v.FixProblems, key+" landed, but the harness never pushed its fix")
			} else if _, err := g.git(nil, "merge-base", "--is-ancestor", fix, lr.Head); err != nil {
				v.FixProblems = append(v.FixProblems, fmt.Sprintf("%s landed at %s, which doesn't contain its fix %s", key, short(lr.Head), short(fix)))
			}
		case kindBigRisk, kindModRisk:
			approved := map[string]bool{}
			for _, a := range run.actions {
				if a.Action == "approve" && a.Repo == br.plan.Repo && a.Branch == br.plan.Name && a.Err == "" && a.Start.Before(at) {
					approved[a.Head] = true
				}
			}
			carried, problem := landedApproval(rn.repos[br.plan.Repo], lr, approved, parentAt[key])
			switch {
			case problem != "":
				v.ApprovalProblems = append(v.ApprovalProblems, fmt.Sprintf("%s landed at %s with approval %q: %s", key, short(lr.Head), lr.Approve, problem))
			case carried:
				v.CarriedApprovals++
			default:
				v.DirectApprovals++
			}
		}
	}
	v.Checked = []string{
		"every planned branch landed",
		"main's tree has each landed branch's files with the expected contents, including fixed tests, gofmt fixes, and resolved conflicts",
		"gofmt -l and go test ./... pass on main",
		"at each landing, the recorded results of the gate's checks passed for the landed head and parent head",
		"each failing branch landed with its fix, and each high-risk branch with an approval made before the landing, of the landed head or of a commit whose change merge-tree applies to the parent's head to make the landed head's tree",
		"at each landing, every result that names a merge base names the parent's head",
		"every commit that a check pushed has a Git-K8s-Fixer trailer that names the check",
	}
	return v
}

// landedApproval checks the approval that a high-risk branch landed with,
// from lr, its Branch object record from the landing. approved holds the heads
// that the reviewer approved before the landing, and parent is the parent's
// head that the branch landed on. The approval must name the landed head,
// or name in full an approved head whose change the landed head makes on
// top of parent, as sameChange checks. carried reports the second case.
// landedApproval returns "" for the problem if the approval holds.
func landedApproval(g *gitRepo, lr *branchRec, approved map[string]bool, parent string) (carried bool, problem string) {
	switch {
	case len(lr.Approve) >= 7 && strings.HasPrefix(lr.Head, lr.Approve) && approved[lr.Head]:
		return false, ""
	case len(lr.Approve) == 40 && approved[lr.Approve]:
		return true, sameChange(g, lr.Approve, lr.Head, parent)
	}
	return false, "the approval doesn't name the landed head, or in full a head that the reviewer approved before the landing"
}

// sameChange checks, without git-k8s's code, that the commit landed has the
// change of the commit approved on top of parent, the parent's head that the
// branch landed on. It applies what approved changes on top of its merge
// base with parent to parent with git merge-tree, and compares the result
// with landed's tree. It returns "" if they match, and the problem
// otherwise.
func sameChange(g *gitRepo, approved, landed, parent string) string {
	if parent == "" {
		return "no parent head from the Landed event"
	}
	full, err := g.git(nil, "rev-parse", "--verify", parent+"^{commit}")
	if err != nil {
		return err.Error()
	}
	bases, err := g.git(nil, "merge-base", "--all", full, approved)
	if err != nil {
		return err.Error()
	}
	if strings.Contains(bases, "\n") || bases == "" {
		return fmt.Sprintf("%s and %s don't have one merge base: %q", short(full), short(approved), bases)
	}
	tree, err := g.git(nil, "merge-tree", "--write-tree", "--merge-base="+bases, full, approved)
	if err != nil {
		return err.Error()
	}
	want, err := g.git(nil, "rev-parse", "--verify", landed+"^{tree}")
	if err != nil {
		return err.Error()
	}
	if tree != want {
		return fmt.Sprintf("%s's change on top of %s has tree %s, but the landed head has %s", short(approved), short(full), short(tree), short(want))
	}
	return ""
}

// gateProblems checks a Branch object record from a landing against the
// scenario's merge gate. parent is the parent's head that the branch landed
// on, from the Landed event, or "" to use the record's. The repository
// controller can move the record's parent head to the landed commit before
// the watch sees the Landed status.
func gateProblems(b *branchRec, gotest bool, parent string) []string {
	var problems []string
	if parent == "" {
		parent = b.ParentHead
	}
	need := []string{"base", "gofmt", "risk"}
	if gotest {
		need = append(need, "gotest")
	}
	for _, name := range need {
		c, ok := b.Checks[name]
		switch {
		case !ok:
			problems = append(problems, name+" has no result")
		case c.Commit != b.Head:
			problems = append(problems, fmt.Sprintf("%s is for %s", name, short(c.Commit)))
		case c.State != "Passed":
			problems = append(problems, name+" is "+c.State)
		}
	}
	if c := b.Checks["base"]; c.Outputs["behind"] == "true" || parent == "" || !strings.HasPrefix(c.ParentCommit, parent) {
		problems = append(problems, fmt.Sprintf("base ran against %s, not the parent's head %s (behind=%s)", short(c.ParentCommit), short(parent), c.Outputs["behind"]))
	}
	if c := b.Checks["risk"]; c.ParentCommit != "" && !strings.HasPrefix(c.ParentCommit, parent) {
		problems = append(problems, fmt.Sprintf("risk ran against %s, not the parent's head %s", short(c.ParentCommit), short(parent)))
	}
	for _, name := range []string{"base", "gofmt", "risk", "approval", "gotest"} {
		if c, ok := b.Checks[name]; ok && c.MergeBase != "" && !strings.HasPrefix(c.MergeBase, parent) {
			problems = append(problems, fmt.Sprintf("%s holds for the change on top of %s, not on top of the parent's head %s", name, short(c.MergeBase), short(parent)))
		}
	}
	if level := b.Checks["risk"].Outputs["level"]; level != "low" {
		if a := b.Checks["approval"]; a.State != "Passed" || a.Commit != b.Head {
			problems = append(problems, fmt.Sprintf("risk is %q and approval is %s for %s", level, a.State, short(a.Commit)))
		}
	}
	return problems
}

// verifyTree checks out main and checks that it has every landed change,
// is formatted, and passes its tests.
func (rn *runner) verifyTree(ctx context.Context, v *verifyResult, rp repoPlan, g *gitRepo, main string) {
	dir := filepath.Join(rn.out, "main-"+rp.Name)
	_ = os.RemoveAll(dir)
	if _, err := g.git(nil, "worktree", "add", "-q", "-f", "--detach", dir, main); err != nil {
		v.MissingChanges = append(v.MissingChanges, rp.Name+": "+err.Error())
		return
	}
	defer func() {
		_, _ = g.git(nil, "worktree", "remove", "--force", dir)
	}()
	pairs := map[int][]string{}
	for _, b := range rn.plan.Branches {
		if b.Repo == rp.Name && b.Kind == kindConflict {
			pairs[b.Pair] = append(pairs[b.Pair], b.Name)
		}
	}
	for _, b := range rn.plan.Branches {
		if b.Repo != rp.Name {
			continue
		}
		want := expectedFiles(b)
		if b.Kind == kindConflict {
			owners := pairs[b.Pair]
			sort.Strings(owners)
			want[conflictFile(b.Pair)] = conflictSource(b.Pair, strings.Join(owners, "+"))
		}
		for name, content := range want {
			got, err := os.ReadFile(filepath.Join(dir, name))
			if err != nil || strings.TrimSpace(string(got)) != strings.TrimSpace(content) {
				v.MissingChanges = append(v.MissingChanges, fmt.Sprintf("%s: %s from %s", rp.Name, name, b.Name))
			}
		}
	}
	out, err := exec.CommandContext(ctx, "gofmt", "-l", dir).CombinedOutput()
	if err != nil || strings.TrimSpace(string(out)) != "" {
		v.Gofmt = append(v.Gofmt, fmt.Sprintf("%s: %v %s", rp.Name, err, strings.TrimSpace(string(out))))
	}
	tctx, cancel := context.WithTimeout(ctx, 5*time.Minute)
	defer cancel()
	cmd := exec.CommandContext(tctx, "go", "test", "./...")
	cmd.Dir = dir
	cmd.Env = append(os.Environ(), "GOPROXY=http://127.0.0.1:"+rn.env["MOD_PORT"], "GOSUMDB=off", "GOFLAGS=-mod=mod",
		"GOMODCACHE="+filepath.Join(rn.env["STATE"], "gomodcache"), "GOCACHE="+filepath.Join(rn.env["STATE"], "gocache"),
		"GOTOOLCHAIN=local", "GOWORK=off", "NO_PROXY=127.0.0.1,localhost")
	if out, err := cmd.CombinedOutput(); err != nil {
		lines := strings.Split(strings.TrimSpace(string(out)), "\n")
		v.GoTest = append(v.GoTest, fmt.Sprintf("%s: %v: %s", rp.Name, err, strings.Join(lines[max(0, len(lines)-10):], " | ")))
	}
}

// verifyTrailers counts fixer trailers on main, and checks that the commit
// of every PushedFix event has one.
func (rn *runner) verifyTrailers(v *verifyResult, rp repoPlan, g *gitRepo, main string, run *runData) {
	out, err := g.git(nil, "log", "--format=%H%x1f%ae%x1f%s%x1f%(trailers:key=Git-K8s-Fixer,valueonly,separator=%x2c)%x1e", main)
	if err != nil {
		v.TrailerProblems = append(v.TrailerProblems, err.Error())
		return
	}
	for entry := range strings.SplitSeq(out, "\x1e") {
		f := strings.Split(strings.TrimSpace(entry), "\x1f")
		if len(f) != 4 {
			continue
		}
		trailer := strings.TrimSpace(f[3])
		if trailer != "" {
			v.FixerTrailers[trailer]++
		} else if strings.HasPrefix(f[2], "Merge main into") && !strings.HasSuffix(f[1], "@example.com") {
			v.TrailerProblems = append(v.TrailerProblems, fmt.Sprintf("%s: %s %q by %s has no Git-K8s-Fixer trailer", rp.Name, short(f[0]), f[2], f[1]))
		}
	}
	bare := filepath.Join(rn.env["STATE"], "repos", repoKey(rn.plan.NS, rp.Name)+".git")
	for _, rc := range run.recs {
		if rc.Kind != "event" || rc.event.Reason != "PushedFix" || rc.event.Type != "ADDED" {
			continue
		}
		br := rn.byObj[rc.event.Object]
		if br == nil || br.plan.Repo != rp.Name {
			continue
		}
		sha, _, _ := strings.Cut(strings.TrimPrefix(rc.event.Note, "pushed "), " ")
		cmd := exec.Command("git", "-C", bare, "log", "-1", "--format=%(trailers:key=Git-K8s-Fixer,valueonly)", sha)
		cmd.Env = append(os.Environ(), "GIT_CONFIG_GLOBAL=/dev/null", "GIT_CONFIG_NOSYSTEM=1")
		b, err := cmd.Output()
		trailer := strings.TrimSpace(string(b))
		switch {
		case err != nil:
			v.TrailerProblems = append(v.TrailerProblems, fmt.Sprintf("%s: can't read %s from %s's PushedFix event", rp.Name, sha, br.plan.Name))
		case trailer == "":
			v.TrailerProblems = append(v.TrailerProblems, fmt.Sprintf("%s: %s, which a check pushed to %s, has no Git-K8s-Fixer trailer", rp.Name, sha, br.plan.Name))
		default:
			v.PushedFixes[trailer]++
		}
	}
}

// reverify checks a finished run again, from its plan, its working copies,
// its records, and the git server, and writes its verify.json and summary
// again.
func reverify(env map[string]string, out string) error {
	data, err := os.ReadFile(filepath.Join(out, "plan.json"))
	if err != nil {
		return err
	}
	var p plan
	if err := json.Unmarshal(data, &p); err != nil {
		return err
	}
	rn := &runner{env: env, plan: p, out: out, repos: map[string]*gitRepo{}, byObj: map[string]*branchRun{}}
	for _, rp := range p.Repos {
		rn.repos[rp.Name] = &gitRepo{dir: filepath.Join(out, "work", rp.Name), url: env["HOST_URL"] + "/" + repoKey(p.NS, rp.Name) + ".git"}
	}
	for _, bp := range p.Branches {
		br := &branchRun{plan: bp, obj: gitk8s.BranchObjectName(bp.Repo, bp.Name)}
		rn.runs = append(rn.runs, br)
		rn.byObj[br.obj] = br
	}
	v := rn.verify(context.Background())
	if err := saveJSON(filepath.Join(out, "verify.json"), v); err != nil {
		return err
	}
	return errors.Join(analyze(out), v.err())
}
