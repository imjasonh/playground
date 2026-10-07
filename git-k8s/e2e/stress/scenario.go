package main

import (
	"context"
	"crypto/rand"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	mrand "math/rand/v2"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"sort"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
)

// Branch kinds, which decide what a branch's first push contains and what
// its developer does afterward.
const (
	// kindClean adds a package and its test.
	kindClean = "clean"
	// kindUnformatted isn't gofmt-formatted, so the gofmt check pushes a fix.
	kindUnformatted = "unformatted"
	// kindFailing has a failing test. Its developer pushes a fix after the
	// gotest check fails.
	kindFailing = "failing"
	// kindConflict changes the same line as the other branch of its pair.
	// After one lands, the other's developer merges main and resolves the
	// conflict.
	kindConflict = "conflict"
	// kindBigRisk adds more than 200 lines, and kindModRisk requires a new
	// module. Both are high risk, so a person approves them.
	kindBigRisk = "bigrisk"
	kindModRisk = "modrisk"
	// kindMulti makes three commits.
	kindMulti = "multi"
)

type branchPlan struct {
	Repo string `json:"repo"`
	Name string `json:"name"`
	ID   string `json:"id"`
	Kind string `json:"kind"`
	Pair int    `json:"pair,omitempty"`
}

type repoPlan struct {
	Name    string `json:"name"`
	Landing string `json:"landing,omitempty"`
	Gotest  bool   `json:"gotest"`
	// Poll is the GitRepository's pollInterval, or "" for the default.
	Poll string `json:"poll,omitempty"`
}

type plan struct {
	Scenario string       `json:"scenario"`
	NS       string       `json:"namespace"`
	Repos    []repoPlan   `json:"repos"`
	Branches []branchPlan `json:"branches"`
	// ApproveDelay is how long the harness waits to approve a high-risk
	// head after the risk check reports it.
	ApproveDelay string `json:"approveDelay"`
	// Stagger is the time between first pushes; zero pushes them all at
	// once.
	Stagger string `json:"stagger,omitempty"`
	Warmup  bool   `json:"warmup"`
	Timeout string `json:"timeout"`
}

func (p *plan) repo(name string) repoPlan {
	for _, r := range p.Repos {
		if r.Name == name {
			return r
		}
	}
	return repoPlan{}
}

// repoKey is the name of a GitRepository's repository on the git server.
func repoKey(ns, repo string) string { return ns + "-" + repo }

func buildPlan(scenario string, n, repos int, poll string) (plan, error) {
	suffix := make([]byte, 2)
	_, _ = rand.Read(suffix)
	p := plan{Scenario: scenario, NS: "stress-" + scenario + "-" + hex.EncodeToString(suffix), ApproveDelay: "15s", Warmup: true, Timeout: "45m"}
	id := func(i int) string { return fmt.Sprintf("f%03d", i) }
	add := func(repo string, i int, kind string) {
		p.Branches = append(p.Branches, branchPlan{Repo: repo, Name: "c/" + id(i), ID: id(i), Kind: kind})
	}
	repoNames := func(count int) []string {
		var names []string
		for i := range count {
			names = append(names, string(rune('a'+i)))
		}
		return names
	}
	switch scenario {
	case "clean", "nogotest", "big":
		if n == 0 {
			n = 20
			if scenario == "big" {
				n = 100
			}
		}
		if repos == 0 {
			repos = 1
		}
		names := []string{"app"}
		if repos > 1 {
			names = repoNames(repos)
		}
		for _, name := range names {
			p.Repos = append(p.Repos, repoPlan{Name: name, Gotest: scenario != "nogotest", Poll: poll})
		}
		for i := 1; i <= n; i++ {
			for _, name := range names {
				add(name, i, kindClean)
			}
		}
		if scenario == "big" {
			p.Timeout = "120m"
		}
	case "mixed":
		if n == 0 {
			n = 24
		}
		p.Repos = []repoPlan{{Name: "app", Gotest: true, Poll: poll}}
		var kinds []string
		pairs := 2
		for range pairs * 2 {
			kinds = append(kinds, kindConflict)
		}
		kinds = append(kinds, kindBigRisk, kindModRisk)
		for range max(2, n/10) {
			kinds = append(kinds, kindFailing)
		}
		for range (n*3 + 5) / 10 {
			kinds = append(kinds, kindUnformatted)
		}
		for len(kinds) < n {
			kinds = append(kinds, kindClean)
		}
		r := mrand.New(mrand.NewPCG(1, 2))
		r.Shuffle(len(kinds), func(i, j int) { kinds[i], kinds[j] = kinds[j], kinds[i] })
		pair := map[int]int{}
		for i, kind := range kinds {
			add("app", i+1, kind)
			if kind == kindConflict {
				// Fill pairs in order, two branches each.
				k := 1
				for pair[k] == 2 {
					k++
				}
				pair[k]++
				p.Branches[len(p.Branches)-1].Pair = k
			}
		}
	case "landing":
		if n == 0 {
			n = 10
		}
		p.Repos = []repoPlan{{Name: "rebase", Landing: "Rebase", Gotest: true, Poll: poll}, {Name: "squash", Landing: "Squash", Gotest: true, Poll: poll}}
		for i := 1; i <= n; i++ {
			add("rebase", i, kindMulti)
			add("squash", i, kindMulti)
		}
	case "parallel":
		if n == 0 {
			n = 10
		}
		if repos == 0 {
			repos = 4
		}
		for _, name := range repoNames(repos) {
			p.Repos = append(p.Repos, repoPlan{Name: name, Gotest: true, Poll: poll})
		}
		for i := 1; i <= n; i++ {
			for _, r := range p.Repos {
				add(r.Name, i, kindClean)
			}
		}
	case "poll30":
		if n == 0 {
			n = 8
		}
		// The GitRepository leaves pollInterval out, so it polls every 30
		// seconds. Pushes come 7 seconds apart, so they land at different
		// points in the poll cycle.
		p.Repos = []repoPlan{{Name: "app", Gotest: false}}
		p.Stagger = "7s"
		for i := 1; i <= n; i++ {
			add("app", i, kindClean)
		}
	default:
		return p, fmt.Errorf("unknown scenario %q", scenario)
	}
	return p, nil
}

// branchRun is the harness's state for one branch.
type branchRun struct {
	plan     branchPlan
	obj      string
	busy     atomic.Bool
	head     string
	fixed    bool
	resolved map[string]bool
	approved map[string]bool
	// approvalHead is the high-risk head that the harness approves at
	// approvalDue.
	approvalHead string
	approvalDue  time.Time
	landed       bool
}

// actionRec is something that the harness did, as a developer or reviewer.
type actionRec struct {
	Action string    `json:"action"`
	Repo   string    `json:"repo"`
	Branch string    `json:"branch"`
	Head   string    `json:"head,omitempty"`
	Start  time.Time `json:"start"`
	Err    string    `json:"err,omitempty"`
	Note   string    `json:"note,omitempty"`
}

type runner struct {
	env      map[string]string
	k        *kubeClient
	r        *recorder
	w        *world
	plan     plan
	out      string
	repos    map[string]*gitRepo
	runs     []*branchRun
	byObj    map[string]*branchRun
	user     string
	greetSum string
	start    time.Time
	// mu guards the fixed, resolved, and approved fields of runs, which
	// actions write in their own goroutines.
	mu sync.Mutex
}

func (rn *runner) note(format string, args ...any) {
	msg := fmt.Sprintf(format, args...)
	logf("%s", msg)
	rn.r.add("note", time.Now(), map[string]string{"msg": msg})
}

func (rn *runner) action(a actionRec) {
	rn.r.add("action", time.Now(), a)
}

func runScenario(ctx context.Context, env map[string]string, p plan, out string) error {
	if err := os.MkdirAll(out, 0o755); err != nil {
		return err
	}
	k, err := newKubeClient(env["CONTEXT"])
	if err != nil {
		return err
	}
	r, err := newRecorder(filepath.Join(out, "log.jsonl"))
	if err != nil {
		return err
	}
	defer r.close()
	rn := &runner{env: env, k: k, r: r, w: newWorld(p.NS), plan: p, out: out, repos: map[string]*gitRepo{}, byObj: map[string]*branchRun{}, start: time.Now()}
	if err := saveJSON(filepath.Join(out, "plan.json"), p); err != nil {
		return err
	}
	if rn.user, err = k.username(ctx); err != nil {
		return err
	}
	if rn.greetSum, err = greetSum(env); err != nil {
		return err
	}

	recCtx, stop := context.WithCancel(ctx)
	defer stop()
	startWatchers(recCtx, k, r, rn.w)
	if node, err := nodeCgroup(env["CLUSTER"]); err != nil {
		rn.note("not recording CPU: %v", err)
	} else {
		go sampleCPU(recCtx, r, rn.w, node)
	}
	go scrapeMetrics(recCtx, k, r, 10*time.Second)
	var keys []string
	for _, rp := range p.Repos {
		keys = append(keys, repoKey(p.NS, rp.Name))
	}
	go pollRefs(recCtx, r, rn.w, filepath.Join(env["STATE"], "repos"), func() []string { return keys }, []string{"main"})
	go tick(recCtx, r, rn.w)
	go func() {
		for {
			select {
			case <-recCtx.Done():
				return
			case <-time.After(time.Second):
				r.flush()
			}
		}
	}()

	timeout, _ := time.ParseDuration(p.Timeout)
	rn.note("scenario %s in namespace %s: %d repositories, %d branches", p.Scenario, p.NS, len(p.Repos), len(p.Branches))
	if err := rn.setup(ctx); err != nil {
		return err
	}
	if p.Warmup {
		if err := rn.warmup(ctx); err != nil {
			return err
		}
	}
	if err := rn.prepare(); err != nil {
		return err
	}
	rn.note("burst start")
	scenarioErr := rn.burst(ctx, time.Now().Add(timeout))
	if scenarioErr != nil {
		rn.note("scenario failed: %v", scenarioErr)
	}
	rn.note("burst end")
	rn.settle(ctx)
	scrapeOnce(ctx, k, r)
	v := rn.verify(ctx)
	if err := saveJSON(filepath.Join(out, "verify.json"), v); err != nil {
		return err
	}
	rn.dumpState(ctx)
	stop()
	r.flush()
	return errors.Join(scenarioErr, v.err())
}

func saveJSON(path string, v any) error {
	b, err := json.MarshalIndent(v, "", "  ")
	if err != nil {
		return err
	}
	return os.WriteFile(path, append(b, '\n'), 0o644)
}

// greetSum returns the go.sum lines for example.com/greet v1.0.0, which the
// module proxy that setup.sh starts serves.
func greetSum(env map[string]string) (string, error) {
	cmd := exec.Command("go", "mod", "download", "-json", "example.com/greet@v1.0.0")
	cmd.Dir = os.TempDir()
	cmd.Env = append(os.Environ(), "GOPROXY=http://127.0.0.1:"+env["MOD_PORT"], "GOSUMDB=off", "GOFLAGS=-modcacherw",
		"GOMODCACHE="+filepath.Join(env["STATE"], "gomodcache"), "GOTOOLCHAIN=local", "NO_PROXY=127.0.0.1,localhost")
	out, err := cmd.Output()
	if err != nil {
		return "", fmt.Errorf("downloading example.com/greet from the module proxy: %w", err)
	}
	var m struct{ Sum, GoModSum string }
	if err := json.Unmarshal(out, &m); err != nil {
		return "", err
	}
	return fmt.Sprintf("example.com/greet v1.0.0 %s\nexample.com/greet v1.0.0/go.mod %s\n", m.Sum, m.GoModSum), nil
}

// nodeCgroup returns the cgroup directory of the kind cluster's node, which
// Docker on Linux with cgroup v2 puts in one of two places, by its cgroup
// driver.
func nodeCgroup(cluster string) (string, error) {
	out, err := exec.Command("docker", "inspect", "-f", "{{.Id}}", cluster+"-control-plane").Output()
	if err != nil {
		return "", fmt.Errorf("inspecting the kind node: %w", err)
	}
	id := strings.TrimSpace(string(out))
	for _, dir := range []string{"/sys/fs/cgroup/docker/" + id, "/sys/fs/cgroup/system.slice/docker-" + id + ".scope"} {
		if _, err := os.Stat(filepath.Join(dir, "cpu.stat")); err == nil {
			return dir, nil
		}
	}
	return "", fmt.Errorf("can't find the cgroup v2 directory of the kind node's container %s", id)
}

func (rn *runner) branchPath(name string) string {
	return "/apis/git-k8s.imjasonh.com/v1alpha1/namespaces/" + rn.plan.NS + "/gitbranches/" + name
}

// setup creates the namespace, the credentials, each repository on the git
// server, and its GitRepository.
func (rn *runner) setup(ctx context.Context) error {
	ns := rn.plan.NS
	if err := rn.k.apply(ctx, "/api/v1/namespaces/"+ns, map[string]any{
		"apiVersion": "v1", "kind": "Namespace",
		"metadata": map[string]any{"name": ns, "labels": map[string]string{
			"git-k8s.imjasonh.com/check-pods":    "true",
			"pod-security.kubernetes.io/enforce": "restricted",
		}},
	}); err != nil {
		return fmt.Errorf("creating namespace %s: %w", ns, err)
	}
	if err := rn.k.apply(ctx, "/api/v1/namespaces/"+ns+"/secrets/creds", map[string]any{
		"apiVersion": "v1", "kind": "Secret", "type": "kubernetes.io/basic-auth",
		"metadata":   map[string]any{"name": "creds", "namespace": ns},
		"stringData": map[string]string{"username": "git-k8s", "password": rn.env["PASSWORD"]},
	}); err != nil {
		return err
	}
	for _, rp := range rn.plan.Repos {
		key := repoKey(ns, rp.Name)
		if err := os.RemoveAll(filepath.Join(rn.env["STATE"], "repos", key+".git")); err != nil {
			return err
		}
		g, err := initRepo(filepath.Join(rn.out, "work", rp.Name), rn.env["HOST_URL"]+"/"+key+".git", baseFiles())
		if err != nil {
			return err
		}
		rn.repos[rp.Name] = g
		if err := rn.k.apply(ctx, "/apis/git-k8s.imjasonh.com/v1alpha1/namespaces/"+ns+"/gitrepositories/"+rp.Name,
			gitRepository(ns, rp, rn.env["CLUSTER_URL"]+"/"+key+".git")); err != nil {
			return fmt.Errorf("applying GitRepository %s: %w", rp.Name, err)
		}
	}
	deadline := time.Now().Add(3 * time.Minute)
	for _, rp := range rn.plan.Repos {
		for rn.w.branch(ns, rp.Name, "main") == nil {
			if time.Now().After(deadline) {
				return fmt.Errorf("GitRepository %s didn't list main within 3 minutes", rp.Name)
			}
			sleep(ctx, 200*time.Millisecond)
		}
	}
	rn.note("repositories ready")
	return nil
}

func gitRepository(ns string, rp repoPlan, url string) map[string]any {
	checks := []map[string]any{{"name": "base", "mayPush": true}, {"name": "gofmt", "mayPush": true}, {"name": "risk"}, {"name": "approval"}}
	when := `checks.base.passed && checks.gofmt.passed && (checks.risk.outputs.level == "low" || checks.approval.passed)`
	if rp.Gotest {
		checks = append(checks, map[string]any{"name": "gotest"})
		when = `checks.base.passed && checks.gofmt.passed && checks.gotest.passed && (checks.risk.outputs.level == "low" || checks.approval.passed)`
	}
	merge := map[string]any{"checks": checks, "when": when, "deleteLandedBranches": true}
	if rp.Landing != "" {
		merge["landing"] = rp.Landing
	}
	spec := map[string]any{
		"url":       url,
		"secretRef": map[string]string{"name": "creds"},
		"branches": []map[string]any{
			{"match": "main", "merge": merge},
			{"match": "c/**", "parent": "main"},
		},
	}
	if rp.Poll != "" {
		spec["pollInterval"] = rp.Poll
	}
	return map[string]any{
		"apiVersion": "git-k8s.imjasonh.com/v1alpha1", "kind": "GitRepository",
		"metadata": map[string]any{"name": rp.Name, "namespace": ns},
		"spec":     spec,
	}
}

// warmup lands one clean branch in each repository and waits for it, so
// the burst doesn't measure go-cache's first build of a repository.
func (rn *runner) warmup(ctx context.Context) error {
	start := time.Now()
	var warm []*branchRun
	for _, rp := range rn.plan.Repos {
		br := &branchRun{plan: branchPlan{Repo: rp.Name, Name: "c/w00", ID: "w00", Kind: kindClean}}
		br.obj = gitk8s.BranchObjectName(rp.Name, br.plan.Name)
		g := rn.repos[rp.Name]
		if _, err := g.git(nil, "checkout", "-q", "-B", br.plan.Name, "main"); err != nil {
			return err
		}
		for _, c := range branchCommits(br.plan, rn.greetSum) {
			if err := g.write(c.files); err != nil {
				return err
			}
			if _, err := g.commit(author{"dev w00", "w00@example.com"}, c.message); err != nil {
				return err
			}
		}
		if err := g.push(br.plan.Name); err != nil {
			return err
		}
		rn.action(actionRec{Action: "warmup", Repo: rp.Name, Branch: br.plan.Name, Start: time.Now()})
		warm = append(warm, br)
	}
	rn.note("warm-up pushed")
	idx := 0
	for {
		evs, next := rn.w.eventsSince(idx)
		idx = next
		for _, e := range evs {
			for _, br := range warm {
				if e.Reason == "Landed" && e.Object == br.obj && e.NS == rn.plan.NS {
					br.landed = true
				}
			}
		}
		if !slices.ContainsFunc(warm, func(br *branchRun) bool { return !br.landed }) {
			break
		}
		if time.Since(start) > 10*time.Minute {
			return errors.New("the warm-up branches didn't land within 10 minutes")
		}
		select {
		case <-ctx.Done():
			return ctx.Err()
		case <-rn.w.changed:
		case <-time.After(250 * time.Millisecond):
		}
	}
	rn.note("warm-up landed after %s", time.Since(start).Round(time.Millisecond))
	// Let the landing reach the git server and the GitBranches go away.
	rn.waitQuiet(ctx, 60*time.Second)
	return nil
}

// waitQuiet waits until each repository's main on the git server matches
// main's GitBranch and only main's GitBranch is left, for up to max.
func (rn *runner) waitQuiet(ctx context.Context, max time.Duration) {
	deadline := time.Now().Add(max)
	for time.Now().Before(deadline) {
		quiet := true
		rn.w.mu.Lock()
		for _, b := range rn.w.branches {
			if b.Parent != "" {
				quiet = false
			} else if rn.w.ext[repoKey(b.NS, b.Repo)+"/main"] != b.Head {
				quiet = false
			}
		}
		rn.w.mu.Unlock()
		if quiet {
			return
		}
		sleep(ctx, 250*time.Millisecond)
	}
	rn.note("still not quiet after %s", max)
}

// prepare makes each branch's first commits on top of main, without
// pushing them.
func (rn *runner) prepare() error {
	for _, rp := range rn.plan.Repos {
		if _, err := rn.repos[rp.Name].fetch(); err != nil {
			return err
		}
	}
	for _, bp := range rn.plan.Branches {
		g := rn.repos[bp.Repo]
		br := &branchRun{plan: bp, obj: gitk8s.BranchObjectName(bp.Repo, bp.Name), resolved: map[string]bool{}, approved: map[string]bool{}}
		if _, err := g.git(nil, "checkout", "-q", "-B", bp.Name, "refs/remotes/origin/main"); err != nil {
			return err
		}
		dev := author{"dev " + bp.ID, bp.ID + "@example.com"}
		for _, c := range branchCommits(bp, rn.greetSum) {
			if err := g.write(c.files); err != nil {
				return err
			}
			if _, err := g.commit(dev, c.message); err != nil {
				return err
			}
		}
		head, err := g.git(nil, "rev-parse", "HEAD")
		if err != nil {
			return err
		}
		br.head = head
		rn.runs = append(rn.runs, br)
		rn.byObj[br.obj] = br
	}
	return nil
}

// burst pushes every branch, then plays its developer and reviewer until
// every branch lands, deadline passes, or no branch lands for 10 minutes.
func (rn *runner) burst(ctx context.Context, deadline time.Time) error {
	stagger, _ := time.ParseDuration(rn.plan.Stagger)
	go func() {
		for i, br := range rn.runs {
			if i > 0 && stagger > 0 {
				sleep(ctx, stagger)
			}
			g := rn.repos[br.plan.Repo]
			start := time.Now()
			g.mu.Lock()
			_, err := g.git(nil, "push", "-q", g.url, "refs/heads/"+br.plan.Name+":refs/heads/"+br.plan.Name)
			g.mu.Unlock()
			a := actionRec{Action: "push", Repo: br.plan.Repo, Branch: br.plan.Name, Head: br.head, Start: start, Note: br.plan.Kind}
			if err != nil {
				a.Err = err.Error()
			}
			rn.action(a)
		}
		rn.note("pushed %d branches", len(rn.runs))
	}()
	delay, _ := time.ParseDuration(rn.plan.ApproveDelay)
	idx := 0
	lastLanding := time.Now()
	t := time.NewTicker(250 * time.Millisecond)
	defer t.Stop()
	for {
		select {
		case <-ctx.Done():
			return ctx.Err()
		case <-rn.w.changed:
		case <-t.C:
		}
		evs, next := rn.w.eventsSince(idx)
		idx = next
		for _, e := range evs {
			if e.Reason != "Landed" || e.NS != rn.plan.NS {
				continue
			}
			if br := rn.byObj[e.Object]; br != nil && !br.landed {
				br.landed = true
				lastLanding = time.Now()
				logf("landed %s/%s: %s", br.plan.Repo, br.plan.Name, e.Note)
			}
		}
		left := 0
		for _, br := range rn.runs {
			if br.landed {
				continue
			}
			left++
			rn.step(ctx, br, delay)
		}
		if left == 0 {
			return nil
		}
		if time.Now().After(deadline) {
			return fmt.Errorf("%d branches didn't land before the deadline", left)
		}
		if time.Since(lastLanding) > 10*time.Minute {
			return fmt.Errorf("no branch landed for 10 minutes; %d branches left", left)
		}
	}
}

// step plays the developer or reviewer of br once.
func (rn *runner) step(ctx context.Context, br *branchRun, delay time.Duration) {
	if br.busy.Load() {
		return
	}
	obs := rn.w.branch(rn.plan.NS, br.plan.Repo, br.plan.Name)
	if obs == nil || obs.Deleting {
		return
	}
	rn.mu.Lock()
	fixed, resolved, approved := br.fixed, br.resolved[obs.Head], br.approved[obs.Head]
	rn.mu.Unlock()
	switch br.plan.Kind {
	case kindFailing:
		c := obs.Checks["gotest"]
		if !fixed && c.State == "Failed" && c.Commit == obs.Head {
			rn.async(br, func() error { return rn.fix(br, obs.Head) })
		}
	case kindConflict:
		c := obs.Checks["base"]
		if c.State == "Failed" && c.Outputs["conflicts"] != "" && c.Commit == obs.Head && c.ParentCommit == obs.ParentHead && !resolved {
			rn.async(br, func() error { return rn.resolve(br, obs.Head) })
		}
	case kindBigRisk, kindModRisk:
		if !needsApproval(obs, approved) {
			return
		}
		if br.approvalHead != obs.Head {
			br.approvalHead, br.approvalDue = obs.Head, time.Now().Add(delay)
			rn.note("%s is high risk at %s; approving at %s", br.plan.Name, short(obs.Head), br.approvalDue.Format("15:04:05.000"))
		}
		if time.Now().After(br.approvalDue) {
			head, name := obs.Head, obs.Name
			rn.async(br, func() error { return rn.approve(ctx, br, name, head) })
		}
	}
}

// needsApproval reports whether the reviewer of a high-risk branch approves
// the head in obs: risk rated that head high, the reviewer hasn't approved
// it, which approved says, and the approval check doesn't pass for it. The
// check can pass for a head that the reviewer didn't approve when approvals
// follow the change, such as the base check's merge of main into a head
// that the reviewer approved.
func needsApproval(obs *branchRec, approved bool) bool {
	risk, approval := obs.Checks["risk"], obs.Checks["approval"]
	if risk.Commit != obs.Head || risk.Outputs["level"] != "high" || approved {
		return false
	}
	return approval.Commit != obs.Head || approval.State != "Passed"
}

func (rn *runner) async(br *branchRun, f func() error) {
	br.busy.Store(true)
	go func() {
		defer br.busy.Store(false)
		if err := f(); err != nil {
			rn.note("%s/%s: %v", br.plan.Repo, br.plan.Name, err)
		}
	}()
}

// fix pushes a commit that fixes br's failing test on top of the branch's
// head on the git server, as its developer would after pulling.
func (rn *runner) fix(br *branchRun, failed string) error {
	g := rn.repos[br.plan.Repo]
	g.mu.Lock()
	defer g.mu.Unlock()
	start := time.Now()
	var head string
	err := retry(5, func() error {
		heads, err := g.fetch(br.plan.Name)
		if err != nil {
			return err
		}
		if heads[br.plan.Name] == "" {
			return fmt.Errorf("the git server doesn't have %s", br.plan.Name)
		}
		if _, err := g.git(nil, "checkout", "-q", "-B", br.plan.Name, "refs/remotes/origin/"+br.plan.Name); err != nil {
			return err
		}
		if err := g.write(map[string]string{"feat/" + br.plan.ID + "/" + br.plan.ID + "_test.go": featureTest(br.plan.ID, featureNumber(br.plan.ID))}); err != nil {
			return err
		}
		if head, err = g.commit(author{"dev " + br.plan.ID, br.plan.ID + "@example.com"}, "Fix "+br.plan.ID+"'s test"); err != nil {
			return err
		}
		return g.push(br.plan.Name)
	})
	a := actionRec{Action: "fix", Repo: br.plan.Repo, Branch: br.plan.Name, Head: head, Start: start, Note: "gotest failed at " + short(failed)}
	if err != nil {
		a.Err = err.Error()
	} else {
		rn.mu.Lock()
		br.fixed = true
		rn.mu.Unlock()
	}
	rn.action(a)
	return err
}

// resolve merges main into br, resolves the conflict on its pair's line,
// and pushes the merge, as its developer would.
func (rn *runner) resolve(br *branchRun, conflicted string) error {
	g := rn.repos[br.plan.Repo]
	g.mu.Lock()
	defer g.mu.Unlock()
	start := time.Now()
	var head string
	err := retry(5, func() error {
		if _, err := g.fetch(br.plan.Name); err != nil {
			return err
		}
		if _, err := g.git(nil, "checkout", "-q", "-f", "-B", br.plan.Name, "refs/remotes/origin/"+br.plan.Name); err != nil {
			return err
		}
		dev := authorEnv(author{"dev " + br.plan.ID, br.plan.ID + "@example.com"})
		msg := "Merge main into " + br.plan.Name
		if _, err := g.git(dev, "merge", "-q", "--no-ff", "-m", msg, "refs/remotes/origin/main"); err != nil {
			// Resolve the conflict with both branches' names, as the
			// pair's second developer would.
			var owners []string
			for _, other := range rn.plan.Branches {
				if other.Kind == kindConflict && other.Pair == br.plan.Pair {
					owners = append(owners, other.Name)
				}
			}
			sort.Strings(owners)
			if err := g.write(map[string]string{conflictFile(br.plan.Pair): conflictSource(br.plan.Pair, strings.Join(owners, "+"))}); err != nil {
				return err
			}
			if _, err := g.git(dev, "commit", "-q", "--no-edit"); err != nil {
				_, _ = g.git(nil, "merge", "--abort")
				return err
			}
		}
		var err error
		if head, err = g.git(nil, "rev-parse", "HEAD"); err != nil {
			return err
		}
		return g.push(br.plan.Name)
	})
	a := actionRec{Action: "resolve", Repo: br.plan.Repo, Branch: br.plan.Name, Head: head, Start: start, Note: "base conflicted at " + short(conflicted)}
	if err != nil {
		a.Err = err.Error()
	} else {
		rn.mu.Lock()
		br.resolved[conflicted] = true
		rn.mu.Unlock()
	}
	rn.action(a)
	return err
}

// approve annotates br's GitBranch to approve head, as a reviewer would.
func (rn *runner) approve(ctx context.Context, br *branchRun, name, head string) error {
	start := time.Now()
	err := rn.k.mergePatch(ctx, rn.branchPath(name), map[string]any{
		"metadata": map[string]any{"annotations": map[string]string{approveAnnotation: head, approvedByAnnotation: rn.user}},
	})
	a := actionRec{Action: "approve", Repo: br.plan.Repo, Branch: br.plan.Name, Head: head, Start: start, Note: "approved by " + rn.user}
	if err != nil {
		a.Err = err.Error()
	} else {
		rn.mu.Lock()
		br.approved[head] = true
		rn.mu.Unlock()
	}
	rn.action(a)
	return err
}

// settle waits for the landings to reach the git server and the landed
// branches' GitBranches to go away.
func (rn *runner) settle(ctx context.Context) {
	rn.waitQuiet(ctx, 90*time.Second)
	rn.note("settled")
}

// dumpState writes the GitRepositories and GitBranches that are left, each
// Deployment's image, and the logs of git-k8s and the checks since the
// scenario started.
func (rn *runner) dumpState(ctx context.Context) {
	ctxName := rn.env["CONTEXT"]
	kubectlTo := func(name string, args ...string) {
		cmd := exec.CommandContext(ctx, "kubectl", append([]string{"--context", ctxName}, args...)...)
		out, err := cmd.CombinedOutput()
		if err != nil {
			out = append(out, []byte("\n"+err.Error()+"\n")...)
		}
		_ = os.WriteFile(filepath.Join(rn.out, name), out, 0o644)
	}
	kubectlTo("gitobjects.yaml", "-n", rn.plan.NS, "get", "gitrepositories,gitbranches", "-o", "yaml")
	kubectlTo("pods.txt", "get", "pods", "-A", "-o", "wide")
	kubectlTo("images.txt", "get", "deployments", "-A", "-o",
		`jsonpath={range .items[*]}{.metadata.namespace}/{.metadata.name}{" "}{.spec.template.spec.containers[0].image}{"\n"}{end}`)
	// A check's request to the results endpoint can wait for the
	// endpoint's 10-second timeout before the check logs how it ended, and
	// the last landings start such requests.
	sleep(ctx, 11*time.Second)
	_ = os.MkdirAll(filepath.Join(rn.out, "logs"), 0o755)
	since := rn.start.Add(-5 * time.Second).UTC().Format(time.RFC3339)
	for _, program := range programs {
		kubectlTo(filepath.Join("logs", program+".log"), "-n", program, "logs", "-l", "app.kubernetes.io/name="+program,
			"--all-containers", "--prefix", "--timestamps", "--tail=-1", "--since-time="+since, "--max-log-requests=10")
	}
}
