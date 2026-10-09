package main

import (
	"encoding/json"
	"fmt"
	"maps"
	"math"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
)

var t0 = time.Date(2026, 10, 6, 18, 0, 0, 0, time.UTC)

// at returns the time s seconds after t0.
func at(s float64) time.Time { return t0.Add(time.Duration(s * float64(time.Second))) }

// writeLogs writes the lines of each program's log to dir/logs, as a run
// saves them.
func writeLogs(t *testing.T, dir string, logs map[string][]string) {
	t.Helper()
	if err := os.MkdirAll(filepath.Join(dir, "logs"), 0o755); err != nil {
		t.Fatal(err)
	}
	for program, lines := range logs {
		if err := os.WriteFile(filepath.Join(dir, "logs", program+".log"), []byte(strings.Join(lines, "\n")+"\n"), 0o644); err != nil {
			t.Fatal(err)
		}
	}
}

func TestNewDist(t *testing.T) {
	if got, want := newDist([]float64{4, 1, 3, 2, 5}), (dist{N: 5, Min: 1, P50: 3, P90: 4.6, Max: 5, Mean: 3}); got != want {
		t.Errorf("newDist = %+v, want %+v", got, want)
	}
	if got := newDist(nil); got != (dist{}) {
		t.Errorf("newDist(nil) = %+v, want zeros", got)
	}
}

func TestRates(t *testing.T) {
	// The first and last landings are a minute from their neighbors, and
	// the rest 6 seconds apart.
	var times []time.Time
	s := 0.0
	for i := range 20 {
		switch i {
		case 0:
		case 1, 19:
			s += 60
		default:
			s += 6
		}
		times = append(times, at(s))
	}
	if got := middleRate(times); math.Abs(got-10) > 1e-9 {
		t.Errorf("middleRate = %v, want 10 a minute", got)
	}
	if got := rate(times, 0, len(times)-1); got >= 10 {
		t.Errorf("rate from the first landing to the last = %v, want less than the middle's 10", got)
	}
	if got := rate(times, 3, 3); got != 0 {
		t.Errorf("rate over no landings = %v, want 0", got)
	}
}

func TestHistQuantile(t *testing.T) {
	les := []float64{0.1, 0.5, 1, math.Inf(1)}
	for _, c := range []struct {
		q    float64
		cum  []float64
		want float64
	}{
		{.5, []float64{10, 30, 40, 40}, 0.3},
		{.99, []float64{10, 30, 40, 40}, 0.98},
		// Every observation is above the highest finite bucket.
		{.5, []float64{0, 0, 0, 10}, 1},
		{.5, []float64{0, 0, 0, 0}, 0},
	} {
		if got := histQuantile(c.q, les, c.cum); math.Abs(got-c.want) > 1e-9 {
			t.Errorf("histQuantile(%v, %v) = %v, want %v", c.q, c.cum, got, c.want)
		}
	}
}

func TestParseSeries(t *testing.T) {
	name, labels := parseSeries(`kube_reconcile_total{controller="merge",note="a \"b\", c",result="error"}`)
	want := map[string]string{"controller": "merge", "note": `a \"b\", c`, "result": "error"}
	if name != "kube_reconcile_total" || !maps.Equal(labels, want) {
		t.Errorf("parseSeries = %q, %v; want kube_reconcile_total, %v", name, labels, want)
	}
	if name, labels := parseSeries("go_goroutines"); name != "go_goroutines" || len(labels) != 0 {
		t.Errorf("parseSeries without labels = %q, %v", name, labels)
	}
}

func TestLogTime(t *testing.T) {
	for _, c := range []struct {
		line string
		want time.Time
	}{
		{`[pod/check-base-1/check-base] 2026-10-06T18:00:01.123456789Z time=2026-10-06T18:00:01.120Z level=WARN msg="reconcile failed; retrying"`, at(1.123456789)},
		{`[pod/check-base-1/check-base] 2026-10-06T18:00:02.5Z 2026/10/06 18:00:02 INFO the core program didn't take a result check=base`, at(2.5)},
		{`time=2026-10-06T18:00:03.25Z level=INFO msg=listening`, at(3.25)},
		{`2026/10/06 18:00:04 INFO the core program didn't take a result check=base`, at(4)},
	} {
		if got, ok := logTime(c.line); !ok || !got.Equal(c.want) {
			t.Errorf("logTime(%q) = %v, %v; want %v", c.line, got, ok, c.want)
		}
	}
	if got, ok := logTime("goroutine 1 [running]:"); ok {
		t.Errorf("logTime of a line without a time = %v, want none", got)
	}
}

func TestLogLevels(t *testing.T) {
	dir := t.TempDir()
	writeLogs(t, dir, map[string][]string{"check-base": {
		`[pod/check-base-1/check-base] 2026-10-06T18:00:01.5Z time=2026-10-06T18:00:01.499Z level=WARN msg="reconcile failed; retrying" controller=check-base`,
		`[pod/check-base-1/check-base] 2026-10-06T18:00:02.5Z 2026/10/06 18:00:02 INFO the core program didn't take a result check=base`,
		`[pod/check-base-1/check-base] 2026-10-06T18:00:03.5Z {"time":"2026-10-06T18:00:03.5Z","level":"INFO","msg":"listening"}`,
		`2026/10/06 18:00:04 ERROR the check failed`,
		`time=2026-10-06T18:00:05Z level=INFO msg=started`,
		`[pod/check-base-1/check-base] 2026-10-06T18:00:06.5Z 2026/10/06 18:00:06 GET /results 204`,
		`goroutine 1 [running]:`,
	}})
	es := errorSummary{LogLevels: map[string]map[string]int{}}
	logLevels(dir, &es)
	if got, want := es.LogLevels["check-base"], map[string]int{"INFO": 3, "WARN": 1, "ERROR": 1}; !maps.Equal(got, want) {
		t.Errorf("levels = %v, want %v", got, want)
	}
	if len(es.LogSamples) != 2 {
		t.Errorf("samples = %q, want the WARN and ERROR lines", es.LogSamples)
	}
}

// failure is a check's warning, in slog's text handler's format after
// kubectl's prefix, that a reconcile of the Branch object name ended at end
// seconds after t0 with err.
func failure(check string, end float64, name, duration, err string) string {
	ts := at(end).Format(time.RFC3339Nano)
	return fmt.Sprintf(`[pod/check-%[1]s-1/check-%[1]s] %[2]s time=%[2]s level=WARN msg="reconcile failed; retrying" controller=check-%[1]s key=stress-x/%[3]s duration=%[4]s err="%[5]s" retry=1 failures=1`,
		check, ts, name, duration, err)
}

func notFound(name string) string {
	return `git fetch: exit status 128\nsending the base check's result to the core program: Not Found: GitBranch stress-x/` + name + ` doesn't exist`
}

const timedOut = "the core program didn't write the base check's result: the result wasn't written in time; try again"

func TestResultWaits(t *testing.T) {
	dir := t.TempDir()
	writeLogs(t, dir, map[string][]string{
		// Three 404s, from builds before the endpoint answered 410, and a
		// reconcile whose every try got a 503 hold all four workers of the
		// base check from 13 to 20 seconds.
		"check-base": {
			failure("base", 20, "app-c-f001-1", "10s", notFound("app-c-f001-1")),
			failure("base", 21, "app-c-f002-2", "10s", notFound("app-c-f002-2")),
			failure("base", 112, "app-c-f003-3", "100s", timedOut),
			failure("base", 23, "app-c-f004-4", "10s", notFound("app-c-f004-4")),
			failure("base", 24, "app-c-f005-5", "50ms", `main moved to 0123 after it was listed at 4567`),
		},
		"check-gotest": {
			`[pod/check-gotest-1/check-gotest] 2026-10-06T18:00:30.5Z 2026/10/06 18:00:30 INFO the core program didn't take a result check=gotest namespace=stress-x branch=app-c-f005-5 reason="the Branch object stress-x/app-c-f005-5 doesn't exist"`,
			`[pod/check-gotest-1/check-gotest] 2026-10-06T18:00:31.5Z 2026/10/06 18:00:31 INFO the core program didn't take a result check=gotest namespace=stress-x branch=app-c-f006-6 reason="the result isn't for c/f006 at 0123 and main at 4567"`,
			// A build from before the kinds' rename.
			`[pod/check-gotest-1/check-gotest] 2026-10-06T18:00:32.5Z 2026/10/06 18:00:32 INFO the core program didn't take a result check=gotest namespace=stress-x branch=app-c-f007-7 reason="GitBranch stress-x/app-c-f007-7 doesn't exist"`,
		},
	})
	names := map[string]string{"app-c-f001-1": "app c/f001", "app-c-f005-5": "app c/f005"}
	landed := map[string]time.Time{"app-c-f005-5": at(30)}
	cycles := []*frontCycle{
		{Landed: at(25), Cycle: 10, Busy: true}, // 15 to 25: overlaps the stall for 5 seconds
		{Landed: at(18), Cycle: 6, Busy: false}, // not busy
		{Landed: at(40), Cycle: 6, Busy: true},  // after the stall
	}
	ws := resultWaits(dir, t0, landed, names, cycles)

	var got []string
	for _, w := range ws.Waits {
		got = append(got, fmt.Sprintf("%s %s %s %g-%g", w.Check, w.Branch, w.Reason, w.From, w.To))
	}
	want := []string{
		"base app c/f001 gone 10-20",
		"base app-c-f002-2 gone 11-21",
		"base app-c-f003-3 timeout 12-112",
		"base app-c-f004-4 gone 13-23",
	}
	if !slices.Equal(got, want) {
		t.Errorf("waits = %q, want %q", got, want)
	}
	if ws.MaxAtOnce["base"] != 4 {
		t.Errorf("most waits at once = %v, want base 4", ws.MaxAtOnce)
	}
	if want := []stall{{Check: "base", From: 13, To: 20}}; !slices.Equal(ws.Stalls, want) {
		t.Errorf("stalls = %+v, want %+v", ws.Stalls, want)
	}
	if ws.StalledCycles != 1 || ws.StalledSeconds != 5 {
		t.Errorf("stalled cycles = %d for %v seconds, want 1 for 5", ws.StalledCycles, ws.StalledSeconds)
	}
	if len(ws.Gone) != 2 {
		t.Fatalf("410 answers = %+v, want two", ws.Gone)
	}
	if g := ws.Gone[0]; g.Check != "gotest" || g.Branch != "app c/f005" || g.At != 30.5 || g.Landed == nil || *g.Landed != 30 {
		t.Errorf("410 answer = %+v, want gotest's for app c/f005 at 30.5, which landed at 30", g)
	}
	if g := ws.Gone[1]; g.Check != "gotest" || g.Branch != "app-c-f007-7" || g.At != 32.5 || g.Landed != nil {
		t.Errorf("410 answer = %+v, want gotest's for app-c-f007-7 at 32.5, which didn't land", g)
	}
}

func TestReadImages(t *testing.T) {
	dir := t.TempDir()
	const digest = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
	images := "git-k8s/git-k8s registry:5000/gk-stress/git-k8s@sha256:" + digest + "\n" +
		"go-cache/go-cache registry:5000/gk-stress/go-cache:latest\n" +
		"Error from server (Forbidden): deployments.apps is forbidden\n"
	if err := os.WriteFile(filepath.Join(dir, "images.txt"), []byte(images), 0o644); err != nil {
		t.Fatal(err)
	}
	got := readImages(dir)
	want := map[string]string{
		"git-k8s/git-k8s":   "registry:5000/gk-stress/git-k8s@sha256:" + digest,
		"go-cache/go-cache": "registry:5000/gk-stress/go-cache:latest",
	}
	if !maps.Equal(got, want) {
		t.Errorf("readImages = %v, want %v", got, want)
	}
	if got := shortDigest(want["git-k8s/git-k8s"]); got != digest[:12] {
		t.Errorf("shortDigest = %q, want %q", got, digest[:12])
	}
	if got := shortDigest(want["go-cache/go-cache"]); got != want["go-cache/go-cache"] {
		t.Errorf("shortDigest of a reference without a digest = %q, want it whole", got)
	}
}

func TestPodTimes(t *testing.T) {
	// Container times have whole seconds, as the API server reports them.
	done := func(name string, from, to float64) containerRec {
		return containerRec{Name: name, State: "terminated:Completed:0", Started: at(from), Finished: at(to)}
	}
	recs := []record{
		{T: at(0.4), pod: &podRec{Phase: "Pending"}},
		{T: at(9.2), pod: &podRec{Phase: "Running", Init: []containerRec{done("fetch", 2, 3), done("build", 3, 6), done("upload", 6, 7)}, Main: []containerRec{{Name: "test", State: "running", Started: at(7)}}}},
		{T: at(11.3), pod: &podRec{Phase: "Succeeded", Init: []containerRec{done("fetch", 2, 3), done("build", 3, 6), done("upload", 6, 7)}, Main: []containerRec{done("test", 7, 11)}}},
	}
	got := podTimes(recs)
	want := map[string]float64{
		"start": 2, "fetch": 1, "build": 3, "upload": 1, "test": 4, "total": 11,
		"seen:fetch": 8.8, "seen:build": 8.8, "seen:upload": 8.8, "seen:test": 10.9, "seen:done": 10.9,
	}
	for k, v := range want {
		if math.Abs(got[k]-v) > 1e-9 {
			t.Errorf("%s = %v, want %v", k, got[k], v)
		}
	}
	if len(got) != len(want) {
		t.Errorf("podTimes = %v, want %v", got, want)
	}
}

// TestAnalyze analyzes a small run that the recorder writes: three
// branches that land 10 seconds apart, with logs and images.
func TestAnalyze(t *testing.T) {
	dir := t.TempDir()
	p := plan{Scenario: "clean", NS: "stress-clean-0000", Repos: []repoPlan{{Name: "app", Gotest: true, Poll: "2s"}}}
	for i := 1; i <= 3; i++ {
		id := fmt.Sprintf("f%03d", i)
		p.Branches = append(p.Branches, branchPlan{Repo: "app", Name: "c/" + id, ID: id, Kind: kindClean})
	}
	if err := saveJSON(filepath.Join(dir, "plan.json"), p); err != nil {
		t.Fatal(err)
	}
	r, err := newRecorder(filepath.Join(dir, "log.jsonl"))
	if err != nil {
		t.Fatal(err)
	}
	for i, b := range p.Branches {
		r.add("action", t0, actionRec{Action: "push", Repo: b.Repo, Branch: b.Name, Start: t0.Add(-100 * time.Millisecond), Note: b.Kind})
		landed := at(float64(10 * (i + 1)))
		r.add("event", landed, eventRec{Type: "ADDED", NS: p.NS, EventTime: landed, Reason: "Landed", EvType: "Normal",
			Note: fmt.Sprintf("fast-forwarded main from %040d to %s at %040d", i, b.Name, i+1), Object: gitk8s.BranchObjectName(b.Repo, b.Name)})
	}
	head := strings.Repeat("e", 40)
	errs := map[string]checkResult{}
	// More than eight checks, because Go's iteration order varies less for
	// smaller maps.
	for _, name := range []string{"risk", "gotest", "approval", "base", "gofmt", "vet", "lint", "license", "docs"} {
		errs[name] = checkResult{Commit: head, State: "Error", Message: "failed"}
	}
	r.add("branch", at(5), branchRec{Type: "MODIFIED", NS: p.NS, Name: gitk8s.BranchObjectName("app", "c/f001"), Repo: "app", Branch: "c/f001", Head: head, Checks: errs})
	r.close()
	gone := gitk8s.BranchObjectName("app", "c/f003")
	writeLogs(t, dir, map[string][]string{"check-gotest": {
		`[pod/check-gotest-1/check-gotest] 2026-10-06T18:00:30.2Z 2026/10/06 18:00:30 INFO the core program didn't take a result check=gotest namespace=stress-clean-0000 branch=` + gone + ` reason="the Branch object stress-clean-0000/` + gone + ` doesn't exist"`,
	}})
	if err := os.WriteFile(filepath.Join(dir, "images.txt"), []byte("git-k8s/git-k8s registry:5000/gk-stress/git-k8s@sha256:"+strings.Repeat("ab", 32)+"\n"), 0o644); err != nil {
		t.Fatal(err)
	}

	if err := analyze(dir); err != nil {
		t.Fatal(err)
	}
	b, err := os.ReadFile(filepath.Join(dir, "summary.json"))
	if err != nil {
		t.Fatal(err)
	}
	var s summary
	if err := json.Unmarshal(b, &s); err != nil {
		t.Fatal(err)
	}
	if s.Landed != 3 || s.Drain != 30 || s.PerMin != 6 || s.SteadyPerMin != 6 || s.Latency.P50 != 20 {
		t.Errorf("landed %d, drain %v, %v a minute overall and %v first to last, p50 %v; want 3, 30, 6, 6, 20", s.Landed, s.Drain, s.PerMin, s.SteadyPerMin, s.Latency.P50)
	}
	if len(s.Waits.Gone) != 1 || len(s.Waits.Waits) != 0 {
		t.Errorf("waits = %+v, want one 410 answer and no waits", s.Waits)
	}
	// Results that err in the same record are listed by check name, so that
	// analyzing a run again writes the same summary.
	var errChecks []string
	for _, e := range s.Errors.ErrorResults {
		errChecks = append(errChecks, strings.Fields(e)[3])
	}
	if want := []string{"approval", "base", "docs", "gofmt", "gotest", "license", "lint", "risk", "vet"}; !slices.Equal(errChecks, want) {
		t.Errorf("error results = %q, want them for %q", s.Errors.ErrorResults, want)
	}
	md, err := os.ReadFile(filepath.Join(dir, "summary.md"))
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"| Landed | 3 of 3 |", "Image digests: git-k8s `abababababab`", "## Results for deleted branches", "| gotest | app c/f003 | 30.2 | 30.0 |"} {
		if !strings.Contains(string(md), want) {
			t.Errorf("summary.md doesn't have %q:\n%s", want, md)
		}
	}
	for _, name := range []string{"branches.tsv", "fronts.tsv", "timeline.txt"} {
		if _, err := os.Stat(filepath.Join(dir, name)); err != nil {
			t.Error(err)
		}
	}
}
