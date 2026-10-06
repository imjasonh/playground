package main

import (
	"bufio"
	"cmp"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"math"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"sort"
	"strconv"
	"strings"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
)

// record is one decoded line of a run's log.
type record struct {
	T       time.Time
	Kind    string
	branch  *branchRec
	event   eventRec
	pod     *podRec
	cpu     *cpuRec
	metrics *metricsRec
	ext     *extRec
	tick    *tickRec
	action  *actionDone
	note    string
}

// actionDone is an action with the time that it finished.
type actionDone struct {
	actionRec
	Done time.Time
}

type runData struct {
	dir     string
	plan    plan
	recs    []record
	actions []actionDone
	verify  *verifyResult
}

// loadRun reads a run's plan, log, and verification, with the log's records
// in time order.
func loadRun(dir string) (*runData, error) {
	run := &runData{dir: dir}
	b, err := os.ReadFile(filepath.Join(dir, "plan.json"))
	if err != nil {
		return nil, err
	}
	if err := json.Unmarshal(b, &run.plan); err != nil {
		return nil, fmt.Errorf("plan.json: %w", err)
	}
	if b, err := os.ReadFile(filepath.Join(dir, "verify.json")); err == nil {
		var v verifyResult
		if json.Unmarshal(b, &v) == nil {
			run.verify = &v
		}
	}
	f, err := os.Open(filepath.Join(dir, "log.jsonl"))
	if err != nil {
		return nil, err
	}
	defer f.Close()
	dec := json.NewDecoder(bufio.NewReaderSize(f, 1<<20))
	for {
		var r rec
		if err := dec.Decode(&r); errors.Is(err, io.EOF) {
			break
		} else if err != nil {
			// A run that was killed can leave half a line at the end.
			logf("%s: stopping at a bad record: %v", dir, err)
			break
		}
		rc := record{T: r.T, Kind: r.Kind}
		var err error
		switch r.Kind {
		case "branch":
			rc.branch = new(branchRec)
			err = json.Unmarshal(r.D, rc.branch)
		case "event":
			err = json.Unmarshal(r.D, &rc.event)
		case "pod":
			rc.pod = new(podRec)
			err = json.Unmarshal(r.D, rc.pod)
		case "cpu":
			rc.cpu = new(cpuRec)
			err = json.Unmarshal(r.D, rc.cpu)
		case "metrics":
			rc.metrics = new(metricsRec)
			err = json.Unmarshal(r.D, rc.metrics)
		case "ext":
			rc.ext = new(extRec)
			err = json.Unmarshal(r.D, rc.ext)
		case "tick":
			rc.tick = new(tickRec)
			err = json.Unmarshal(r.D, rc.tick)
		case "note":
			var m map[string]string
			err = json.Unmarshal(r.D, &m)
			rc.note = m["msg"]
		case "action":
			var a actionRec
			err = json.Unmarshal(r.D, &a)
			rc.action = &actionDone{a, r.T}
			run.actions = append(run.actions, *rc.action)
		}
		if err != nil {
			return nil, fmt.Errorf("decoding a %s record at %s: %w", r.Kind, r.T, err)
		}
		run.recs = append(run.recs, rc)
	}
	sort.SliceStable(run.recs, func(i, j int) bool { return run.recs[i].T.Before(run.recs[j].T) })
	sort.SliceStable(run.actions, func(i, j int) bool { return run.actions[i].Done.Before(run.actions[j].Done) })
	return run, nil
}

// dist summarizes a sample, in seconds unless it says otherwise.
type dist struct {
	N    int     `json:"n"`
	Min  float64 `json:"min"`
	P50  float64 `json:"p50"`
	P90  float64 `json:"p90"`
	Max  float64 `json:"max"`
	Mean float64 `json:"mean"`
}

func newDist(xs []float64) dist {
	if len(xs) == 0 {
		return dist{}
	}
	s := slices.Sorted(slices.Values(xs))
	sum := 0.0
	for _, x := range s {
		sum += x
	}
	return dist{N: len(s), Min: r2(s[0]), P50: r2(quantile(s, .5)), P90: r2(quantile(s, .9)), Max: r2(s[len(s)-1]), Mean: r2(sum / float64(len(s)))}
}

// quantile interpolates between the closest ranks of a sorted sample.
func quantile(sorted []float64, q float64) float64 {
	if len(sorted) == 0 {
		return 0
	}
	pos := q * float64(len(sorted)-1)
	i := int(pos)
	if i >= len(sorted)-1 {
		return sorted[len(sorted)-1]
	}
	return sorted[i] + (pos-float64(i))*(sorted[i+1]-sorted[i])
}

func r2(v float64) float64 {
	if math.IsNaN(v) || math.IsInf(v, 0) {
		return 0
	}
	return math.Round(v*100) / 100
}

func secs(d time.Duration) float64 { return d.Seconds() }

// evTime is when an event happened, by the clock of the controller that
// recorded it, or when the watch saw it.
func evTime(rc record) time.Time {
	if !rc.event.EventTime.IsZero() {
		return rc.event.EventTime
	}
	return rc.T
}

func terminal(state string) bool {
	return state == "Passed" || state == "Failed" || state == "Fixed" || state == "Error"
}

func position(b *branchRec) int {
	if b.Queued == nil {
		return -1
	}
	return b.Queued.Position
}

// branchStats is one planned branch's way from its first push to its
// landing. The phases are in seconds and add up to Total: Pickup until the
// GitBranch exists, Checks until the branch first joins the queue, Queue
// behind other branches, Front at the front of the queue, and Out after the
// branch left the queue until it joined again.
type branchStats struct {
	Repo       string         `json:"repo"`
	Branch     string         `json:"branch"`
	Kind       string         `json:"kind"`
	Pushed     time.Time      `json:"pushed,omitzero"`
	FirstSeen  time.Time      `json:"firstSeen,omitzero"`
	Landed     time.Time      `json:"landed,omitzero"`
	Synced     time.Time      `json:"synced,omitzero"`
	Total      float64        `json:"total"`
	Pickup     float64        `json:"pickup"`
	Checks     float64        `json:"checks"`
	Queue      float64        `json:"queue"`
	Front      float64        `json:"front"`
	Out        float64        `json:"out"`
	Sync       float64        `json:"sync"`
	Joins      int            `json:"joins"`
	Fronts     int            `json:"fronts"`
	DevPushes  int            `json:"devPushes"`
	Fixes      map[string]int `json:"fixes,omitempty"`
	TestPods   int            `json:"testPods"`
	Results    map[string]int `json:"results"`
	Reasons    []string       `json:"reasons"`
	LandedNote string         `json:"landedNote,omitempty"`
	Last       string         `json:"last,omitempty"`
}

func (st *branchStats) walk(recs []record, end time.Time) {
	if st.Pushed.IsZero() {
		return
	}
	cur, joined, seen := -1, false, false
	last := st.Pushed
	add := func(to time.Time) {
		if !to.After(last) {
			return
		}
		d := secs(to.Sub(last))
		switch {
		case !seen:
			st.Pickup += d
		case cur == 1:
			st.Front += d
		case cur >= 0:
			st.Queue += d
		case joined:
			st.Out += d
		default:
			st.Checks += d
		}
		last = to
	}
	for _, rc := range recs {
		if !end.IsZero() && !rc.T.Before(end) {
			break
		}
		add(rc.T)
		if !seen {
			seen, st.FirstSeen = true, rc.T
		}
		pos := position(rc.branch)
		if pos >= 0 && cur < 0 {
			st.Joins++
			joined = true
		}
		if pos == 1 && cur != 1 {
			st.Fronts++
		}
		cur = pos
	}
	if !end.IsZero() {
		add(end)
	}
}

// frontCycle is the work that landed one branch after it reached the front
// of the queue, in seconds: Handoff from the later of the last landing and
// the branch joining the queue until the branch is first in it, Merge until
// the base check pushed its merge of the parent, List until the GitBranch
// has the merge as its head, Checks until the gate passes for the head, and
// Land until the branch landed. Cycle is the time since the repository's
// last landing, and Busy says whether the branch was already queued then,
// so the queue, not pushes, set the cycle.
type frontCycle struct {
	Repo    string    `json:"repo"`
	Branch  string    `json:"branch"`
	Landed  time.Time `json:"landed"`
	Busy    bool      `json:"busy"`
	Merged  bool      `json:"merged"`
	Cycle   float64   `json:"cycle"`
	Handoff float64   `json:"handoff"`
	Merge   float64   `json:"merge"`
	// PushLag is how long after the merge was listed the base check's
	// push returned and it recorded the PushedFix event.
	PushLag float64 `json:"pushLag"`
	Checks  float64 `json:"checks"`
	Land    float64 `json:"land"`
	// Depth is the parent's queue length when the cycle started.
	Depth   int                `json:"depth"`
	CheckAt map[string]float64 `json:"checkAt,omitempty"`
	Pod     map[string]float64 `json:"pod,omitempty"`
}

type fixEvent struct {
	at    time.Time
	obj   string
	fixer string
	sha   string
}

func newFixEvent(rc record) fixEvent {
	e := rc.event
	f := fixEvent{at: evTime(rc), obj: e.Object}
	if fields := strings.Fields(e.Note); len(fields) > 1 {
		f.sha = fields[1]
	}
	switch {
	case strings.Contains(e.Controller, "base"), strings.Contains(e.Note, " is behind "):
		f.fixer = "base"
	case strings.Contains(e.Controller, "gofmt"), strings.Contains(e.Note, "need gofmt"):
		f.fixer = "gofmt"
	default:
		f.fixer = "other:" + e.Controller
	}
	return f
}

type repoSummary struct {
	Repo         string  `json:"repo"`
	N            int     `json:"n"`
	Landed       int     `json:"landed"`
	FirstLanding float64 `json:"firstLanding"`
	LastLanding  float64 `json:"lastLanding"`
	Drain        float64 `json:"drain"`
	PerMin       float64 `json:"perMin"`
	SteadyPerMin float64 `json:"steadyPerMin"`
	MiddlePerMin float64 `json:"middlePerMin"`
	MedianGap    float64 `json:"medianGap"`
	MaxQueue     int     `json:"maxQueue"`
	Latency      dist    `json:"latency"`
}

type cycleSummary struct {
	// N counts the busy cycles that the distributions describe, and Merged
	// how many of them waited for the base check to merge the parent.
	N       int             `json:"n"`
	Merged  int             `json:"merged"`
	Cycle   dist            `json:"cycle"`
	Handoff dist            `json:"handoff"`
	Merge   dist            `json:"merge"`
	PushLag dist            `json:"pushLag"`
	Checks  dist            `json:"checks"`
	Land    dist            `json:"land"`
	CheckAt map[string]dist `json:"checkAt"`
	Pod     map[string]dist `json:"pod"`
	// ByDepth holds the cycles and merges by the parent's queue length
	// when the cycle started.
	ByDepth []depthRow `json:"byDepth"`
}

type depthRow struct {
	Depth string `json:"depth"`
	Cycle dist   `json:"cycle"`
	Merge dist   `json:"merge"`
}

type groupCPU struct {
	Avg float64 `json:"avg"`
	Max float64 `json:"max"`
}

// cpuSummary is the kind node's CPU use in cores during the burst, from
// the first push to the last landing, and before it.
type cpuSummary struct {
	Cores   int                 `json:"cores"`
	Samples int                 `json:"samples"`
	Before  float64             `json:"before"`
	Avg     float64             `json:"avg"`
	P50     float64             `json:"p50"`
	P90     float64             `json:"p90"`
	Max     float64             `json:"max"`
	HostAvg float64             `json:"hostAvg"`
	MemMax  float64             `json:"memMaxMiB"`
	Groups  map[string]groupCPU `json:"groups"`
}

// reconcileSummary is one controller's reconciles during the burst.
type reconcileSummary struct {
	Program    string             `json:"program"`
	Controller string             `json:"controller"`
	Total      float64            `json:"total"`
	Results    map[string]float64 `json:"results"`
	Mean       float64            `json:"mean"`
	P50        float64            `json:"p50"`
	P90        float64            `json:"p90"`
	P99        float64            `json:"p99"`
	QueueMax   float64            `json:"queueMax"`
}

type errorSummary struct {
	ErrorResults    []string                  `json:"errorResults,omitempty"`
	PushRejections  int                       `json:"pushRejections"`
	WarningEvents   map[string]int            `json:"warningEvents,omitempty"`
	WarningSamples  []string                  `json:"warningSamples,omitempty"`
	Reasons         map[string]int            `json:"reasons"`
	Diverged        []string                  `json:"diverged,omitempty"`
	ActionErrors    []string                  `json:"actionErrors,omitempty"`
	ReconcileErrors map[string]float64        `json:"reconcileErrors,omitempty"`
	Restarts        []string                  `json:"restarts,omitempty"`
	LogLevels       map[string]map[string]int `json:"logLevels,omitempty"`
	LogSamples      []string                  `json:"logSamples,omitempty"`
}

// resultWait is a check's reconcile that failed after it waited for the
// results endpoint's whole timeout, which held one of the check's workers.
// Times are seconds after the first push.
type resultWait struct {
	Check  string `json:"check"`
	Branch string `json:"branch"`
	// Reason is "gone" for a 404 for a GitBranch that was gone, which
	// builds before the endpoint answered 410 sent only after the timeout,
	// and "timeout" for 503s, on every try, for a result that the core
	// program didn't write in time.
	Reason string `json:"reason,omitempty"`
	// From is when the check's reconcile started, and To when it ended.
	From float64 `json:"from"`
	To   float64 `json:"to"`
	// Landed is when the branch landed, if it did while the run watched.
	Landed *float64 `json:"landed,omitempty"`
}

// goneAnswer is a check's result that the results endpoint answered 410
// for, because the GitBranch was gone. At is in seconds after the first
// push.
type goneAnswer struct {
	Check  string   `json:"check"`
	Branch string   `json:"branch"`
	At     float64  `json:"at"`
	Landed *float64 `json:"landed,omitempty"`
}

// stall is a time when such reconciles held every worker of a check, in
// seconds after the first push.
type stall struct {
	Check string  `json:"check"`
	From  float64 `json:"from"`
	To    float64 `json:"to"`
}

// waitSummary describes the checks' reconciles that failed after the
// results endpoint's whole timeout, and the results that it didn't take
// because their GitBranches were gone.
type waitSummary struct {
	Waits     []resultWait   `json:"waits,omitempty"`
	MaxAtOnce map[string]int `json:"maxAtOnce,omitempty"`
	Stalls    []stall        `json:"stalls,omitempty"`
	// StalledCycles counts the busy front-of-queue cycles that overlapped
	// a stall, and StalledSeconds adds up the overlaps.
	StalledCycles  int          `json:"stalledCycles"`
	StalledSeconds float64      `json:"stalledSeconds"`
	Gone           []goneAnswer `json:"gone,omitempty"`
}

type summary struct {
	Scenario      string             `json:"scenario"`
	Namespace     string             `json:"namespace"`
	Repos         int                `json:"repos"`
	N             int                `json:"n"`
	Landed        int                `json:"landed"`
	Kinds         map[string]int     `json:"kinds"`
	Poll          string             `json:"poll"`
	Gotest        bool               `json:"gotest"`
	Landing       string             `json:"landing,omitempty"`
	Start         time.Time          `json:"start"`
	PushSpan      float64            `json:"pushSpan"`
	FirstLanding  float64            `json:"firstLanding"`
	LastLanding   float64            `json:"lastLanding"`
	Drain         float64            `json:"drain"`
	PerMin        float64            `json:"perMin"`
	SteadyPerMin  float64            `json:"steadyPerMin"`
	MiddlePerMin  float64            `json:"middlePerMin"`
	MedianGap     float64            `json:"medianGap"`
	PerRepo       []repoSummary      `json:"perRepo"`
	Latency       dist               `json:"latency"`
	LatencyByKind map[string]dist    `json:"latencyByKind"`
	Phases        map[string]dist    `json:"phases"`
	Sync          dist               `json:"sync"`
	Cycle         cycleSummary       `json:"cycle"`
	Fixes         map[string]int     `json:"fixes"`
	Results       map[string]int     `json:"results"`
	DevPushes     int                `json:"devPushes"`
	Joins         int                `json:"joins"`
	TestPods      int                `json:"testPods"`
	PodPhases     map[string]dist    `json:"podPhases"`
	MaxTestPods   int                `json:"maxTestPods"`
	AvgTestPods   float64            `json:"avgTestPods"`
	MaxQueue      int                `json:"maxQueue"`
	CPU           cpuSummary         `json:"cpu"`
	Reconciles    []reconcileSummary `json:"reconciles"`
	GoCache       map[string]float64 `json:"goCache,omitempty"`
	Errors        errorSummary       `json:"errors"`
	Waits         waitSummary        `json:"waits"`
	Stuck         []string           `json:"stuck,omitempty"`
	Warmup        map[string]float64 `json:"warmup,omitempty"`
	Verify        *verifyResult      `json:"verify,omitempty"`
	// Images has each Deployment's image, by namespace/name, so that runs
	// show which build they ran.
	Images map[string]string `json:"images,omitempty"`
}

// analyze writes summary.json, summary.md, branches.tsv, fronts.tsv, and
// timeline.txt for a run.
func analyze(dir string) error {
	run, err := loadRun(dir)
	if err != nil {
		return err
	}
	s, stats, cycles := summarize(run)
	if err := saveJSON(filepath.Join(dir, "summary.json"), s); err != nil {
		return err
	}
	if err := os.WriteFile(filepath.Join(dir, "summary.md"), []byte(summaryMarkdown(s)), 0o644); err != nil {
		return err
	}
	if err := os.WriteFile(filepath.Join(dir, "branches.tsv"), []byte(branchesTSV(s, stats)), 0o644); err != nil {
		return err
	}
	if err := os.WriteFile(filepath.Join(dir, "fronts.tsv"), []byte(frontsTSV(s, cycles)), 0o644); err != nil {
		return err
	}
	return os.WriteFile(filepath.Join(dir, "timeline.txt"), []byte(timeline(run, s.Start)), 0o644)
}

func summarize(run *runData) (*summary, []*branchStats, []*frontCycle) {
	p := &run.plan
	ns := p.NS
	s := &summary{
		Scenario: p.Scenario, Namespace: ns, Repos: len(p.Repos), N: len(p.Branches), Kinds: map[string]int{},
		Poll: "30s (default)", LatencyByKind: map[string]dist{}, Phases: map[string]dist{}, Fixes: map[string]int{},
		Results: map[string]int{}, PodPhases: map[string]dist{}, Verify: run.verify, Warmup: map[string]float64{},
	}
	if len(p.Repos) > 0 {
		if p.Repos[0].Poll != "" {
			s.Poll = p.Repos[0].Poll
		}
		s.Gotest = p.Repos[0].Gotest
		var landings []string
		for _, r := range p.Repos {
			if r.Landing != "" {
				landings = append(landings, r.Name+"="+r.Landing)
			}
		}
		s.Landing = strings.Join(landings, ", ")
	}
	s.Errors = errorSummary{WarningEvents: map[string]int{}, Reasons: map[string]int{}, ReconcileErrors: map[string]float64{}, LogLevels: map[string]map[string]int{}}

	planned := map[string]branchPlan{}
	for _, b := range p.Branches {
		planned[gitk8s.BranchObjectName(b.Repo, b.Name)] = b
		s.Kinds[b.Kind]++
	}
	byKey := map[string][]record{}
	landedEv := map[string]record{}
	fixesByObj := map[string][]fixEvent{}
	extByRepo := map[string][]record{}
	testPods := map[string][]record{}
	var ticks, cpus, scrapes []record
	lastRestarts := map[string]int{}
	warnings, warnReasons := map[string]int{}, map[string]string{}
	for _, rc := range run.recs {
		switch rc.Kind {
		case "branch":
			if rc.branch.NS == ns {
				key := rc.branch.Repo + "/" + rc.branch.Branch
				byKey[key] = append(byKey[key], rc)
			}
		case "event":
			e := rc.event
			if e.NS != ns {
				continue
			}
			if e.EvType == "Warning" {
				// A repeated event is one object whose series counts the
				// repeats.
				warnings[e.Name] = max(warnings[e.Name], max(1, e.Count))
				warnReasons[e.Name] = e.Reason
				if e.Type == "ADDED" && len(s.Errors.WarningSamples) < 20 {
					s.Errors.WarningSamples = append(s.Errors.WarningSamples, fmt.Sprintf("%s %s %s: %s", e.Controller, e.Reason, e.Object, e.Note))
				}
			}
			switch e.Reason {
			case "Landed":
				if _, ok := landedEv[e.Object]; !ok {
					landedEv[e.Object] = rc
				}
			case "PushedFix":
				if e.Type == "ADDED" {
					fixesByObj[e.Object] = append(fixesByObj[e.Object], newFixEvent(rc))
				}
			}
		case "pod":
			pr := rc.pod
			if pr.NS == ns && pr.App == "test" {
				testPods[pr.UID] = append(testPods[pr.UID], rc)
			} else if slices.Contains(programs, pr.NS) {
				n := restarts(*pr)
				if old, ok := lastRestarts[pr.UID]; ok && n > old {
					s.Errors.Restarts = append(s.Errors.Restarts, fmt.Sprintf("%s %s/%s restarted (%d restarts)", rc.T.Format(time.TimeOnly), pr.NS, pr.Name, n))
				}
				lastRestarts[pr.UID] = n
			}
		case "tick":
			ticks = append(ticks, rc)
		case "cpu":
			cpus = append(cpus, rc)
		case "metrics":
			scrapes = append(scrapes, rc)
		case "ext":
			if rc.ext.Ref == "main" {
				extByRepo[rc.ext.Repo] = append(extByRepo[rc.ext.Repo], rc)
			}
		}
	}
	for name, n := range warnings {
		s.Errors.WarningEvents[warnReasons[name]] += n
	}

	pushed := map[string]actionDone{}
	devPushes := map[string]int{}
	warmPush := map[string]time.Time{}
	for _, a := range run.actions {
		k := a.Repo + "/" + a.Branch
		switch a.Action {
		case "push":
			if _, ok := pushed[k]; !ok {
				pushed[k] = a
			}
			devPushes[k]++
		case "fix", "resolve":
			devPushes[k]++
		case "warmup":
			warmPush[a.Repo] = a.Done
		}
		if a.Err != "" {
			s.Errors.ActionErrors = append(s.Errors.ActionErrors, fmt.Sprintf("%s %s %s %s: %s", a.Done.Format(time.TimeOnly), a.Action, a.Repo, a.Branch, a.Err))
		}
	}
	var start, lastPush time.Time
	for _, a := range pushed {
		if start.IsZero() || a.Done.Before(start) {
			start = a.Done
		}
		if a.Done.After(lastPush) {
			lastPush = a.Done
		}
	}
	s.Start = start
	s.PushSpan = r2(secs(lastPush.Sub(start)))
	for _, rp := range p.Repos {
		obj := gitk8s.BranchObjectName(rp.Name, "c/w00")
		if ev, ok := landedEv[obj]; ok && !warmPush[rp.Name].IsZero() {
			s.Warmup[rp.Name] = r2(secs(evTime(ev).Sub(warmPush[rp.Name])))
		}
	}

	// Each planned branch.
	podsByObj := map[string][]string{}
	for uid, recs := range testPods {
		if owner := recs[0].pod.Owner; owner != "" {
			podsByObj[owner] = append(podsByObj[owner], uid)
		}
	}
	var stats []*branchStats
	errorSeen := map[string]bool{}
	for _, b := range p.Branches {
		k := b.Repo + "/" + b.Name
		obj := gitk8s.BranchObjectName(b.Repo, b.Name)
		st := &branchStats{Repo: b.Repo, Branch: b.Name, Kind: b.Kind, Results: map[string]int{}, Fixes: map[string]int{}, DevPushes: devPushes[k]}
		if a, ok := pushed[k]; ok {
			st.Pushed = a.Done
		}
		if ev, ok := landedEv[obj]; ok {
			st.Landed, st.LandedNote = evTime(ev), ev.event.Note
		}
		recs := byKey[k]
		st.walk(recs, st.Landed)
		if !st.Landed.IsZero() && !st.Pushed.IsZero() {
			st.Total = secs(st.Landed.Sub(st.Pushed))
		}
		seen := map[string]bool{}
		for _, rc := range recs {
			br := rc.branch
			for name, c := range br.Checks {
				if !terminal(c.State) {
					continue
				}
				if id := name + " " + c.Commit + " " + c.ParentCommit; !seen[id] {
					seen[id] = true
					st.Results[name]++
				}
				if c.State == "Error" {
					id := b.Name + " " + name + " " + c.Commit + " " + c.ParentCommit
					if !errorSeen[id] {
						errorSeen[id] = true
						s.Errors.ErrorResults = append(s.Errors.ErrorResults, fmt.Sprintf("%s %s %s %s at %s: %s", rc.T.Format("15:04:05.000"), b.Repo, b.Name, name, short(c.Commit), c.Message))
						if strings.Contains(c.Message, "pushing ") {
							s.Errors.PushRejections++
						}
					}
				}
			}
			if br.Merged != nil && !slices.Contains(st.Reasons, br.Merged.Reason) {
				st.Reasons = append(st.Reasons, br.Merged.Reason)
			}
			if len(br.Diverged) > 0 && len(s.Errors.Diverged) < 20 {
				s.Errors.Diverged = append(s.Errors.Diverged, fmt.Sprintf("%s %s %s: %s", rc.T.Format("15:04:05.000"), b.Repo, b.Name, br.Diverged))
			}
		}
		for _, reason := range st.Reasons {
			s.Errors.Reasons[reason]++
		}
		for _, f := range fixesByObj[obj] {
			st.Fixes[f.fixer]++
			s.Fixes[f.fixer]++
		}
		st.TestPods = len(podsByObj[obj])
		for name, n := range st.Results {
			s.Results[name] += n
		}
		s.DevPushes += st.DevPushes
		s.Joins += st.Joins
		if st.Landed.IsZero() {
			last := "never listed"
			if len(recs) > 0 {
				br := recs[len(recs)-1].branch
				last = fmt.Sprintf("head %s, state %s, position %d, checks %s", short(br.Head), br.State, position(br), summarizeChecks(br))
				if br.Merged != nil {
					last += fmt.Sprintf(", Merged %s: %s", br.Merged.Reason, br.Merged.Message)
				}
				if br.Deleting || br.Type == "DELETED" {
					last += ", deleted"
				}
			}
			st.Last = last
			s.Stuck = append(s.Stuck, fmt.Sprintf("%s %s (%s): %s", b.Repo, b.Name, b.Kind, last))
		}
		stats = append(stats, st)
	}

	// Landings, by repository and overall.
	type landing struct {
		at   time.Time
		st   *branchStats
		head string
	}
	byRepo := map[string][]landing{}
	var all []time.Time
	for _, st := range stats {
		if st.Landed.IsZero() {
			continue
		}
		fields := strings.Fields(st.LandedNote)
		head := ""
		if len(fields) > 0 {
			head = fields[len(fields)-1]
		}
		byRepo[st.Repo] = append(byRepo[st.Repo], landing{st.Landed, st, head})
		all = append(all, st.Landed)
	}
	slices.SortFunc(all, func(a, b time.Time) int { return a.Compare(b) })
	s.Landed = len(all)
	maxQueue := map[string]int{}
	for _, rc := range ticks {
		for key, tp := range rc.tick.Parents {
			repo := strings.TrimPrefix(key, ns+"/")
			maxQueue[repo] = max(maxQueue[repo], tp.Queue)
			s.MaxQueue = max(s.MaxQueue, tp.Queue)
		}
	}
	var gaps []float64
	var cycles []*frontCycle
	for _, rp := range p.Repos {
		ls := byRepo[rp.Name]
		slices.SortFunc(ls, func(a, b landing) int { return a.at.Compare(b.at) })
		rs := repoSummary{Repo: rp.Name, Landed: len(ls), MaxQueue: maxQueue[rp.Name]}
		for _, b := range p.Branches {
			if b.Repo == rp.Name {
				rs.N++
			}
		}
		var lat []float64
		times := make([]time.Time, len(ls))
		ext := extByRepo[repoKey(ns, rp.Name)]
		for i, l := range ls {
			times[i] = l.at
			lat = append(lat, l.st.Total)
			if i > 0 {
				gaps = append(gaps, secs(l.at.Sub(ls[i-1].at)))
			}
			// The git server has the landing once its main is this
			// landing's head or a later one's.
		sync:
			for _, e := range ext {
				if e.T.Before(l.at) {
					continue
				}
				for _, later := range ls[i:] {
					if later.head != "" && strings.HasPrefix(e.ext.SHA, later.head) {
						l.st.Synced, l.st.Sync = e.T, secs(e.T.Sub(l.at))
						break sync
					}
				}
			}
		}
		rs.Latency = newDist(lat)
		if len(ls) > 0 {
			rs.FirstLanding = r2(secs(ls[0].at.Sub(start)))
			rs.LastLanding = r2(secs(ls[len(ls)-1].at.Sub(start)))
			rs.Drain = rs.LastLanding
			if rs.Drain > 0 {
				rs.PerMin = r2(float64(len(ls)) / rs.Drain * 60)
			}
			rs.SteadyPerMin = r2(rate(times, 0, len(times)-1))
			rs.MiddlePerMin = r2(middleRate(times))
			var repoGaps []float64
			for i := 1; i < len(times); i++ {
				repoGaps = append(repoGaps, secs(times[i].Sub(times[i-1])))
			}
			rs.MedianGap = newDist(repoGaps).P50
		}
		s.PerRepo = append(s.PerRepo, rs)
		var prev time.Time
		for _, l := range ls {
			fc := frontOf(l.st, byKey[l.st.Repo+"/"+l.st.Branch], fixesByObj[gitk8s.BranchObjectName(l.st.Repo, l.st.Branch)],
				testPods, podsByObj[gitk8s.BranchObjectName(l.st.Repo, l.st.Branch)], l.at, prev, rp.Gotest)
			if !prev.IsZero() {
				fc.Depth = depthAfter(ticks, ns+"/"+rp.Name, prev.Add(300*time.Millisecond))
			}
			cycles = append(cycles, fc)
			prev = l.at
		}
	}
	if len(all) > 0 {
		s.FirstLanding = r2(secs(all[0].Sub(start)))
		s.LastLanding = r2(secs(all[len(all)-1].Sub(start)))
		s.Drain = s.LastLanding
		if s.Drain > 0 {
			s.PerMin = r2(float64(len(all)) / s.Drain * 60)
		}
		s.SteadyPerMin = r2(rate(all, 0, len(all)-1))
		s.MiddlePerMin = r2(middleRate(all))
	}
	s.MedianGap = newDist(gaps).P50

	// Latency and phases.
	var total, pickup, checks, queue, front, out, sync []float64
	byKind := map[string][]float64{}
	for _, st := range stats {
		if st.Landed.IsZero() || st.Pushed.IsZero() {
			continue
		}
		total = append(total, st.Total)
		byKind[st.Kind] = append(byKind[st.Kind], st.Total)
		pickup = append(pickup, st.Pickup)
		checks = append(checks, st.Checks)
		queue = append(queue, st.Queue)
		front = append(front, st.Front)
		out = append(out, st.Out)
		if !st.Synced.IsZero() {
			sync = append(sync, st.Sync)
		}
	}
	s.Latency = newDist(total)
	for kind, xs := range byKind {
		s.LatencyByKind[kind] = newDist(xs)
	}
	s.Phases = map[string]dist{"pickup": newDist(pickup), "checks": newDist(checks), "queue": newDist(queue), "front": newDist(front), "out": newDist(out)}
	s.Sync = newDist(sync)
	s.Cycle = summarizeCycles(cycles)

	// Test Pods.
	end := start
	if len(all) > 0 {
		end = all[len(all)-1]
	}
	phases := map[string][]float64{}
	for _, recs := range testPods {
		if _, ok := planned[recs[0].pod.Owner]; !ok {
			continue
		}
		s.TestPods++
		for name, d := range podTimes(recs) {
			phases[name] = append(phases[name], d)
		}
	}
	for name, xs := range phases {
		s.PodPhases[name] = newDist(xs)
	}
	var podSum float64
	var podN int
	for _, rc := range ticks {
		if rc.T.Before(start) || rc.T.After(end) {
			continue
		}
		s.MaxTestPods = max(s.MaxTestPods, rc.tick.Pods)
		podSum += float64(rc.tick.Pods)
		podN++
	}
	if podN > 0 {
		s.AvgTestPods = r2(podSum / float64(podN))
	}

	s.CPU = summarizeCPU(cpus, start, end)
	s.Reconciles, s.GoCache, s.Errors.ReconcileErrors = summarizeMetrics(scrapes, start, end)
	logLevels(run.dir, &s.Errors)
	landedAt := map[string]time.Time{}
	for _, rc := range run.recs {
		if rc.Kind == "event" && rc.event.Reason == "Landed" {
			landedAt[rc.event.Object] = evTime(rc)
		}
	}
	names := map[string]string{}
	for _, bp := range run.plan.Branches {
		names[gitk8s.BranchObjectName(bp.Repo, bp.Name)] = bp.Repo + " " + bp.Name
	}
	s.Waits = resultWaits(run.dir, start, landedAt, names, cycles)
	s.Images = readImages(run.dir)
	return s, stats, cycles
}

// readImages reads the images.txt that a run writes: a line for each
// Deployment, with its namespace/name and its first container's image.
func readImages(dir string) map[string]string {
	b, err := os.ReadFile(filepath.Join(dir, "images.txt"))
	if err != nil {
		return nil
	}
	images := map[string]string{}
	for line := range strings.SplitSeq(string(b), "\n") {
		name, image, ok := strings.Cut(strings.TrimSpace(line), " ")
		if ok && strings.Contains(name, "/") && image != "" && !strings.Contains(image, " ") {
			images[name] = image
		}
	}
	return images
}

// shortDigest returns the first 12 hex digits of an image reference's
// digest, or the whole reference if it has no digest.
func shortDigest(ref string) string {
	_, d, ok := strings.Cut(ref, "@sha256:")
	if !ok {
		return ref
	}
	return d[:min(12, len(d))]
}

// depthAfter returns the queue length of the parent with key at the first
// tick at or after t.
func depthAfter(ticks []record, key string, t time.Time) int {
	for _, rc := range ticks {
		if rc.T.Before(t) {
			continue
		}
		return rc.tick.Parents[key].Queue
	}
	return 0
}

// rate returns the landings per minute from times[i] to times[j].
func rate(times []time.Time, i, j int) float64 {
	if j <= i || j >= len(times) {
		return 0
	}
	d := secs(times[j].Sub(times[i]))
	if d <= 0 {
		return 0
	}
	return float64(j-i) / d * 60
}

// middleRate is the landing rate between the 10th and 90th percentiles of
// the landings, which leaves out the first branches' checks and the tail.
func middleRate(times []time.Time) float64 {
	n := len(times)
	if n < 5 {
		return rate(times, 0, n-1)
	}
	return rate(times, n/10, int(math.Ceil(0.9*float64(n)))-1)
}

// frontOf breaks down the work that landed st at landed.
func frontOf(st *branchStats, recs []record, fixes []fixEvent, testPods map[string][]record, pods []string, landed, prev time.Time, gotest bool) *frontCycle {
	fc := &frontCycle{Repo: st.Repo, Branch: st.Branch, Landed: landed, CheckAt: map[string]float64{}}
	var frontStart, joinAt time.Time
	cur := -1
	for _, rc := range recs {
		if !rc.T.Before(landed) {
			break
		}
		pos := position(rc.branch)
		if pos >= 0 && cur < 0 {
			joinAt = rc.T
		}
		if pos == 1 && cur != 1 {
			frontStart = rc.T
		}
		cur = pos
	}
	if !prev.IsZero() {
		fc.Cycle = r2(secs(landed.Sub(prev)))
		fc.Busy = !joinAt.IsZero() && joinAt.Before(prev)
	}
	ref := joinAt
	if prev.After(ref) {
		ref = prev
	}
	if frontStart.IsZero() || frontStart.Before(ref) {
		frontStart = ref
	}
	if !ref.IsZero() {
		fc.Handoff = r2(secs(frontStart.Sub(ref)))
	}
	// The PushedFix event comes seconds after the merge is listed, and can
	// come after the landing, so the merge counts from when the branch's
	// head became the fix.
	from := frontStart
	for _, f := range fixes {
		if f.fixer != "base" || f.sha == "" || f.at.Before(frontStart.Add(-2*time.Second)) || f.at.After(landed.Add(30*time.Second)) {
			continue
		}
		for _, rc := range recs {
			if rc.T.Before(frontStart.Add(-2*time.Second)) || !rc.T.Before(landed) || !strings.HasPrefix(rc.branch.Head, f.sha) {
				continue
			}
			fc.Merged = true
			fc.Merge = r2(max(0, secs(rc.T.Sub(frontStart))))
			fc.PushLag = r2(secs(f.at.Sub(rc.T)))
			from = rc.T
			break
		}
	}
	passAt := landed
	need := []string{"base", "gofmt", "risk", "approval"}
	if gotest {
		need = append(need, "gotest")
	}
	for _, rc := range recs {
		if rc.T.Before(from) || rc.T.After(landed.Add(5*time.Second)) {
			continue
		}
		b := rc.branch
		for _, name := range need {
			if c := b.Checks[name]; c.State == "Passed" && c.Commit == b.Head {
				if _, ok := fc.CheckAt[name]; !ok {
					fc.CheckAt[name] = r2(secs(rc.T.Sub(from)))
				}
			}
		}
		if len(gateProblems(b, gotest, "")) == 0 && rc.T.Before(passAt) {
			passAt = rc.T
			break
		}
	}
	if passAt.Before(from) {
		passAt = from
	}
	fc.Checks = r2(secs(passAt.Sub(from)))
	fc.Land = r2(max(0, secs(landed.Sub(passAt))))
	// The test Pod that ran for the landed head started after the head
	// was listed.
	var first []record
	for _, uid := range pods {
		r := testPods[uid]
		if len(r) == 0 || r[0].T.Before(from.Add(-time.Second)) || r[0].T.After(landed) {
			continue
		}
		if first == nil || r[0].T.Before(first[0].T) {
			first = r
		}
	}
	if first != nil {
		fc.Pod = podTimes(first)
		for k, v := range fc.Pod {
			fc.Pod[k] = r2(v)
		}
		fc.Pod["created"] = r2(secs(first[0].T.Sub(from)))
	}
	return fc
}

// podTimes returns how long a test Pod took to start its first container,
// how long each container ran, and how long the Pod took in all, from the
// watch's records of it.
func podTimes(recs []record) map[string]float64 {
	out := map[string]float64{}
	created := recs[0].T
	var last *podRec
	for _, rc := range recs {
		if len(rc.pod.Init)+len(rc.pod.Main) > 0 {
			last = rc.pod
		}
	}
	if last == nil {
		return out
	}
	var firstStart, lastFinish time.Time
	for _, c := range append(slices.Clone(last.Init), last.Main...) {
		if c.Started.IsZero() {
			continue
		}
		if firstStart.IsZero() || c.Started.Before(firstStart) {
			firstStart = c.Started
		}
		if !c.Finished.IsZero() {
			out[c.Name] = secs(c.Finished.Sub(c.Started))
			if c.Finished.After(lastFinish) {
				lastFinish = c.Finished
			}
		}
	}
	// Container times have whole seconds, so these are rough.
	if !firstStart.IsZero() {
		out["start"] = max(0, secs(firstStart.Sub(created.Truncate(time.Second))))
	}
	if !lastFinish.IsZero() {
		out["total"] = max(0, secs(lastFinish.Sub(created.Truncate(time.Second))))
	}
	// The watch saw each change within milliseconds, so the seen: times,
	// from when the watch first saw the Pod, are finer.
	for _, rc := range recs {
		p := rc.pod
		if _, ok := out["seen:done"]; !ok && (p.Phase == "Succeeded" || p.Phase == "Failed") {
			out["seen:done"] = secs(rc.T.Sub(created))
		}
		for _, c := range append(slices.Clone(p.Init), p.Main...) {
			if _, ok := out["seen:"+c.Name]; !ok && strings.HasPrefix(c.State, "terminated") {
				out["seen:"+c.Name] = secs(rc.T.Sub(created))
			}
		}
	}
	return out
}

func summarizeCycles(cycles []*frontCycle) cycleSummary {
	cs := cycleSummary{CheckAt: map[string]dist{}, Pod: map[string]dist{}}
	var cycle, handoff, merge, pushLag, checks, land []float64
	checkAt := map[string][]float64{}
	pod := map[string][]float64{}
	buckets := []struct {
		label    string
		min, max int
	}{{"1", 1, 1}, {"2-3", 2, 3}, {"4-7", 4, 7}, {"8-15", 8, 15}, {"16-31", 16, 31}, {"32-63", 32, 63}, {"64+", 64, math.MaxInt}}
	depthCycle := make([][]float64, len(buckets))
	depthMerge := make([][]float64, len(buckets))
	for _, c := range cycles {
		if !c.Busy {
			continue
		}
		cs.N++
		if c.Merged {
			cs.Merged++
			merge = append(merge, c.Merge)
			pushLag = append(pushLag, c.PushLag)
		}
		cycle = append(cycle, c.Cycle)
		handoff = append(handoff, c.Handoff)
		checks = append(checks, c.Checks)
		land = append(land, c.Land)
		for i, bk := range buckets {
			if c.Depth >= bk.min && c.Depth <= bk.max {
				depthCycle[i] = append(depthCycle[i], c.Cycle)
				if c.Merged {
					depthMerge[i] = append(depthMerge[i], c.Merge)
				}
			}
		}
		for k, v := range c.CheckAt {
			checkAt[k] = append(checkAt[k], v)
		}
		for k, v := range c.Pod {
			pod[k] = append(pod[k], v)
		}
	}
	cs.Cycle, cs.Handoff, cs.Merge, cs.PushLag, cs.Checks, cs.Land = newDist(cycle), newDist(handoff), newDist(merge), newDist(pushLag), newDist(checks), newDist(land)
	for i, bk := range buckets {
		if len(depthCycle[i]) > 0 {
			cs.ByDepth = append(cs.ByDepth, depthRow{Depth: bk.label, Cycle: newDist(depthCycle[i]), Merge: newDist(depthMerge[i])})
		}
	}
	for k, v := range checkAt {
		cs.CheckAt[k] = newDist(v)
	}
	for k, v := range pod {
		cs.Pod[k] = newDist(v)
	}
	return cs
}

func summarizeCPU(cpus []record, start, end time.Time) cpuSummary {
	cs := cpuSummary{Cores: numCPU(), Groups: map[string]groupCPU{}}
	var node, host, before []float64
	groups := map[string][]float64{}
	for _, rc := range cpus {
		c := rc.cpu
		if rc.T.Before(start) && rc.T.After(start.Add(-20*time.Second)) {
			before = append(before, c.Node)
		}
		if rc.T.Before(start) || rc.T.After(end) {
			continue
		}
		node = append(node, c.Node)
		host = append(host, c.Host)
		cs.MemMax = max(cs.MemMax, c.MemMiB)
		for g, v := range c.Groups {
			groups[g] = append(groups[g], v)
		}
	}
	cs.Samples = len(node)
	d := newDist(node)
	cs.Avg, cs.P50, cs.P90, cs.Max = d.Mean, d.P50, d.P90, d.Max
	cs.HostAvg = newDist(host).Mean
	cs.Before = newDist(before).Mean
	cs.MemMax = r2(cs.MemMax)
	for g, xs := range groups {
		// Groups that appear partway count as zero before they do.
		sum, peak := 0.0, 0.0
		for _, x := range xs {
			sum += x
			peak = max(peak, x)
		}
		cs.Groups[g] = groupCPU{Avg: r2(sum / float64(max(1, len(node)))), Max: r2(peak)}
	}
	return cs
}

var labelRE = regexp.MustCompile(`(\w+)="((?:[^"\\]|\\.)*)"`)

func parseSeries(series string) (string, map[string]string) {
	name, rest, ok := strings.Cut(series, "{")
	labels := map[string]string{}
	if ok {
		for _, m := range labelRE.FindAllStringSubmatch(strings.TrimSuffix(rest, "}"), -1) {
			labels[m[1]] = m[2]
		}
	}
	return name, labels
}

// summarizeMetrics compares each Pod's last scrape with its last scrape
// before the burst, and reports the reconciles of each controller, go-cache's
// requests, and reconcile errors by controller.
func summarizeMetrics(scrapes []record, start, end time.Time) ([]reconcileSummary, map[string]float64, map[string]float64) {
	type podKey struct{ program, pod string }
	baseline := map[podKey]map[string]float64{}
	final := map[podKey]map[string]float64{}
	queueMax := map[string]float64{}
	for _, rc := range scrapes {
		m := rc.metrics
		k := podKey{m.Program, m.Pod}
		if !rc.T.After(start) {
			baseline[k] = m.Samples
		}
		final[k] = m.Samples
		if rc.T.After(start.Add(-10*time.Second)) && !rc.T.After(end.Add(10*time.Second)) {
			byController := map[string]float64{}
			for series, v := range m.Samples {
				if name, labels := parseSeries(series); name == "kube_queue_depth" {
					byController[m.Program+"/"+labels["controller"]] += v
				}
			}
			for c, v := range byController {
				queueMax[c] = max(queueMax[c], v)
			}
		}
	}
	delta := map[string]map[string]float64{}
	for k, fin := range final {
		base := baseline[k]
		d := delta[k.program]
		if d == nil {
			d = map[string]float64{}
			delta[k.program] = d
		}
		for series, v := range fin {
			if b, ok := base[series]; ok && v >= b {
				d[series] += v - b
			} else {
				d[series] += v
			}
		}
	}
	type ctl struct{ program, controller string }
	sums := map[ctl]*reconcileSummary{}
	buckets := map[ctl]map[float64]float64{}
	get := func(c ctl) *reconcileSummary {
		if sums[c] == nil {
			sums[c] = &reconcileSummary{Program: c.program, Controller: c.controller, Results: map[string]float64{}}
		}
		return sums[c]
	}
	goCache := map[string]float64{}
	errs := map[string]float64{}
	durSum := map[ctl]float64{}
	durCount := map[ctl]float64{}
	for program, d := range delta {
		for series, v := range d {
			name, labels := parseSeries(series)
			c := ctl{program, labels["controller"]}
			switch name {
			case "kube_reconcile_total":
				rs := get(c)
				rs.Total += v
				rs.Results[labels["result"]] += v
				if labels["result"] == "error" || labels["result"] == "permanent_error" {
					errs[program+"/"+c.controller] += v
				}
			case "kube_reconcile_duration_seconds_bucket":
				le := math.Inf(1)
				if labels["le"] != "+Inf" {
					le, _ = strconv.ParseFloat(labels["le"], 64)
				}
				if buckets[c] == nil {
					buckets[c] = map[float64]float64{}
				}
				buckets[c][le] += v
			case "kube_reconcile_duration_seconds_sum":
				durSum[c] += v
			case "kube_reconcile_duration_seconds_count":
				durCount[c] += v
			default:
				if strings.HasPrefix(name, "go_cache_") && strings.HasSuffix(name, "_total") && v > 0 {
					goCache[strings.TrimPrefix(series, "go_cache_")] += v
				}
			}
		}
	}
	var out []reconcileSummary
	for c, rs := range sums {
		if rs.Total == 0 {
			continue
		}
		if n := durCount[c]; n > 0 {
			rs.Mean = r2(durSum[c] / n * 1000)
		}
		les := slices.Sorted(func(yield func(float64) bool) {
			for le := range buckets[c] {
				if !yield(le) {
					return
				}
			}
		})
		cum := make([]float64, len(les))
		for i, le := range les {
			cum[i] = buckets[c][le]
		}
		rs.P50, rs.P90, rs.P99 = r2(histQuantile(.5, les, cum)*1000), r2(histQuantile(.9, les, cum)*1000), r2(histQuantile(.99, les, cum)*1000)
		rs.QueueMax = queueMax[c.program+"/"+c.controller]
		rs.Total = math.Round(rs.Total)
		out = append(out, *rs)
	}
	sort.Slice(out, func(i, j int) bool {
		if out[i].Program != out[j].Program {
			return out[i].Program < out[j].Program
		}
		return out[i].Controller < out[j].Controller
	})
	return out, goCache, errs
}

// histQuantile estimates a quantile from cumulative bucket counts, as
// Prometheus's histogram_quantile does. The result is in the buckets'
// unit.
func histQuantile(q float64, les, cum []float64) float64 {
	if len(cum) == 0 || cum[len(cum)-1] == 0 {
		return 0
	}
	rank := q * cum[len(cum)-1]
	for i, le := range les {
		if cum[i] < rank {
			continue
		}
		lo, prev := 0.0, 0.0
		if i > 0 {
			lo, prev = les[i-1], cum[i-1]
		}
		if math.IsInf(le, 1) {
			return lo
		}
		if cum[i] == prev {
			return le
		}
		return lo + (le-lo)*(rank-prev)/(cum[i]-prev)
	}
	return les[len(les)-1]
}

// levelRE matches the level of a log line: from slog's JSON handler, from its
// text handler, or from its default logger, which writes the level after the
// log package's date and time.
var levelRE = regexp.MustCompile(`"level":"(\w+)"|\blevel=(\w+)|^(?:\[\S+\] )?(?:\S+Z )?\d{4}/\d\d/\d\d \d\d:\d\d:\d\d(?:\.\d+)? (DEBUG|INFO|WARN|ERROR) `)

// logLevels counts the log lines of each program by level, from the logs
// that the run saved, and keeps some warnings and errors.
func logLevels(dir string, es *errorSummary) {
	for _, program := range programs {
		f, err := os.Open(filepath.Join(dir, "logs", program+".log"))
		if err != nil {
			continue
		}
		counts := map[string]int{}
		sc := bufio.NewScanner(f)
		sc.Buffer(make([]byte, 1<<20), 1<<20)
		for sc.Scan() {
			line := sc.Text()
			m := levelRE.FindStringSubmatch(line)
			if m == nil {
				continue
			}
			level := m[1] + m[2] + m[3]
			counts[level]++
			if (level == "WARN" || level == "ERROR") && len(es.LogSamples) < 40 {
				if len(line) > 400 {
					line = line[:400] + "..."
				}
				es.LogSamples = append(es.LogSamples, line)
			}
		}
		f.Close()
		es.LogLevels[program] = counts
	}
}

// checkWorkers is how many branches each check's controller reconciles at
// once: kube's default, which the checks keep.
const checkWorkers = 4

// waitRE matches a check's warning that a reconcile failed after the results
// endpoint's whole 10-second wait: a 404 for a GitBranch that was gone, from
// builds before the endpoint answered 410, or 503s, on every try, for a
// result that the core program didn't write in time.
var waitRE = regexp.MustCompile(`\btime=(\S+) .*\bkey=(\S+) duration=(\S+) err=".*(Not Found: GitBranch \S+ doesn't exist|the result wasn't written in time)`)

// goneRE matches a check's note that the results endpoint answered 410
// because the GitBranch was gone. The endpoint answers as soon as the API
// server shows that the GitBranch is gone, and the reconcile ends.
var goneRE = regexp.MustCompile(`didn't take a result"? .*\bbranch=(\S+) reason="GitBranch \S+ doesn't exist"`)

// timeRE matches the time of a log line: the time that kubectl logs
// --timestamps adds after the --prefix, the time attribute of slog's text
// handler, or the date and time of the log package, which slog's default
// logger writes through.
var timeRE = regexp.MustCompile(`^(?:\[\S+\] )?(\d{4}-\d\d-\d\dT\S+Z) |\btime=(\S+)|^(?:\[\S+\] )?(\d{4}/\d\d/\d\d \d\d:\d\d:\d\d(?:\.\d+)?) `)

// logTime returns when a program wrote a log line. The log package's times
// are in the container's time zone, which is UTC, and have whole seconds.
func logTime(line string) (time.Time, bool) {
	m := timeRE.FindStringSubmatch(line)
	if m == nil {
		return time.Time{}, false
	}
	layout, value := time.RFC3339Nano, cmp.Or(m[1], m[2])
	if value == "" {
		layout, value = "2006/01/02 15:04:05", m[3]
	}
	t, err := time.Parse(layout, value)
	return t, err == nil
}

// resultWaits finds, from the logs that the run saved, the checks'
// reconciles that failed after the results endpoint's whole timeout, the
// times when they held every worker of a check, and the results that the
// endpoint answered 410 for. landed holds when each GitBranch landed, and
// names each planned branch's repository and branch, by the GitBranch's
// name.
func resultWaits(dir string, start time.Time, landed map[string]time.Time, names map[string]string, cycles []*frontCycle) waitSummary {
	ws := waitSummary{MaxAtOnce: map[string]int{}}
	rel := func(t time.Time) float64 { return r2(secs(t.Sub(start))) }
	landedAt := func(name string) *float64 {
		t, ok := landed[name]
		if !ok {
			return nil
		}
		l := rel(t)
		return &l
	}
	type edge struct {
		t     time.Time
		delta int
	}
	var stalls [][2]time.Time
	for _, program := range programs {
		check, ok := strings.CutPrefix(program, "check-")
		if !ok {
			continue
		}
		f, err := os.Open(filepath.Join(dir, "logs", program+".log"))
		if err != nil {
			continue
		}
		var edges []edge
		sc := bufio.NewScanner(f)
		sc.Buffer(make([]byte, 1<<20), 1<<20)
		for sc.Scan() {
			line := sc.Text()
			if m := goneRE.FindStringSubmatch(line); m != nil {
				if at, ok := logTime(line); ok {
					ws.Gone = append(ws.Gone, goneAnswer{Check: check, Branch: cmp.Or(names[m[1]], m[1]), At: rel(at), Landed: landedAt(m[1])})
				}
				continue
			}
			m := waitRE.FindStringSubmatch(line)
			if m == nil {
				continue
			}
			end, err := time.Parse(time.RFC3339Nano, m[1])
			if err != nil {
				continue
			}
			d, err := time.ParseDuration(m[3])
			if err != nil {
				continue
			}
			name := m[2][strings.LastIndex(m[2], "/")+1:]
			reason := "timeout"
			if strings.HasPrefix(m[4], "Not Found") {
				reason = "gone"
			}
			ws.Waits = append(ws.Waits, resultWait{Check: check, Branch: cmp.Or(names[name], name), Reason: reason, From: rel(end.Add(-d)), To: rel(end), Landed: landedAt(name)})
			edges = append(edges, edge{end.Add(-d), 1}, edge{end, -1})
		}
		f.Close()
		sort.Slice(edges, func(i, j int) bool {
			if !edges[i].t.Equal(edges[j].t) {
				return edges[i].t.Before(edges[j].t)
			}
			return edges[i].delta < edges[j].delta
		})
		n := 0
		var from time.Time
		for _, e := range edges {
			n += e.delta
			if n > ws.MaxAtOnce[check] {
				ws.MaxAtOnce[check] = n
			}
			switch {
			case e.delta > 0 && n == checkWorkers:
				from = e.t
			case e.delta < 0 && n == checkWorkers-1:
				ws.Stalls = append(ws.Stalls, stall{Check: check, From: rel(from), To: rel(e.t)})
				stalls = append(stalls, [2]time.Time{from, e.t})
			}
		}
	}
	sort.Slice(ws.Waits, func(i, j int) bool { return ws.Waits[i].From < ws.Waits[j].From })
	sort.Slice(ws.Stalls, func(i, j int) bool { return ws.Stalls[i].From < ws.Stalls[j].From })
	sort.SliceStable(ws.Gone, func(i, j int) bool { return ws.Gone[i].At < ws.Gone[j].At })

	// Merge the stalls of different checks, so that an overlap counts once.
	sort.Slice(stalls, func(i, j int) bool { return stalls[i][0].Before(stalls[j][0]) })
	var merged [][2]time.Time
	for _, s := range stalls {
		if k := len(merged) - 1; k >= 0 && !s[0].After(merged[k][1]) {
			if s[1].After(merged[k][1]) {
				merged[k][1] = s[1]
			}
			continue
		}
		merged = append(merged, s)
	}
	var total float64
	for _, fc := range cycles {
		if !fc.Busy {
			continue
		}
		from := fc.Landed.Add(-time.Duration(fc.Cycle * float64(time.Second)))
		var overlap float64
		for _, s := range merged {
			lo, hi := s[0], s[1]
			if from.After(lo) {
				lo = from
			}
			if fc.Landed.Before(hi) {
				hi = fc.Landed
			}
			if hi.After(lo) {
				overlap += secs(hi.Sub(lo))
			}
		}
		if overlap > 0 {
			ws.StalledCycles++
			total += overlap
		}
	}
	ws.StalledSeconds = r2(total)
	return ws
}
