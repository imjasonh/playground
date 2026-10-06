package main

import (
	"cmp"
	"encoding/json"
	"flag"
	"fmt"
	"maps"
	"os"
	"path/filepath"
	"slices"
	"sort"
	"strings"
	"time"
)

// f1 formats v with one decimal, without "-0.0".
func f1(v float64) string { return strings.Replace(fmt.Sprintf("%.1f", v), "-0.0", "0.0", 1) }

func distRow(name string, d dist) string {
	return fmt.Sprintf("| %s | %d | %s | %s | %s | %s |\n", name, d.N, f1(d.P50), f1(d.P90), f1(d.Max), f1(d.Mean))
}

func sortedKeys[V any](m map[string]V) []string { return slices.Sorted(maps.Keys(m)) }

func countList(m map[string]int) string {
	var parts []string
	for _, k := range sortedKeys(m) {
		parts = append(parts, fmt.Sprintf("%s %d", k, m[k]))
	}
	if len(parts) == 0 {
		return "none"
	}
	return strings.Join(parts, ", ")
}

func summaryMarkdown(s *summary) string {
	var b strings.Builder
	p := func(format string, args ...any) { fmt.Fprintf(&b, format, args...) }
	p("# Scenario %s\n\n", s.Scenario)
	p("Namespace `%s`: %d repositories, %d branches (%s), pollInterval %s, gotest in the gate: %v", s.Namespace, s.Repos, s.N, countList(s.Kinds), s.Poll, s.Gotest)
	if s.Landing != "" {
		p(", landing %s", s.Landing)
	}
	p(". The first push finished at %s.\n\n", s.Start.Format(time.RFC3339Nano))
	var images []string
	for _, program := range programs {
		if image, ok := s.Images[program+"/"+program]; ok {
			images = append(images, fmt.Sprintf("%s `%s`", program, shortDigest(image)))
		}
	}
	if len(images) > 0 {
		p("Image digests: %s.\n\n", strings.Join(images, ", "))
	}

	p("| Measure | Value |\n|---|---|\n")
	p("| Landed | %d of %d |\n", s.Landed, s.N)
	p("| Time to push every branch | %s s |\n", f1(s.PushSpan))
	p("| First landing after the first push | %s s |\n", f1(s.FirstLanding))
	p("| Drain: first push to last landing | %s s |\n", f1(s.Drain))
	p("| Landings per minute, overall | %s |\n", f1(s.PerMin))
	p("| Landings per minute, first to last landing | %s |\n", f1(s.SteadyPerMin))
	p("| Landings per minute, middle 80%% of landings | %s |\n", f1(s.MiddlePerMin))
	p("| Median time between landings in a repository | %s s |\n", f1(s.MedianGap))
	p("| Push to landed, p50 / p90 / max | %s / %s / %s s |\n", f1(s.Latency.P50), f1(s.Latency.P90), f1(s.Latency.Max))
	p("| Landed to the git server's main, p50 / max | %s / %s s |\n", f1(s.Sync.P50), f1(s.Sync.Max))
	p("| Most branches in a queue | %d |\n", s.MaxQueue)
	p("| Test Pods: total, most at once, mean at once | %d, %d, %s |\n", s.TestPods, s.MaxTestPods, f1(s.AvgTestPods))
	p("| Node CPU cores, mean / p90 / max (the host has %d CPUs; %s before the burst) | %s / %s / %s |\n", s.CPU.Cores, f1(s.CPU.Before), f1(s.CPU.Avg), f1(s.CPU.P90), f1(s.CPU.Max))
	p("| Host CPU cores in use, mean, by the node and everything else | %s |\n", f1(s.CPU.HostAvg))
	p("| Node memory, max | %.0f MiB |\n", s.CPU.MemMax)
	if len(s.Warmup) > 0 {
		var parts []string
		for _, k := range sortedKeys(s.Warmup) {
			parts = append(parts, fmt.Sprintf("%s %s s", k, f1(s.Warmup[k])))
		}
		p("| Warm-up branch, push to landed | %s |\n", strings.Join(parts, ", "))
	}

	if len(s.PerRepo) > 1 {
		p("\n## Repositories\n\n| Repository | Landed | First landing (s) | Last landing (s) | Per minute, overall | First to last | Middle 80%% | Median gap (s) | Max queue | p50 / p90 latency (s) |\n|---|---|---|---|---|---|---|---|---|---|\n")
		for _, r := range s.PerRepo {
			p("| %s | %d of %d | %s | %s | %s | %s | %s | %s | %d | %s / %s |\n", r.Repo, r.Landed, r.N, f1(r.FirstLanding), f1(r.LastLanding), f1(r.PerMin), f1(r.SteadyPerMin), f1(r.MiddlePerMin), f1(r.MedianGap), r.MaxQueue, f1(r.Latency.P50), f1(r.Latency.P90))
		}
	}

	p("\n## Where each branch's time went\n\nSeconds per landed branch. Pickup ends when the GitBranch exists, checks when the branch first joins the queue, queue counts time behind other branches, front counts time at the front, and out counts time after the branch left the queue until it joined again.\n\n")
	p("| Phase | n | p50 | p90 | max | mean |\n|---|---|---|---|---|---|\n")
	for _, name := range []string{"pickup", "checks", "queue", "front", "out"} {
		b.WriteString(distRow(name, s.Phases[name]))
	}
	b.WriteString(distRow("total", s.Latency))
	if len(s.LatencyByKind) > 1 {
		p("\n| Kind | n | p50 | p90 | max | mean |\n|---|---|---|---|---|---|\n")
		for _, k := range sortedKeys(s.LatencyByKind) {
			b.WriteString(distRow(k, s.LatencyByKind[k]))
		}
	}

	c := s.Cycle
	p("\n## Front of the queue\n\n%d landings came from a busy queue, with the next branch already queued at the last landing; the base check merged the parent into %d of them. Seconds:\n\n", c.N, c.Merged)
	p("| Segment | n | p50 | p90 | max | mean |\n|---|---|---|---|---|---|\n")
	b.WriteString(distRow("landing to landing", c.Cycle))
	b.WriteString(distRow("handoff: last landing to first in the queue", c.Handoff))
	b.WriteString(distRow("base check merges the parent, until the merge is listed", c.Merge))
	b.WriteString(distRow("checks pass for the head that lands", c.Checks))
	b.WriteString(distRow("merge controller lands", c.Land))
	b.WriteString(distRow("base check's push returns, after the merge is listed", c.PushLag))
	if len(c.ByDepth) > 0 {
		p("\nBy the parent's queue length when the cycle started (median seconds):\n\n| Queue length | Cycles | Landing to landing, p50 | Merges | Base merge, p50 |\n|---|---|---|---|---|\n")
		for _, d := range c.ByDepth {
			p("| %s | %d | %s | %d | %s |\n", d.Depth, d.Cycle.N, f1(d.Cycle.P50), d.Merge.N, f1(d.Merge.P50))
		}
	}
	if len(c.CheckAt) > 0 {
		p("\nEach check's pass, in seconds after the head that landed was listed:\n\n| Check | n | p50 | p90 | max | mean |\n|---|---|---|---|---|---|\n")
		for _, k := range sortedKeys(c.CheckAt) {
			b.WriteString(distRow(k, c.CheckAt[k]))
		}
	}
	if len(c.Pod) > 0 {
		p("\nThe test Pod for the head that landed (created: seconds after the head was listed; start: creation to first container; then each container; whole seconds):\n\n| Step | n | p50 | p90 | max | mean |\n|---|---|---|---|---|---|\n")
		for _, k := range sortedKeys(c.Pod) {
			b.WriteString(distRow(k, c.Pod[k]))
		}
	}

	p("\n## Work\n\n| Measure | Count |\n|---|---|\n")
	p("| Fixes that checks pushed | %s |\n", countList(s.Fixes))
	landed := float64(max(1, s.Landed))
	var results []string
	for _, k := range sortedKeys(s.Results) {
		results = append(results, fmt.Sprintf("%s %d (%s per landing)", k, s.Results[k], f1(float64(s.Results[k])/landed)))
	}
	p("| Check results for distinct heads and parent heads | %s |\n", strings.Join(results, ", "))
	p("| Developer pushes, including fixes and merges | %d |\n", s.DevPushes)
	p("| Times branches joined a queue | %d |\n", s.Joins)
	p("| Test Pods | %d (%s per landing) |\n", s.TestPods, f1(float64(s.TestPods)/landed))
	if len(s.PodPhases) > 0 {
		p("\nAll test Pods, seconds (container times have whole seconds):\n\n| Step | n | p50 | p90 | max | mean |\n|---|---|---|---|---|---|\n")
		for _, k := range sortedKeys(s.PodPhases) {
			b.WriteString(distRow(k, s.PodPhases[k]))
		}
	}

	p("\n## CPU by group\n\nCores during the burst, from the Pods' cgroups:\n\n| Group | Mean | Max |\n|---|---|---|\n")
	groups := sortedKeys(s.CPU.Groups)
	sort.SliceStable(groups, func(i, j int) bool { return s.CPU.Groups[groups[i]].Avg > s.CPU.Groups[groups[j]].Avg })
	for _, g := range groups {
		p("| %s | %.2f | %.2f |\n", g, s.CPU.Groups[g].Avg, s.CPU.Groups[g].Max)
	}

	p("\n## Reconciles during the burst\n\nDurations in milliseconds, estimated from histogram buckets; max queue from scrapes every 10 seconds.\n\n| Program | Controller | Reconciles | Results | Mean | p50 | p90 | p99 | Max queue |\n|---|---|---|---|---|---|---|---|---|\n")
	for _, r := range s.Reconciles {
		var res []string
		for _, k := range sortedKeys(r.Results) {
			if r.Results[k] > 0 {
				res = append(res, fmt.Sprintf("%s %.0f", k, r.Results[k]))
			}
		}
		p("| %s | %s | %.0f | %s | %s | %s | %s | %s | %.0f |\n", r.Program, r.Controller, r.Total, strings.Join(res, ", "), f1(r.Mean), f1(r.P50), f1(r.P90), f1(r.P99), r.QueueMax)
	}
	if len(s.GoCache) > 0 {
		var parts []string
		for _, k := range sortedKeys(s.GoCache) {
			parts = append(parts, fmt.Sprintf("`%s` %.0f", k, s.GoCache[k]))
		}
		p("\ngo-cache requests: %s.\n", strings.Join(parts, ", "))
	}

	if w := s.Waits; len(w.Waits) > 0 {
		p("\n## Results that waited for the endpoint's timeout\n\n")
		p("The results endpoint waits up to 10 seconds for a check's result to show in the GitBranch, and the check's worker waits too; each check has %d workers. These reconciles failed after such waits. Reason `gone` is a 404 for a GitBranch that was gone, which builds before the endpoint answered 410 sent only after the whole wait. Reason `timeout` means that each of the check's tries got a 503, because the core program didn't write the result in time; a 503 that a later try got past doesn't show in the logs. Seconds after the first push:\n\n", checkWorkers)
		p("| Check | Branch | Reason | Reconcile started | Ended | Branch landed |\n|---|---|---|---|---|---|\n")
		for _, x := range w.Waits {
			landed := "not seen"
			if x.Landed != nil {
				landed = f1(*x.Landed)
			}
			p("| %s | %s | %s | %s | %s | %s |\n", x.Check, x.Branch, cmp.Or(x.Reason, "gone"), f1(x.From), f1(x.To), landed)
		}
		var most []string
		for _, k := range sortedKeys(w.MaxAtOnce) {
			most = append(most, fmt.Sprintf("%s %d", k, w.MaxAtOnce[k]))
		}
		p("\nMost of these reconciles from one check at once: %s.\n", strings.Join(most, ", "))
		if len(w.Stalls) > 0 {
			p("\nEvery worker of a check waited:\n\n")
			for _, st := range w.Stalls {
				p("- %s, from %s to %s s (%s s)\n", st.Check, f1(st.From), f1(st.To), f1(st.To-st.From))
			}
			p("\n%d busy front-of-queue cycles overlapped those times, by %s s in all.\n", w.StalledCycles, f1(w.StalledSeconds))
		}
	}
	if gone := s.Waits.Gone; len(gone) > 0 {
		byCheck := map[string]int{}
		for _, g := range gone {
			byCheck[g.Check]++
		}
		p("\n## Results for deleted branches\n\n")
		p("The results endpoint answered 410 Gone for %d results whose GitBranches were gone (%s). It answers as soon as it sees that the GitBranch is gone, and the check's reconcile ends, so these requests don't hold a worker for the endpoint's 10-second wait. Seconds after the first push:\n\n", len(gone), countList(byCheck))
		p("| Check | Branch | Answered | Branch landed |\n|---|---|---|---|\n")
		for _, g := range gone {
			landed := "not seen"
			if g.Landed != nil {
				landed = f1(*g.Landed)
			}
			p("| %s | %s | %s | %s |\n", g.Check, g.Branch, f1(g.At), landed)
		}
	}

	e := s.Errors
	p("\n## Errors and anomalies\n\n")
	p("- Merged reasons, by how many branches saw each: %s.\n", countList(e.Reasons))
	p("- Check results in state Error: %d, of which %d failed to push a fix.\n", len(e.ErrorResults), e.PushRejections)
	for _, x := range e.ErrorResults {
		p("  - %s\n", x)
	}
	p("- Warning events: %s.\n", countList(e.WarningEvents))
	for _, x := range e.WarningSamples {
		p("  - %s\n", x)
	}
	if len(e.ReconcileErrors) > 0 {
		var parts []string
		for _, k := range sortedKeys(e.ReconcileErrors) {
			parts = append(parts, fmt.Sprintf("%s %.0f", k, e.ReconcileErrors[k]))
		}
		p("- Reconciles that returned errors: %s.\n", strings.Join(parts, ", "))
	} else {
		p("- Reconciles that returned errors: none.\n")
	}
	for _, x := range e.Diverged {
		p("- Diverged: %s\n", x)
	}
	for _, x := range e.Restarts {
		p("- %s\n", x)
	}
	for _, x := range e.ActionErrors {
		p("- Harness action failed: %s\n", x)
	}
	var levels []string
	for _, prog := range sortedKeys(e.LogLevels) {
		levels = append(levels, fmt.Sprintf("%s (%s)", prog, countList(e.LogLevels[prog])))
	}
	p("- Log lines by level: %s.\n", strings.Join(levels, "; "))
	for _, x := range e.LogSamples {
		p("  - `%s`\n", strings.ReplaceAll(x, "`", "'"))
	}
	if len(s.Stuck) > 0 {
		p("\nBranches that didn't land:\n\n")
		for _, x := range s.Stuck {
			p("- %s\n", x)
		}
	}

	p("\n## Verification\n\n")
	if v := s.Verify; v != nil {
		p("Checked:\n\n")
		for _, x := range v.Checked {
			p("- %s\n", x)
		}
		p("\nFixer trailers on main: %s. Commits that checks pushed, by trailer: %s.\n\n", countList(v.FixerTrailers), countList(v.PushedFixes))
		if err := v.err(); err != nil {
			p("Problems:\n\n```\n%v\n```\n", err)
		} else {
			p("No problems.\n")
		}
	} else {
		p("The run didn't write verify.json.\n")
	}
	return b.String()
}

func branchesTSV(s *summary, stats []*branchStats) string {
	var b strings.Builder
	b.WriteString("repo\tbranch\tkind\tpushed_s\tlanded_s\ttotal\tpickup\tchecks\tqueue\tfront\tout\tsync\tjoins\tfronts\tdev_pushes\tfixes\ttest_pods\tresults\treasons\tlast\n")
	for _, st := range stats {
		off := func(t time.Time) string {
			if t.IsZero() {
				return ""
			}
			return f1(secs(t.Sub(s.Start)))
		}
		var res []string
		for _, k := range sortedKeys(st.Results) {
			res = append(res, fmt.Sprintf("%s=%d", k, st.Results[k]))
		}
		var fixes []string
		for _, k := range sortedKeys(st.Fixes) {
			fixes = append(fixes, fmt.Sprintf("%s=%d", k, st.Fixes[k]))
		}
		fmt.Fprintf(&b, "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%d\t%d\t%d\t%s\t%d\t%s\t%s\t%s\n",
			st.Repo, st.Branch, st.Kind, off(st.Pushed), off(st.Landed), f1(st.Total), f1(st.Pickup), f1(st.Checks), f1(st.Queue),
			f1(st.Front), f1(st.Out), f1(st.Sync), st.Joins, st.Fronts, st.DevPushes, strings.Join(fixes, ","), st.TestPods,
			strings.Join(res, ","), strings.Join(st.Reasons, ","), st.Last)
	}
	return b.String()
}

func frontsTSV(s *summary, cycles []*frontCycle) string {
	var b strings.Builder
	b.WriteString("repo\tbranch\tlanded_s\tbusy\tdepth\tmerged\tcycle\thandoff\tmerge\tchecks\tland\tpush_lag\tcheck_pass_after_listing\ttest_pod\n")
	for _, c := range cycles {
		var at, pod []string
		for _, k := range sortedKeys(c.CheckAt) {
			at = append(at, fmt.Sprintf("%s=%s", k, f1(c.CheckAt[k])))
		}
		for _, k := range sortedKeys(c.Pod) {
			pod = append(pod, fmt.Sprintf("%s=%s", k, f1(c.Pod[k])))
		}
		fmt.Fprintf(&b, "%s\t%s\t%s\t%v\t%d\t%v\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n", c.Repo, c.Branch, f1(secs(c.Landed.Sub(s.Start))), c.Busy, c.Depth, c.Merged,
			f1(c.Cycle), f1(c.Handoff), f1(c.Merge), f1(c.Checks), f1(c.Land), f1(c.PushLag), strings.Join(at, ","), strings.Join(pod, ","))
	}
	return b.String()
}

// timeline renders a run's records as text, with times in seconds after
// the first push: what the harness did, each change to a GitBranch, events,
// the git server's main, test Pods' phases, and every fifth second's queue
// lengths.
func timeline(run *runData, start time.Time) string {
	var b strings.Builder
	ns := run.plan.NS
	off := func(t time.Time) string { return fmt.Sprintf("%+9.3f", secs(t.Sub(start))) }
	lastLine := map[string]string{}
	podPhase := map[string]string{}
	ticks := 0
	for _, rc := range run.recs {
		switch rc.Kind {
		case "note":
			fmt.Fprintf(&b, "%s note    %s\n", off(rc.T), rc.note)
		case "action":
			a := rc.action
			line := fmt.Sprintf("%s %s %s", a.Repo, a.Branch, short(a.Head))
			if a.Note != "" {
				line += " (" + a.Note + ")"
			}
			if a.Err != "" {
				line += " error: " + a.Err
			}
			fmt.Fprintf(&b, "%s %-7s %s\n", off(rc.T), a.Action, line)
		case "branch":
			br := rc.branch
			if br.NS != ns {
				continue
			}
			var line string
			if br.Parent == "" {
				q := br.Queue
				more := ""
				if len(q) > 4 {
					q, more = q[:4], fmt.Sprintf(" +%d", len(br.Queue)-4)
				}
				line = fmt.Sprintf("%s %s head=%s queue=%d [%s%s]", br.Repo, br.Branch, short(br.Head), len(br.Queue), strings.Join(q, " "), more)
			} else {
				merged := ""
				if br.Merged != nil {
					merged = br.Merged.Reason
					if br.Merged.Reason == "Queued" || br.Merged.Reason == "WaitingForChecks" {
						msg := br.Merged.Message
						if len(msg) > 90 {
							msg = msg[:90] + "..."
						}
						merged += "(" + msg + ")"
					}
				}
				line = fmt.Sprintf("%s %s head=%s parent=%s pos=%d %s checks=[%s]", br.Repo, br.Branch, short(br.Head), short(br.ParentHead), position(br), merged, summarizeChecks(br))
				if br.Approve != "" {
					line += " approve=" + short(br.Approve)
				}
			}
			if br.Type == "DELETED" {
				line += " DELETED"
			}
			key := br.Repo + "/" + br.Branch
			if lastLine[key] == line {
				continue
			}
			lastLine[key] = line
			fmt.Fprintf(&b, "%s branch  %s\n", off(rc.T), line)
		case "event":
			e := rc.event
			if e.NS != ns || e.Type != "ADDED" {
				continue
			}
			fmt.Fprintf(&b, "%s event   %s %s %s (%s, at %s): %s\n", off(rc.T), e.EvType, e.Reason, e.Object, e.Controller, off(evTime(rc)), e.Note)
		case "ext":
			fmt.Fprintf(&b, "%s ext     %s %s %s\n", off(rc.T), strings.TrimPrefix(rc.ext.Repo, ns+"-"), rc.ext.Ref, short(rc.ext.SHA))
		case "pod":
			pr := rc.pod
			if pr.NS != ns || pr.App != "test" {
				continue
			}
			phase := pr.Phase
			if pr.Type == "DELETED" {
				phase = "Deleted"
			}
			if podPhase[pr.UID] == phase {
				continue
			}
			podPhase[pr.UID] = phase
			var cs []string
			for _, c := range append(slices.Clone(pr.Init), pr.Main...) {
				cs = append(cs, c.Name+"="+c.State)
			}
			fmt.Fprintf(&b, "%s pod     %s owner=%s %s %s\n", off(rc.T), pr.Name, pr.Owner, phase, strings.Join(cs, " "))
		case "tick":
			ticks++
			if ticks%5 != 0 {
				continue
			}
			var parts []string
			for _, k := range sortedKeys(rc.tick.Parents) {
				parts = append(parts, fmt.Sprintf("%s=%d", strings.TrimPrefix(k, ns+"/"), rc.tick.Parents[k].Queue))
			}
			fmt.Fprintf(&b, "%s tick    queues %s, test Pods %d, open branches %d\n", off(rc.T), strings.Join(parts, " "), rc.tick.Pods, len(rc.tick.Branches))
		}
	}
	return b.String()
}

// reportCmd writes Markdown tables that compare runs, from their
// summary.json files.
func reportCmd(args []string) error {
	fs := flag.NewFlagSet("report", flag.ExitOnError)
	out := fs.String("out", "", "file to write, or standard output")
	_ = fs.Parse(args)
	runs := map[string]*summary{}
	for _, dir := range fs.Args() {
		data, err := os.ReadFile(filepath.Join(dir, "summary.json"))
		if err != nil {
			return err
		}
		s := new(summary)
		if err := json.Unmarshal(data, s); err != nil {
			return fmt.Errorf("%s: %w", dir, err)
		}
		runs[dir] = s
	}
	report := comparison(fs.Args(), runs)
	if *out == "" {
		fmt.Print(report)
		return nil
	}
	return os.WriteFile(*out, []byte(report), 0o644)
}

// comparison renders two tables, with a row for each run directory in
// dirs: throughput and latency, then errors, waits, and what ran.
func comparison(dirs []string, runs map[string]*summary) string {
	var b strings.Builder
	b.WriteString("| Run | Repos × branches | Poll | gotest | Drain (s) | Landings/min overall | First to last | Middle 80% | Median gap (s) | Push to landed p50 / p90 / max (s) | Pickup p50 (s) | Checks p50 (s) | Queue p50 (s) | Front p50 (s) | Busy cycle p50 (s) | Base merges | gofmt fixes | Test Pods | Max queue | Node CPU mean / max | Landed |\n")
	b.WriteString("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|\n")
	for _, dir := range dirs {
		s := runs[dir]
		perRepo := s.N
		if s.Repos > 0 {
			perRepo = s.N / s.Repos
		}
		fmt.Fprintf(&b, "| %s | %d × %d | %s | %v | %s | %s | %s | %s | %s | %s / %s / %s | %s | %s | %s | %s | %s | %d | %d | %d | %d | %s / %s | %d of %d |\n",
			filepath.Base(dir), s.Repos, perRepo, s.Poll, s.Gotest, f1(s.Drain), f1(s.PerMin), f1(s.SteadyPerMin), f1(s.MiddlePerMin), f1(s.MedianGap),
			f1(s.Latency.P50), f1(s.Latency.P90), f1(s.Latency.Max), f1(s.Phases["pickup"].P50), f1(s.Phases["checks"].P50),
			f1(s.Phases["queue"].P50), f1(s.Phases["front"].P50), f1(s.Cycle.Cycle.P50), s.Fixes["base"], s.Fixes["gofmt"], s.TestPods, s.MaxQueue,
			f1(s.CPU.Avg), f1(s.CPU.Max), s.Landed, s.N)
	}
	b.WriteString("\n| Run | git-k8s image | Check results in Error | Reconciles that returned errors | Results that waited for the endpoint's timeout | 410 answers for deleted branches | Busy cycles that overlapped a stall | Host CPU mean |\n")
	b.WriteString("|---|---|---|---|---|---|---|---|\n")
	for _, dir := range dirs {
		s := runs[dir]
		var reconcileErrors float64
		for _, n := range s.Errors.ReconcileErrors {
			reconcileErrors += n
		}
		image := "unknown"
		if ref, ok := s.Images["git-k8s/git-k8s"]; ok {
			image = "`" + shortDigest(ref) + "`"
		}
		fmt.Fprintf(&b, "| %s | %s | %d | %.0f | %d | %d | %d (%s s) | %s |\n", filepath.Base(dir), image, len(s.Errors.ErrorResults), reconcileErrors,
			len(s.Waits.Waits), len(s.Waits.Gone), s.Waits.StalledCycles, f1(s.Waits.StalledSeconds), f1(s.CPU.HostAvg))
	}
	return b.String()
}
