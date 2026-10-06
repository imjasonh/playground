package main

import (
	"fmt"
	"maps"
	"slices"
	"strings"
	"testing"
)

func TestBuildPlan(t *testing.T) {
	for _, c := range []struct {
		scenario string
		n, repos int
		poll     string
		// repos are the plan's repositories, each as name/landing/gotest/poll.
		wantRepos []string
		wantKinds map[string]int
		stagger   string
		timeout   string
	}{
		{scenario: "clean", poll: "2s", wantRepos: []string{"app//true/2s"}, wantKinds: map[string]int{kindClean: 20}, timeout: "45m"},
		{scenario: "clean", repos: 3, n: 5, poll: "2s", wantRepos: []string{"a//true/2s", "b//true/2s", "c//true/2s"}, wantKinds: map[string]int{kindClean: 15}, timeout: "45m"},
		{scenario: "nogotest", n: 100, poll: "2s", wantRepos: []string{"app//false/2s"}, wantKinds: map[string]int{kindClean: 100}, timeout: "45m"},
		{scenario: "big", poll: "2s", wantRepos: []string{"app//true/2s"}, wantKinds: map[string]int{kindClean: 100}, timeout: "120m"},
		{
			scenario: "mixed", poll: "2s", wantRepos: []string{"app//true/2s"}, timeout: "45m",
			wantKinds: map[string]int{kindConflict: 4, kindBigRisk: 1, kindModRisk: 1, kindFailing: 2, kindUnformatted: 7, kindClean: 9},
		},
		{scenario: "landing", poll: "2s", wantRepos: []string{"rebase/Rebase/true/2s", "squash/Squash/true/2s"}, wantKinds: map[string]int{kindMulti: 20}, timeout: "45m"},
		{scenario: "parallel", poll: "2s", wantRepos: []string{"a//true/2s", "b//true/2s", "c//true/2s", "d//true/2s"}, wantKinds: map[string]int{kindClean: 40}, timeout: "45m"},
		// poll30 leaves pollInterval out whatever -poll says.
		{scenario: "poll30", poll: "2s", wantRepos: []string{"app//false/"}, wantKinds: map[string]int{kindClean: 8}, stagger: "7s", timeout: "45m"},
	} {
		t.Run(c.scenario, func(t *testing.T) {
			p, err := buildPlan(c.scenario, c.n, c.repos, c.poll)
			if err != nil {
				t.Fatal(err)
			}
			if !strings.HasPrefix(p.NS, "stress-"+c.scenario+"-") {
				t.Errorf("namespace = %q, want stress-%s-SUFFIX", p.NS, c.scenario)
			}
			var repos []string
			for _, r := range p.Repos {
				repos = append(repos, fmt.Sprintf("%s/%s/%v/%s", r.Name, r.Landing, r.Gotest, r.Poll))
			}
			if !slices.Equal(repos, c.wantRepos) {
				t.Errorf("repos = %q, want %q", repos, c.wantRepos)
			}
			kinds := map[string]int{}
			seen := map[string]bool{}
			for _, b := range p.Branches {
				kinds[b.Kind]++
				if b.Name != "c/"+b.ID || p.repo(b.Repo).Name != b.Repo {
					t.Errorf("branch %+v doesn't match its id or repository", b)
				}
				if seen[b.Repo+" "+b.Name] {
					t.Errorf("branch %s %s is planned twice", b.Repo, b.Name)
				}
				seen[b.Repo+" "+b.Name] = true
			}
			if !maps.Equal(kinds, c.wantKinds) {
				t.Errorf("kinds = %v, want %v", kinds, c.wantKinds)
			}
			if p.Stagger != c.stagger || p.Timeout != c.timeout || !p.Warmup {
				t.Errorf("stagger %q, timeout %q, warm-up %v; want %q, %q, true", p.Stagger, p.Timeout, p.Warmup, c.stagger, c.timeout)
			}
		})
	}
	if _, err := buildPlan("chaos", 0, 0, "2s"); err == nil {
		t.Error("buildPlan of an unknown scenario succeeded")
	}
}

// TestMixedPlan checks that mixed plans the same branches each time, so
// that runs compare, and pairs its conflicting branches.
func TestMixedPlan(t *testing.T) {
	p1, err := buildPlan("mixed", 0, 0, "2s")
	if err != nil {
		t.Fatal(err)
	}
	p2, err := buildPlan("mixed", 0, 0, "2s")
	if err != nil {
		t.Fatal(err)
	}
	if !slices.Equal(p1.Branches, p2.Branches) {
		t.Errorf("two mixed plans differ:\n%+v\n%+v", p1.Branches, p2.Branches)
	}
	var pairs []int
	for _, b := range p1.Branches {
		if b.Kind == kindConflict {
			pairs = append(pairs, b.Pair)
		} else if b.Pair != 0 {
			t.Errorf("%s is %s, but has pair %d", b.Name, b.Kind, b.Pair)
		}
	}
	if !slices.Equal(pairs, []int{1, 1, 2, 2}) {
		t.Errorf("conflict pairs = %v, want [1 1 2 2]", pairs)
	}
	base := baseFiles()
	for _, k := range pairs {
		if _, ok := base[conflictFile(k)]; !ok {
			t.Errorf("main doesn't start with %s, the line of pair %d", conflictFile(k), k)
		}
	}
}

func TestGitRepository(t *testing.T) {
	type check struct {
		Name    string
		MayPush bool
	}
	checksOf := func(obj map[string]any) ([]check, string, map[string]any) {
		spec := obj["spec"].(map[string]any)
		merge := spec["branches"].([]map[string]any)[0]["merge"].(map[string]any)
		var cs []check
		for _, c := range merge["checks"].([]map[string]any) {
			mayPush, _ := c["mayPush"].(bool)
			cs = append(cs, check{c["name"].(string), mayPush})
		}
		return cs, merge["when"].(string), spec
	}

	cs, when, spec := checksOf(gitRepository("stress-x", repoPlan{Name: "rebase", Landing: "Rebase", Gotest: true, Poll: "2s"}, "http://git/x.git"))
	want := []check{{"base", true}, {"gofmt", true}, {"risk", false}, {"approval", false}, {"gotest", false}}
	if !slices.Equal(cs, want) {
		t.Errorf("checks = %v, want %v", cs, want)
	}
	if !strings.Contains(when, "checks.gotest.passed") || !strings.Contains(when, `checks.risk.outputs.level == "low" || checks.approval.passed`) {
		t.Errorf("when = %q, want gotest and approval of high risk", when)
	}
	merge := spec["branches"].([]map[string]any)[0]["merge"].(map[string]any)
	if spec["pollInterval"] != "2s" || merge["landing"] != "Rebase" || merge["deleteMergedBranches"] != true || spec["url"] != "http://git/x.git" {
		t.Errorf("spec = %v", spec)
	}

	cs, when, spec = checksOf(gitRepository("stress-x", repoPlan{Name: "app"}, "http://git/y.git"))
	if len(cs) != 4 || strings.Contains(when, "gotest") {
		t.Errorf("without gotest: checks = %v, when = %q", cs, when)
	}
	merge = spec["branches"].([]map[string]any)[0]["merge"].(map[string]any)
	if _, ok := spec["pollInterval"]; ok {
		t.Errorf("pollInterval = %v, want it left out", spec["pollInterval"])
	}
	if _, ok := merge["landing"]; ok {
		t.Errorf("landing = %v, want it left out", merge["landing"])
	}
}
