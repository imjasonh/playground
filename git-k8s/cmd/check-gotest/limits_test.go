package main

import (
	"flag"
	"maps"
	"slices"
	"testing"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/kube/k8s"
)

// startedSpec returns the spec of the test Pod that the check starts.
func startedSpec(t *testing.T) PodSpec {
	t.Helper()
	b, repo := branch()
	return started(t, b, repo).Spec
}

// volumeSizes returns the size limit of each emptyDir volume in spec.
func volumeSizes(spec PodSpec) map[string]string {
	sizes := map[string]string{}
	for _, v := range spec.Volumes {
		if v.EmptyDir != nil {
			sizes[v.Name] = v.EmptyDir.SizeLimit
		}
	}
	return sizes
}

// resourcesOf returns the resources of each container in spec.
func resourcesOf(spec PodSpec) map[string]Resources {
	got := map[string]Resources{}
	for _, c := range slices.Concat(spec.InitContainers, spec.Containers) {
		if c.Resources != nil {
			got[c.Name] = *c.Resources
		}
	}
	return got
}

func equalResources(a, b Resources) bool {
	return maps.Equal(a.Requests, b.Requests) && maps.Equal(a.Limits, b.Limits)
}

// limited returns the resources of a container that requests cpu, memory,
// and storage, and can use up to cpuLimit, memoryLimit, and disk. An empty
// cpuLimit means no CPU limit.
func limited(memory, memoryLimit, storage, disk, cpuLimit k8s.Quantity) Resources {
	r := Resources{
		Requests: map[string]k8s.Quantity{"cpu": "100m", "memory": memory, "ephemeral-storage": storage},
		Limits:   map[string]k8s.Quantity{"memory": memoryLimit, "ephemeral-storage": disk},
	}
	if cpuLimit != "" {
		r.Limits["cpu"] = cpuLimit
	}
	return r
}

func TestLimitsTestPods(t *testing.T) {
	spec := startedSpec(t)
	if got, want := volumeSizes(spec), map[string]string{"src": "2Gi", "tmp": "4Gi"}; !maps.Equal(got, want) {
		t.Errorf("volume sizes = %v, want %v", got, want)
	}
	t.Log("Each container's ephemeral-storage limit covers the volumes and 256Mi of logs.")
	want := map[string]Resources{
		"fetch": limited("128Mi", "1Gi", "1Gi", "6400Mi", "2"),
		"test":  limited("256Mi", "2Gi", "1Gi", "6400Mi", "2"),
	}
	if got := resourcesOf(spec); !maps.EqualFunc(got, want, equalResources) {
		t.Errorf("resources = %+v, want %+v", got, want)
	}

	t.Run("flags", func(t *testing.T) {
		defer func(src, cache size, cpu int) { sourceSize, goCacheSize, *cpuLimit = src, cache, cpu }(sourceSize, goCacheSize, *cpuLimit)
		for name, value := range map[string]string{"source-size": "10Gi", "go-cache-size": "6Gi", "cpu-limit": "0"} {
			if err := flag.Set(name, value); err != nil {
				t.Fatal(err)
			}
		}
		spec := startedSpec(t)
		if got, want := volumeSizes(spec), map[string]string{"src": "10Gi", "tmp": "6Gi"}; !maps.Equal(got, want) {
			t.Errorf("with -source-size=10Gi and -go-cache-size=6Gi, volume sizes = %v, want %v", got, want)
		}
		want := map[string]Resources{
			"fetch": limited("128Mi", "1Gi", "1Gi", "16640Mi", ""),
			"test":  limited("256Mi", "2Gi", "1Gi", "16640Mi", ""),
		}
		if got := resourcesOf(spec); !maps.EqualFunc(got, want, equalResources) {
			t.Errorf("with -cpu-limit=0, resources = %+v, want %+v without a CPU limit", got, want)
		}

		t.Log("A container never requests more ephemeral storage than its limit.")
		sourceSize, goCacheSize = 100<<20, 100<<20
		want = map[string]Resources{
			"fetch": limited("128Mi", "1Gi", "456Mi", "456Mi", ""),
			"test":  limited("256Mi", "2Gi", "456Mi", "456Mi", ""),
		}
		if got := resourcesOf(startedSpec(t)); !maps.EqualFunc(got, want, equalResources) {
			t.Errorf("with volumes of 100Mi, resources = %+v, want %+v", got, want)
		}
	})

	t.Run("go-cache", func(t *testing.T) {
		withGoCache(t)
		spec := startedSpec(t)
		if got, want := volumeSizes(spec), map[string]string{"src": "2Gi", "tmp": "4Gi", "go-cache": "4Gi"}; !maps.Equal(got, want) {
			t.Errorf("with -go-cache, volume sizes = %v, want %v", got, want)
		}
		fetch, test := limited("128Mi", "1Gi", "1Gi", "10496Mi", "2"), limited("256Mi", "2Gi", "1Gi", "10496Mi", "2")
		want := map[string]Resources{"fetch": fetch, "build": test, "upload": fetch, "test": test}
		if got := resourcesOf(spec); !maps.EqualFunc(got, want, equalResources) {
			t.Errorf("with -go-cache, resources = %+v, want %+v", got, want)
		}
	})
}

func TestSizeFlags(t *testing.T) {
	for name, want := range map[string]string{"source-size": "2Gi", "go-cache-size": "4Gi", "cpu-limit": "2"} {
		if got := flag.Lookup(name).DefValue; got != want {
			t.Errorf("-%s defaults to %s, want %s", name, got, want)
		}
	}
	s := size(1)
	for _, v := range []string{"", "lots", "0", "1.5Gi", "-1Gi", "2Pi"} {
		if err := s.Set(v); err == nil || s != 1 {
			t.Errorf("Set(%q) = %v and the size is %d, want an error and no change", v, err, s)
		}
	}
	if err := s.Set("10Gi"); err != nil || s != 10<<30 || s.String() != "10Gi" {
		t.Errorf("Set(10Gi) = %v and the size is %s", err, s.String())
	}
}

func TestSizes(t *testing.T) {
	for s, want := range map[string]int64{
		"2Gi": 2 << 30, "500M": 500e6, "1": 1, "1k": 1000, "64Ki": 64 << 10, "3Ti": 3 << 40, "2097151Ti": 2097151 << 40,
		"": 0, "0": 0, "-1Gi": 0, "+1Gi": 0, "1.5Gi": 0, "2GB": 0, "2gi": 0, "Gi": 0, "1e9": 0, "2Pi": 0, "2097152Ti": 0,
	} {
		if got := parseSize(s); got != want {
			t.Errorf("parseSize(%q) = %d, want %d", s, got, want)
		}
	}
	for n, want := range map[int64]string{1000: "1000", 2048: "2Ki", 1536 << 20: "1536Mi", 1 << 30: "1Gi", 5 << 40: "5Ti", 1 << 50: "1024Ti"} {
		if got := formatSize(n); got != want {
			t.Errorf("formatSize(%d) = %q, want %q", n, got, want)
		}
	}
}

func TestReportsEviction(t *testing.T) {
	reason := `Usage of EmptyDir volume "src" exceeds the limit "2Gi". `
	for _, evicted := range []*Pod{
		pod("Failed", &Terminated{ExitCode: 137, Reason: "Error", FinishedAt: time.Now()}, nil),
		pod("Failed", &Terminated{}, &Terminated{ExitCode: 137, Message: "=== RUN   TestBig"}),
	} {
		evicted.Status.Reason, evicted.Status.Message = "Evicted", reason
		b, repo := branch()
		named(b, 1)
		reconcileWith(t, b, repo, evicted)
		want := "Pod " + evicted.Name + ` was evicted: Usage of EmptyDir volume "src" exceeds the limit "2Gi".`
		if res := b.Status.Checks.Result; res.State != gitk8s.Failed || res.Message != want || res.Outputs["pod"] != evicted.Name {
			t.Errorf("result = %+v, want Failed with the message %q, without fetching again", res, want)
		}
	}
}
