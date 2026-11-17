package invocation

import (
	"testing"
	"time"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
)

func TestHitRatio(t *testing.T) {
	for _, tc := range []struct {
		name string
		c    Counts
		want float64
	}{
		{"nothing looked up", Counts{}, -1},
		{"remote cache only", Counts{ActionCacheHits: 3, ActionCacheMisses: 1}, .75},
		{"miss then execute", Counts{ActionCacheHits: 1, ActionCacheMisses: 1, ExecuteRequests: 1}, .5},
		{"execute only", Counts{ExecuteRequests: 4, ExecuteCached: 1, ExecuteMerged: 1}, .5},
	} {
		if got := tc.c.HitRatio(); got != tc.want {
			t.Errorf("%s: HitRatio = %v, want %v", tc.name, got, tc.want)
		}
	}
}

func TestFlushEndsIdleInvocations(t *testing.T) {
	now := time.Unix(1000, 0)
	tr := New(time.Minute)
	tr.now = func() time.Time { return now }
	bazel := &repb.ToolDetails{ToolName: "bazel", ToolVersion: "8.4.2"}

	tr.AddFor(&repb.RequestMetadata{ToolDetails: bazel, ToolInvocationId: "old"}, "a", Counts{ActionCacheHits: 1})
	now = now.Add(30 * time.Second)
	tr.AddFor(&repb.RequestMetadata{ToolDetails: &repb.ToolDetails{ToolName: "ci-substrate-runner"}, ToolInvocationId: "new"}, "b", Counts{RunnerBytesUploaded: 10})
	tr.AddFor(&repb.RequestMetadata{ToolDetails: bazel, ToolInvocationId: "new"}, "b", Counts{ActionCacheMisses: 1})
	tr.AddFor(nil, "a", Counts{ActionCacheHits: 1})

	done := tr.Flush(t.Context(), now.Add(-20*time.Second))
	if len(done) != 1 || done[0].ID != "old" || done[0].ActionCacheHits != 1 {
		t.Fatalf("Flush = %+v, want only the idle invocation with its one hit", done)
	}
	done = tr.Flush(t.Context(), time.Time{})
	if len(done) != 1 {
		t.Fatalf("final Flush = %+v, want the remaining invocation", done)
	}
	s := done[0]
	if s.Tool != "bazel" || s.RunnerBytesUploaded != 10 || s.ActionCacheMisses != 1 || len(s.Instances) != 1 {
		t.Errorf("summary = %+v, want bazel's tool, the runner's bytes, the miss, and one instance", s)
	}

	var nilTracker *Tracker
	nilTracker.AddFor(&repb.RequestMetadata{ToolInvocationId: "x"}, "a", Counts{})
}
