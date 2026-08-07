package snapshotd

import "testing"

func TestStagingGuardEnforcesWeightGlobalAndAgentBounds(t *testing.T) {
	t.Parallel()
	guard, err := NewStagingGuard(StagingLimits{
		MaxBytes: 101, MaxConcurrent: 2, MaxPerAgent: 1, MaxRequestBytes: 80,
	})
	if err != nil {
		t.Fatal(err)
	}
	first, reason := guard.TryAcquire("agent-a\x001", 60)
	if first == nil || reason != "" {
		t.Fatalf("first admission = %v reason=%q", first, reason)
	}
	if lease, reason := guard.TryAcquire("agent-a\x001", 10); lease != nil || reason != "per_agent" {
		t.Fatalf("same agent admission = %v reason=%q", lease, reason)
	}
	if lease, reason := guard.TryAcquire("agent-b\x002", 50); lease != nil || reason != "bytes" {
		t.Fatalf("weighted admission = %v reason=%q", lease, reason)
	}
	second, reason := guard.TryAcquire("agent-b\x002", 40)
	if second == nil || reason != "" {
		t.Fatalf("second admission = %v reason=%q", second, reason)
	}
	if lease, reason := guard.TryAcquire("agent-c\x003", 1); lease != nil || reason != "concurrency" {
		t.Fatalf("global admission = %v reason=%q", lease, reason)
	}
	first.Release()
	first.Release()
	second.Release()
	usage := guard.Usage()
	if usage.Active != 0 || usage.UsedBytes != 0 {
		t.Fatalf("usage after release: %+v", usage)
	}
}

func TestStagingGuardRetainsFailedCleanupBytesWithoutHoldingConcurrency(t *testing.T) {
	t.Parallel()
	guard, err := NewStagingGuard(StagingLimits{
		MaxBytes: 100, MaxConcurrent: 1, MaxPerAgent: 1, MaxRequestBytes: 80,
	})
	if err != nil {
		t.Fatal(err)
	}
	failed, reason := guard.TryAcquire("agent-a\x001", 60)
	if failed == nil || reason != "" {
		t.Fatalf("failed-cleanup admission = %v reason=%q", failed, reason)
	}
	failed.Abandon()
	failed.Release() // The terminal accounting decision is idempotent.
	usage := guard.Usage()
	if usage.Active != 0 || usage.UsedBytes != 60 || usage.RetainedBytes != 60 {
		t.Fatalf("usage after failed cleanup: %+v", usage)
	}
	if lease, reason := guard.TryAcquire("agent-b\x002", 41); lease != nil || reason != "bytes" {
		t.Fatalf("residual byte admission = %v reason=%q", lease, reason)
	}
	next, reason := guard.TryAcquire("agent-b\x002", 40)
	if next == nil || reason != "" {
		t.Fatalf("remaining capacity admission = %v reason=%q", next, reason)
	}
	next.Release()
	usage = guard.Usage()
	if usage.Active != 0 || usage.UsedBytes != 60 || usage.RetainedBytes != 60 {
		t.Fatalf("final usage: %+v", usage)
	}
}
