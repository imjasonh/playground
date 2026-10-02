package main

import (
	"fmt"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
)

func TestMain(m *testing.M) { e2e.Main(m) }

func newNamespace(created time.Time, ttl string) *Namespace {
	ns := &Namespace{Object: kube.Meta("preview-1234", nil)}
	ns.CreationTimestamp = created
	if ttl != "" {
		ns.Annotations = map[string]string{ttlAnnotation: ttl}
	}
	return ns
}

func TestRequeuesUntilExpiry(t *testing.T) {
	now := time.Date(2026, 10, 2, 12, 0, 0, 0, time.UTC)
	ns := newNamespace(now.Add(-time.Hour), "72h")
	ctx, rec := kube.Fake(t.Context(), ns)
	if err := (janitor{now: func() time.Time { return now }}).Reconcile(ctx, ns); err != nil {
		t.Fatal(err)
	}
	if got := rec.RequeueAfter(); got != 71*time.Hour {
		t.Errorf("RequeueAfter = %v, want 71h", got)
	}
	if deleted := kube.Deleted[Namespace](rec); len(deleted) != 0 {
		t.Errorf("deleted %v before expiry", deleted)
	}
}

func TestDeletesExpiredNamespace(t *testing.T) {
	now := time.Date(2026, 10, 2, 12, 0, 0, 0, time.UTC)
	ns := newNamespace(now.Add(-73*time.Hour), "72h")
	ctx, rec := kube.Fake(t.Context(), ns)
	if err := (janitor{now: func() time.Time { return now }}).Reconcile(ctx, ns); err != nil {
		t.Fatal(err)
	}
	if deleted := kube.Deleted[Namespace](rec); len(deleted) != 1 || deleted[0].Name != "preview-1234" {
		t.Errorf("deleted = %+v", deleted)
	}
}

func TestBadTTLIsPermanent(t *testing.T) {
	for _, ttl := range []string{"three days", "-1h", "0s"} {
		ns := newNamespace(time.Now(), ttl)
		ctx, _ := kube.Fake(t.Context(), ns)
		if err := (janitor{now: time.Now}).Reconcile(ctx, ns); !kube.IsPermanent(err) {
			t.Errorf("ttl %q: err = %v, want a permanent error", ttl, err)
		}
	}
}

func TestEndToEnd(t *testing.T) {
	c := e2e.Client(t)
	e2e.Run(t, &kube.Manager{Name: "janitor-e2e"}, kube.For[Namespace](janitor{now: time.Now}, kube.Named("janitor")))
	ctx := t.Context()

	create := func(ttl string) string {
		name := e2e.Namespace(t, c)
		patch := fmt.Sprintf(`{"metadata":{"annotations":{%q:%q}}}`, ttlAnnotation, ttl)
		if err := c.Patch(ctx, client.Path("v1", "namespaces", "", name), client.MergePatch, nil, []byte(patch), nil); err != nil {
			t.Fatal(err)
		}
		return name
	}
	deleting := func(name string) (bool, error) {
		var ns Namespace
		if err := e2e.Get(ctx, c, client.Path("v1", "namespaces", "", name), &ns); err != nil {
			return false, err
		}
		return ns.Deleting(), nil
	}

	t.Log("A namespace is deleted when its time to live runs out, and not before.")
	short, long := create("4s"), create("1h")
	start := time.Now()
	e2e.Eventually(t, 15*time.Second, func() error {
		if d, err := deleting(short); err != nil || !d {
			return fmt.Errorf("namespace %s isn't being deleted (err %v)", short, err)
		}
		return nil
	})
	// Namespaces are created with one-second timestamps, so allow a second.
	if elapsed := time.Since(start); elapsed < 2*time.Second {
		t.Errorf("namespace was deleted after %v, before its time to live", elapsed)
	}
	if d, err := deleting(long); err != nil || d {
		t.Errorf("namespace with a 1h time to live is being deleted (err %v)", err)
	}
}
