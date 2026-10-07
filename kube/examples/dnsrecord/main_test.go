package main

import (
	"errors"
	"fmt"
	"slices"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
)

func TestMain(m *testing.M) { e2e.Main(m) }

var errOutage = errors.New("provider unavailable")

func (m *memory) setFail(err error) {
	m.mu.Lock()
	m.fail = err
	m.mu.Unlock()
}

func (m *memory) value(key RecordKey) string {
	m.mu.Lock()
	defer m.mu.Unlock()
	return m.records[key].Value
}

func newRecord(name, typ, value string) *DNSRecord {
	r := &DNSRecord{Spec: DNSRecordSpec{Zone: "example.com", Name: name, Type: typ, Value: value, TTL: 300}}
	r.Name, r.Namespace = name, "default"
	return r
}

func newReconciler(p Provider) *reconciler {
	d := 10 * time.Minute
	return &reconciler{provider: p, drift: &d}
}

func TestPublishesRecord(t *testing.T) {
	p := &memory{}
	rec := newRecord("www", "A", "192.0.2.10")
	ctx, out := kube.Fake(t.Context(), rec)
	if err := newReconciler(p).Reconcile(ctx, rec); err != nil {
		t.Fatal(err)
	}
	key := RecordKey{FQDN: "www.example.com", Type: "A"}
	if p.value(key) != "192.0.2.10" {
		t.Errorf("provider records = %+v", p.records)
	}
	if rec.Status.Published == nil || *rec.Status.Published != key {
		t.Errorf("published = %+v", rec.Status.Published)
	}
	if c := kube.FindCondition(rec.Status.Conditions, "Ready"); c.Status != kube.True {
		t.Errorf("Ready = %+v", c)
	}
	if out.RequeueAfter() != 10*time.Minute {
		t.Errorf("RequeueAfter = %v, want the drift check interval", out.RequeueAfter())
	}
}

func TestInvalidSpecIsPermanent(t *testing.T) {
	for _, tc := range []struct{ typ, value string }{{"A", "not-an-ip"}, {"A", "2001:db8::1"}, {"AAAA", "192.0.2.1"}, {"CNAME", "under_score"}} {
		p := &memory{}
		rec := newRecord("www", tc.typ, tc.value)
		ctx, _ := kube.Fake(t.Context(), rec)
		if err := newReconciler(p).Reconcile(ctx, rec); !kube.IsPermanent(err) {
			t.Errorf("%s %s: err = %v, want a permanent error", tc.typ, tc.value, err)
		}
		if c := kube.FindCondition(rec.Status.Conditions, "Ready"); c.Reason != "InvalidSpec" {
			t.Errorf("%s %s: Ready = %+v", tc.typ, tc.value, c)
		}
		if len(p.records) != 0 {
			t.Errorf("%s %s: provider has records %+v", tc.typ, tc.value, p.records)
		}
	}
}

func TestRenameDeletesOldRecord(t *testing.T) {
	old := RecordKey{FQDN: "www.example.com", Type: "A"}
	p := &memory{records: map[RecordKey]Record{old: {RecordKey: old, Value: "192.0.2.10", TTL: 300}}}
	rec := newRecord("api", "A", "192.0.2.10")
	rec.Status.Published = &old
	ctx, _ := kube.Fake(t.Context(), rec)
	if err := newReconciler(p).Reconcile(ctx, rec); err != nil {
		t.Fatal(err)
	}
	if _, ok := p.records[old]; ok {
		t.Error("old record still exists")
	}
	if p.value(RecordKey{FQDN: "api.example.com", Type: "A"}) != "192.0.2.10" {
		t.Errorf("records = %+v", p.records)
	}
}

func TestFinalizeDeletesPublishedRecord(t *testing.T) {
	key := RecordKey{FQDN: "www.example.com", Type: "A"}
	p := &memory{records: map[RecordKey]Record{key: {RecordKey: key}}}
	rec := newRecord("www", "A", "192.0.2.10")
	rec.Status.Published = &key
	ctx, _ := kube.Fake(t.Context(), rec)
	if err := newReconciler(p).Finalize(ctx, rec); err != nil {
		t.Fatal(err)
	}
	if len(p.records) != 0 {
		t.Errorf("records = %+v", p.records)
	}
}

func TestOutageIsRetried(t *testing.T) {
	p := &memory{fail: errOutage}
	rec := newRecord("www", "A", "192.0.2.10")
	ctx, _ := kube.Fake(t.Context(), rec)
	err := newReconciler(p).Reconcile(ctx, rec)
	if !errors.Is(err, errOutage) || kube.IsPermanent(err) {
		t.Errorf("err = %v, want the outage, not permanent", err)
	}
}

func TestEndToEnd(t *testing.T) {
	c := e2e.Client(t)
	p := &memory{}
	drift := time.Second
	e2e.Run(t, &kube.Manager{Name: "dnsrecord-e2e"}, kube.For[DNSRecord](&reconciler{provider: p, drift: &drift}))
	ctx := t.Context()
	ns := e2e.Namespace(t, c)
	group := "examples.kube.imjasonh.github.io/v1"
	path := func(name string) string { return client.Path(group, "dnsrecords", ns, name) }
	create := func(name, typ, value string) {
		t.Helper()
		e2e.Eventually(t, 30*time.Second, func() error {
			return c.Create(ctx, path(""), map[string]any{
				"apiVersion": group, "kind": "DNSRecord", "metadata": map[string]any{"name": name},
				"spec": map[string]any{"zone": "example.com", "name": name, "type": typ, "value": value},
			}, nil)
		})
	}
	status := func(name string) (*DNSRecord, error) {
		var r DNSRecord
		return &r, e2e.Get(ctx, c, path(name), &r)
	}
	conditionIs := func(name, typ, want, reason string) error {
		r, err := status(name)
		if err != nil {
			return err
		}
		if cond := kube.FindCondition(r.Status.Conditions, typ); cond == nil || cond.Status != want || (reason != "" && cond.Reason != reason) {
			return fmt.Errorf("%s condition = %+v, want %s %s", typ, cond, want, reason)
		}
		return nil
	}
	www := RecordKey{FQDN: "www.example.com", Type: "A"}
	providerHas := func(key RecordKey, value string) error {
		if got := p.value(key); got != value {
			return fmt.Errorf("provider %s = %q, want %q", key.FQDN, got, value)
		}
		return nil
	}

	t.Log("Creating a DNSRecord publishes it, marks it Ready, and adds a finalizer.")
	create("www", "A", "192.0.2.10")
	e2e.Eventually(t, 10*time.Second, func() error {
		if err := providerHas(www, "192.0.2.10"); err != nil {
			return err
		}
		r, err := status("www")
		if err != nil {
			return err
		}
		if !slices.Contains(r.Finalizers, kube.FinalizerName("dnsrecord-e2e-dnsrecord")) {
			return fmt.Errorf("finalizers = %v", r.Finalizers)
		}
		if r.Spec.TTL != 300 {
			return fmt.Errorf("ttl = %d, want the CRD default 300", r.Spec.TTL)
		}
		return conditionIs("www", "Ready", kube.True, "Published")
	})

	t.Log("A change made directly in the provider is reverted by the drift check.")
	if err := p.Upsert(ctx, Record{RecordKey: www, Value: "198.51.100.1", TTL: 300}); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 10*time.Second, func() error { return providerHas(www, "192.0.2.10") })

	t.Log("During an outage, Synced reports the error; after it, the change goes through.")
	p.setFail(errOutage)
	if err := c.Patch(ctx, path("www"), client.MergePatch, nil, []byte(`{"spec":{"value":"192.0.2.20"}}`), nil); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 10*time.Second, func() error {
		r, err := status("www")
		if err != nil {
			return err
		}
		synced := kube.FindCondition(r.Status.Conditions, "Synced")
		if synced == nil || synced.Status != kube.False || synced.Message != errOutage.Error() {
			return fmt.Errorf("Synced = %+v", synced)
		}
		return nil
	})
	p.setFail(nil)
	e2e.Eventually(t, 10*time.Second, func() error {
		if err := providerHas(www, "192.0.2.20"); err != nil {
			return err
		}
		return conditionIs("www", "Synced", kube.True, "Reconciled")
	})

	t.Log("Renaming a record deletes the old one.")
	if err := c.Patch(ctx, path("www"), client.MergePatch, nil, []byte(`{"spec":{"name":"api"}}`), nil); err != nil {
		t.Fatal(err)
	}
	api := RecordKey{FQDN: "api.example.com", Type: "A"}
	e2e.Eventually(t, 10*time.Second, func() error {
		if err := providerHas(api, "192.0.2.20"); err != nil {
			return err
		}
		return providerHas(www, "")
	})

	t.Log("An invalid spec is reported as a permanent error and never reaches the provider.")
	create("bad", "A", "not-an-ip")
	e2e.Eventually(t, 10*time.Second, func() error {
		if err := conditionIs("bad", "Synced", kube.False, "PermanentError"); err != nil {
			return err
		}
		return conditionIs("bad", "Ready", kube.False, "InvalidSpec")
	})
	if err := providerHas(RecordKey{FQDN: "bad.example.com", Type: "A"}, ""); err != nil {
		t.Error(err)
	}

	t.Log("Deleting the DNSRecord deletes the provider's record before the object goes away.")
	if err := c.Delete(ctx, path("www"), client.DeleteOptions{}); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 10*time.Second, func() error {
		if err := providerHas(api, ""); err != nil {
			return err
		}
		return e2e.Gone(ctx, c, path("www"))
	})
}
