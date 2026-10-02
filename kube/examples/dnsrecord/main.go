// Command dnsrecord manages records in a DNS provider outside Kubernetes,
// the way external-dns, Crossplane, and AWS Controllers for Kubernetes
// manage cloud resources:
//
//	apiVersion: examples.kube.imjasonh.github.io/v1
//	kind: DNSRecord
//	metadata:
//	  name: www
//	spec:
//	  zone: example.com
//	  name: www
//	  type: A
//	  value: 192.0.2.10
//
// It shows the external-resource pattern: observe the real state with the
// provider's API, change it only when it differs from the desired state,
// clean up in Finalize before the object goes away, report an invalid spec
// as a permanent error instead of retrying it, and check for drift on a
// timer because a provider can't be watched. Renaming a record deletes the
// old one, which status remembers.
//
// The provider here keeps records in memory. Implement Provider for Route 53,
// Cloud DNS, or another service to use a real one.
package main

import (
	"context"
	"flag"
	"fmt"
	"net/netip"
	"regexp"
	"sync"
	"time"

	"github.com/imjasonh/playground/kube"
)

// DNSRecord is one DNS record.
type DNSRecord struct {
	kube.Object `kube:"group=examples.kube.imjasonh.github.io,shortName=dns"`
	Spec        DNSRecordSpec   `json:"spec"`
	Status      DNSRecordStatus `json:"status,omitzero"`
}

// DNSRecordSpec is the record to publish.
type DNSRecordSpec struct {
	Zone  string `json:"zone" doc:"DNS zone that holds the record, for example example.com."`
	Name  string `json:"name" pattern:"^[a-z0-9]([-a-z0-9]*[a-z0-9])?$" doc:"Name within the zone."`
	Type  string `json:"type" kube:"enum=A|AAAA|CNAME|TXT,column=Type"`
	Value string `json:"value" kube:"minLength=1,column=Value"`
	TTL   int32  `json:"ttl,omitempty" kube:"min=30,max=86400,default=300"`
}

// DNSRecordStatus is what the provider has.
type DNSRecordStatus struct {
	// Published is the record the controller last wrote, so a rename can
	// delete the old record and deletion knows what to remove.
	Published          *RecordKey       `json:"published,omitempty"`
	FQDN               string           `json:"fqdn,omitempty" kube:"column=FQDN"`
	ObservedGeneration int64            `json:"observedGeneration,omitempty"`
	Conditions         []kube.Condition `json:"conditions,omitempty"`
}

// RecordKey identifies a record in a provider.
type RecordKey struct {
	FQDN string `json:"fqdn"`
	Type string `json:"type"`
}

// Record is a record as a provider stores it.
type Record struct {
	RecordKey
	Value string
	TTL   int32
}

// Provider is a DNS service.
type Provider interface {
	// Get returns the record, or nil if it doesn't exist.
	Get(ctx context.Context, key RecordKey) (*Record, error)
	Upsert(ctx context.Context, r Record) error
	// Delete removes the record. Deleting a missing record succeeds.
	Delete(ctx context.Context, key RecordKey) error
}

type reconciler struct {
	provider Provider
	// drift is how often to compare the provider's record with the spec.
	// It's a pointer so a flag can set it after the controller is built.
	drift *time.Duration
}

var hostnameRE = regexp.MustCompile(`^([a-z0-9]([-a-z0-9]*[a-z0-9])?\.)+[a-z]{2,}\.?$`)

func validate(s DNSRecordSpec) error {
	switch s.Type {
	case "A", "AAAA":
		addr, err := netip.ParseAddr(s.Value)
		if err != nil || addr.Is4() != (s.Type == "A") {
			return fmt.Errorf("%q is not an IPv%s address", s.Value, map[string]string{"A": "4", "AAAA": "6"}[s.Type])
		}
	case "CNAME":
		if !hostnameRE.MatchString(s.Value) {
			return fmt.Errorf("%q is not a hostname", s.Value)
		}
	}
	return nil
}

func (r *reconciler) Reconcile(ctx context.Context, rec *DNSRecord) error {
	key := RecordKey{FQDN: rec.Spec.Name + "." + rec.Spec.Zone, Type: rec.Spec.Type}
	rec.Status.FQDN = key.FQDN
	ready := kube.Condition{Type: "Ready", Status: kube.False}
	defer func() { kube.SetCondition(&rec.Status.Conditions, ready) }()

	if err := validate(rec.Spec); err != nil {
		ready.Reason, ready.Message = "InvalidSpec", err.Error()
		return kube.Permanent(err)
	}
	if old := rec.Status.Published; old != nil && *old != key {
		if err := r.provider.Delete(ctx, *old); err != nil {
			ready.Reason = "ProviderError"
			return fmt.Errorf("deleting renamed record %s %s: %w", old.Type, old.FQDN, err)
		}
		rec.Status.Published = nil
	}
	want := Record{RecordKey: key, Value: rec.Spec.Value, TTL: rec.Spec.TTL}
	got, err := r.provider.Get(ctx, key)
	if err != nil {
		ready.Reason = "ProviderError"
		return err
	}
	if got == nil || *got != want {
		if err := r.provider.Upsert(ctx, want); err != nil {
			ready.Reason = "ProviderError"
			return err
		}
	}
	rec.Status.Published = &key
	ready.Status, ready.Reason = kube.True, "Published"
	kube.RequeueAfter(ctx, *r.drift)
	return nil
}

func (r *reconciler) Finalize(ctx context.Context, rec *DNSRecord) error {
	if p := rec.Status.Published; p != nil {
		return r.provider.Delete(ctx, *p)
	}
	return nil
}

// memory is a Provider that keeps records in memory.
type memory struct {
	mu      sync.Mutex
	records map[RecordKey]Record
	// fail, when set, makes every call fail, to simulate an outage.
	fail error
}

func (m *memory) Get(_ context.Context, key RecordKey) (*Record, error) {
	m.mu.Lock()
	defer m.mu.Unlock()
	if m.fail != nil {
		return nil, m.fail
	}
	if r, ok := m.records[key]; ok {
		return &r, nil
	}
	return nil, nil
}

func (m *memory) Upsert(_ context.Context, r Record) error {
	m.mu.Lock()
	defer m.mu.Unlock()
	if m.fail != nil {
		return m.fail
	}
	if m.records == nil {
		m.records = map[RecordKey]Record{}
	}
	m.records[r.RecordKey] = r
	return nil
}

func (m *memory) Delete(_ context.Context, key RecordKey) error {
	m.mu.Lock()
	defer m.mu.Unlock()
	if m.fail != nil {
		return m.fail
	}
	delete(m.records, key)
	return nil
}

func main() {
	drift := flag.Duration("drift-check", 10*time.Minute, "how often to compare provider records with specs")
	kube.Main(kube.For[DNSRecord](&reconciler{provider: &memory{}, drift: drift}))
}
