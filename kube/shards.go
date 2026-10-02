package kube

import (
	"context"
	"crypto/rand"
	"encoding/hex"
	"fmt"
	"os"
	"time"

	"github.com/imjasonh/playground/kube/internal/client"
)

// Leader election timing, matching client-go's defaults.
var (
	leaseDuration = 15 * time.Second
	renewDeadline = 10 * time.Second
	retryPeriod   = 2 * time.Second
)

const microTime = "2006-01-02T15:04:05.000000Z07:00"

type lease struct {
	APIVersion string `json:"apiVersion"`
	Kind       string `json:"kind"`
	Metadata   struct {
		Name            string `json:"name"`
		Namespace       string `json:"namespace"`
		ResourceVersion string `json:"resourceVersion,omitempty"`
	} `json:"metadata"`
	Spec struct {
		HolderIdentity       string `json:"holderIdentity,omitempty"`
		LeaseDurationSeconds int32  `json:"leaseDurationSeconds,omitempty"`
		AcquireTime          string `json:"acquireTime,omitempty"`
		RenewTime            string `json:"renewTime,omitempty"`
		LeaseTransitions     int32  `json:"leaseTransitions,omitempty"`
	} `json:"spec"`
}

type elector struct {
	c        *client.Client
	ns, name string
	identity string

	// observed is the last holder and renew time seen, and observedAt the
	// local time it was first seen. Judging expiry by local observation
	// time makes the election immune to clock skew between replicas.
	observed   string
	observedAt time.Time
}

func (e *elector) path() string {
	return client.Path("coordination.k8s.io/v1", "leases", e.ns, e.name)
}

// tryAcquireOrRenew takes the lease if it's free or expired, or renews it
// if this replica holds it. It reports whether this replica holds it now.
func (e *elector) tryAcquireOrRenew(ctx context.Context) (bool, error) {
	now := time.Now()
	stamp := now.UTC().Format(microTime)
	var l lease
	err := e.c.Get(ctx, e.path(), &l)
	if client.IsNotFound(err) {
		l.APIVersion, l.Kind = "coordination.k8s.io/v1", "Lease"
		l.Metadata.Name, l.Metadata.Namespace = e.name, e.ns
		l.Spec.HolderIdentity = e.identity
		l.Spec.LeaseDurationSeconds = int32(leaseDuration / time.Second)
		l.Spec.AcquireTime, l.Spec.RenewTime = stamp, stamp
		err := e.c.Create(ctx, client.Path("coordination.k8s.io/v1", "leases", e.ns, ""), l, nil)
		if client.IsAlreadyExists(err) {
			return false, nil
		}
		return err == nil, err
	}
	if err != nil {
		return false, err
	}
	if record := l.Spec.HolderIdentity + "@" + l.Spec.RenewTime; record != e.observed {
		e.observed, e.observedAt = record, now
	}
	held := l.Spec.HolderIdentity != "" && l.Spec.HolderIdentity != e.identity
	duration := time.Duration(l.Spec.LeaseDurationSeconds) * time.Second
	if held && e.observedAt.Add(duration).After(now) {
		return false, nil
	}
	if l.Spec.HolderIdentity != e.identity {
		l.Spec.LeaseTransitions++
		l.Spec.AcquireTime = stamp
	}
	l.Spec.HolderIdentity = e.identity
	l.Spec.LeaseDurationSeconds = int32(leaseDuration / time.Second)
	l.Spec.RenewTime = stamp
	if err := e.c.Update(ctx, e.path(), l, nil); err != nil {
		if client.IsConflict(err) {
			return false, nil
		}
		return false, err
	}
	return true, nil
}

func (e *elector) release() {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	var l lease
	if err := e.c.Get(ctx, e.path(), &l); err != nil || l.Spec.HolderIdentity != e.identity {
		return
	}
	l.Spec.HolderIdentity = ""
	l.Spec.LeaseDurationSeconds = 1
	l.Spec.RenewTime = time.Now().UTC().Format(microTime)
	_ = e.c.Update(ctx, e.path(), l, nil)
}

// lead blocks until this replica holds the lease, then keeps renewing it in
// the background. If renewal fails for longer than renewDeadline, it cancels
// ctx with errLostLease. When ctx is done, it releases the lease so another
// replica can take over at once.
func (m *Manager) lead(ctx context.Context, cancel context.CancelCauseFunc) error {
	ns := m.LeaseNamespace
	if ns == "" {
		ns = m.client.Namespace
	}
	if ns == "" {
		ns = "default"
	}
	host, _ := os.Hostname()
	suffix := make([]byte, 4)
	_, _ = rand.Read(suffix)
	e := &elector{c: m.client, ns: ns, name: labelValue(m.Name), identity: host + "_" + hex.EncodeToString(suffix)}
	log := m.log.With("lease", ns+"/"+e.name, "identity", e.identity)
	log.Info("waiting to become leader")
	for {
		ok, err := e.tryAcquireOrRenew(ctx)
		if err != nil {
			log.Warn("leader election failed", "err", err)
		}
		if ok {
			break
		}
		select {
		case <-ctx.Done():
			return nil
		case <-time.After(retryPeriod):
		}
	}
	log.Info("became leader")
	go func() {
		defer e.release()
		last := time.Now()
		t := time.NewTicker(retryPeriod)
		defer t.Stop()
		for {
			select {
			case <-ctx.Done():
				return
			case <-t.C:
			}
			rctx, rcancel := context.WithTimeout(ctx, retryPeriod)
			ok, err := e.tryAcquireOrRenew(rctx)
			rcancel()
			if ok {
				last = time.Now()
				continue
			}
			if ctx.Err() != nil {
				return
			}
			if time.Since(last) > renewDeadline {
				log.Error("lost leadership", "err", err)
				cancel(fmt.Errorf("%w %s/%s", errLostLease, ns, e.name))
				return
			}
		}
	}()
	return nil
}
