// Package reconcile repairs abandoned placement operations after lease expiry.
package reconcile

import (
	"context"
	"fmt"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
)

type Controller struct {
	Placement placement.Store
	Hosts     *backend.HostSet
}

// RunOnce reconciles expired operation journals. A reachable source remains
// authoritative until placement commit; if the source vanished, a reachable
// prepared target becomes authoritative.
func (c *Controller) RunOnce(ctx context.Context) error {
	records, err := c.Placement.ListRecords(ctx)
	if err != nil {
		return err
	}
	var first error
	now := time.Now()
	for _, record := range records {
		if record.Operation.Kind == "" || record.LeaseUntilUnix > now.UnixNano() {
			continue
		}
		if err := c.reconcile(ctx, record); err != nil && first == nil {
			first = err
		}
	}
	return first
}

func (c *Controller) reconcile(ctx context.Context, record placement.Record) error {
	guard, err := placement.AcquireRecoveryGuard(ctx, c.Placement, record, "reconcile", placement.DefaultLeaseTTL)
	if err != nil {
		return err
	}
	finished := false
	defer func() {
		if !finished {
			guard.Abandon()
		}
	}()
	op := record.Operation
	source, sourceOK := c.Hosts.Get(op.SourceHost)
	target, targetOK := c.Hosts.Get(op.TargetHost)
	if !sourceOK || !targetOK {
		return fmt.Errorf("operation %s/%s awaits authoritative source and target inventory", record.User, record.App)
	}

	for _, gen := range op.Generations {
		sourceStatus, sourceFound, err := source.StatusContext(guard.Context(), record.User, record.App, gen)
		if err != nil {
			return err
		}
		targetStatus, targetFound, err := target.StatusContext(guard.Context(), record.User, record.App, gen)
		if err != nil {
			return err
		}
		if targetFound {
			if targetStatus.State == "running" {
				if err := target.SetNoIdleContext(guard.Context(), record.User, record.App, gen, false); err != nil {
					return err
				}
				if err := target.SleepContext(guard.Context(), record.User, record.App, gen); err != nil {
					return err
				}
			}
			if err := target.EvictContext(guard.Context(), record.User, record.App, gen); err != nil {
				return err
			}
		}
		if !sourceFound && targetFound {
			var adoptErr error
			if op.SourceEpoch != "" {
				_, adoptErr = source.AdoptForcedContext(guard.Context(), record.User, record.App, gen, op.SourceEpoch)
			} else {
				_, adoptErr = source.AdoptContext(guard.Context(), record.User, record.App, gen)
			}
			if adoptErr != nil {
				return adoptErr
			}
		} else if sourceFound && sourceStatus.State == "running" {
			// Source already owns the live copy.
		}
	}
	return release(guard, &finished)
}

func release(guard *placement.Guard, finished *bool) error {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	if err := guard.Release(ctx); err != nil {
		return err
	}
	*finished = true
	return nil
}
