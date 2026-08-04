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
	guard, err := placement.AcquireGuard(ctx, c.Placement, record.User, record.App, "reconcile", placement.DefaultLeaseTTL)
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
	switch {
	case !sourceOK && !targetOK:
		return fmt.Errorf("operation %s/%s has no reachable source or target", record.User, record.App)
	case !sourceOK && targetOK:
		commitCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		err := guard.Commit(commitCtx, op.TargetHost)
		cancel()
		if err != nil {
			return err
		}
		finished = true
		return nil
	case sourceOK && !targetOK:
		if err := source.SetCordoned(ctx, false); err != nil {
			return err
		}
		return release(guard, &finished)
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
			if _, err := source.AdoptForcedContext(guard.Context(), record.User, record.App, gen); err != nil {
				return err
			}
		} else if sourceFound && sourceStatus.State == "running" {
			// Source already owns the live copy.
		}
	}
	if err := source.SetCordoned(guard.Context(), false); err != nil {
		return err
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
