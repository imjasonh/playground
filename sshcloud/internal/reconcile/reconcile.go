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
	Placement  placement.Store
	Hosts      *backend.HostSet
	Tombstones backend.InstanceTombstones
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
	switch op.Kind {
	case "ensure":
		return c.reconcileEnsure(guard, record, &finished)
	case "stop":
		return c.reconcileStop(guard, record, &finished)
	case "migrate", "drain":
		return c.reconcileMove(guard, record, &finished)
	default:
		return fmt.Errorf("operation %s/%s has unsupported recovery kind %q", record.User, record.App, op.Kind)
	}
}

func (c *Controller) reconcileEnsure(guard *placement.Guard, record placement.Record, finished *bool) error {
	target, targetGone, err := c.participant(
		guard.Context(), record.Operation.TargetHost, record.Operation.TargetInstanceID,
	)
	if err != nil {
		return err
	}
	if targetGone {
		if record.HostID != "" {
			return fmt.Errorf(
				"ensure operation %s/%s lost its placed host; explicit hard-loss recovery is required",
				record.User, record.App,
			)
		}
		return release(guard, finished)
	}
	if target == nil {
		return fmt.Errorf("ensure operation %s/%s awaits target inventory", record.User, record.App)
	}
	found := 0
	for _, gen := range record.Operation.Generations {
		expected, expectedFound := generationByID(record.Operation.Desired, gen)
		if !expectedFound || expected.SSHHostPublicKey == "" {
			if err := target.StopContext(guard.Context(), record.User, record.App, gen); err != nil {
				return fmt.Errorf("remove unpinned ensured generation %s: %w", gen, err)
			}
			continue
		}
		status, ok, err := target.StatusContext(guard.Context(), record.User, record.App, gen)
		if err != nil {
			return err
		}
		switch {
		case !ok && expected.State == "sleeping":
			if _, err := target.RegisterSleeping(guard.Context(), record.User, record.App, gen); err != nil {
				return fmt.Errorf("register desired sleeping generation %s: %w", gen, err)
			}
			status, ok, err = target.StatusContext(guard.Context(), record.User, record.App, gen)
			if err != nil {
				return err
			}
		case ok && status.State == "running" && expected.State == "sleeping":
			if err := target.SetNoIdleContext(guard.Context(), record.User, record.App, gen, false); err != nil {
				return err
			}
			if err := target.SleepContext(guard.Context(), record.User, record.App, gen); err != nil {
				return fmt.Errorf("sleep unexpectedly running generation %s: %w", gen, err)
			}
			status, ok, err = target.StatusContext(guard.Context(), record.User, record.App, gen)
			if err != nil {
				return err
			}
		}
		expectedState := expected.State
		if expectedState == "" {
			expectedState = "running"
		}
		if ok && status.State == expectedState &&
			status.SSHHostPublicKey == expected.SSHHostPublicKey {
			found++
		} else if ok {
			return fmt.Errorf(
				"ensure operation %s/%s generation %s is %s with an unexpected SSH host identity",
				record.User, record.App, gen, status.State,
			)
		}
	}
	switch {
	case found == len(record.Operation.Generations):
		identityComplete := len(record.Operation.Desired) != 0
		for _, generation := range record.Operation.Desired {
			if generation.SSHHostPublicKey == "" {
				identityComplete = false
				break
			}
		}
		if !identityComplete {
			for _, gen := range record.Operation.Generations {
				if err := target.StopContext(guard.Context(), record.User, record.App, gen); err != nil {
					return fmt.Errorf("remove unpinned ensured generation %s: %w", gen, err)
				}
			}
			return release(guard, finished)
		}
		actual, err := actualInventory(
			guard.Context(),
			target,
			record.User,
			record.App,
			record.Operation.Desired,
			true,
		)
		if err != nil {
			return fmt.Errorf("read ensured target inventory: %w", err)
		}
		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		if err := target.VerifyServerIdentity(ctx); err != nil {
			cancel()
			return fmt.Errorf("verify ensured target before recovery commit: %w", err)
		}
		err = guard.CommitStateIdentity(ctx, record.Operation.TargetHost, target.InstanceID, actual)
		cancel()
		if err != nil {
			return err
		}
		*finished = true
		return nil
	case found == 0:
		return release(guard, finished)
	default:
		return fmt.Errorf("ensure operation %s/%s has partial target state", record.User, record.App)
	}
}

func (c *Controller) reconcileStop(guard *placement.Guard, record placement.Record, finished *bool) error {
	op := record.Operation
	source, sourceGone, err := c.participant(guard.Context(), op.SourceHost, op.SourceInstanceID)
	if err != nil {
		return err
	}
	if sourceGone {
		// The VM is certainly gone, but its agent may have disappeared before
		// deleting the encrypted remote snapshot. Do not claim Stop completed or
		// erase the only durable retry record.
		return fmt.Errorf(
			"stop operation %s/%s lost source %s@%s before snapshot deletion was acknowledged",
			record.User, record.App, op.SourceHost, op.SourceInstanceID,
		)
	}
	if source == nil {
		return fmt.Errorf("stop operation %s/%s awaits source inventory", record.User, record.App)
	}
	for _, gen := range op.Generations {
		if err := source.StopContext(guard.Context(), record.User, record.App, gen); err != nil {
			return fmt.Errorf("retry stop generation %s: %w", gen, err)
		}
	}
	commitCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	if err := source.VerifyServerIdentity(commitCtx); err != nil {
		return fmt.Errorf("verify stopped source before recovery commit: %w", err)
	}
	actual, err := actualInventory(commitCtx, source, record.User, record.App, op.Desired, true)
	if err != nil {
		return fmt.Errorf("read stopped source inventory: %w", err)
	}
	if err := guard.CommitStateIdentity(
		commitCtx, op.SourceHost, op.SourceInstanceID, actual,
	); err != nil {
		return err
	}
	*finished = true
	return nil
}

func (c *Controller) reconcileMove(guard *placement.Guard, record placement.Record, finished *bool) error {
	op := record.Operation
	source, sourceGone, err := c.participant(guard.Context(), op.SourceHost, op.SourceInstanceID)
	if err != nil {
		return err
	}
	target, targetGone, err := c.participant(guard.Context(), op.TargetHost, op.TargetInstanceID)
	if err != nil {
		return err
	}

	switch {
	case sourceGone && target != nil:
		actual, err := normalizeDesiredInventory(
			guard.Context(), target, record.User, record.App, op.Desired, "",
		)
		if err != nil {
			return fmt.Errorf("source is gone but target is not verifiably prepared: %w", err)
		}
		commitCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()
		if err := target.VerifyServerIdentity(commitCtx); err != nil {
			return fmt.Errorf("verify prepared target before recovery commit: %w", err)
		}
		if err := guard.CommitStateIdentity(
			commitCtx, op.TargetHost, op.TargetInstanceID, actual,
		); err != nil {
			return err
		}
		*finished = true
		return nil
	case targetGone && source != nil:
		if err := c.restoreSource(guard.Context(), source, record); err != nil {
			return err
		}
		return commitSource(guard, source, record, finished)
	case sourceGone && targetGone:
		return fmt.Errorf("operation %s/%s lost both immutable host incarnations", record.User, record.App)
	case source == nil || target == nil:
		return fmt.Errorf(
			"operation %s/%s awaits authoritative source and target inventory or GCE tombstone proof",
			record.User, record.App,
		)
	}

	// Both exact participants are alive. Placement is still the source, so
	// conservatively discard any target copy and retain/restore the source.
	for _, gen := range op.Generations {
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
	}
	if err := c.restoreSource(guard.Context(), source, record); err != nil {
		return err
	}
	return commitSource(guard, source, record, finished)
}

func (c *Controller) restoreSource(ctx context.Context, source *backend.AgentClient, record placement.Record) error {
	op := record.Operation
	for _, gen := range op.Generations {
		status, found, err := source.StatusContext(ctx, record.User, record.App, gen)
		if err != nil {
			return err
		}
		expected, expectedFound := generationByID(record.Generations, gen)
		if !expectedFound {
			return fmt.Errorf("source generation %s is absent from durable inventory", gen)
		}
		if found && expected.SSHHostPublicKey != "" &&
			status.SSHHostPublicKey != expected.SSHHostPublicKey {
			return fmt.Errorf("source generation %s has SSH host key mismatch", gen)
		}
		shouldRun := expected.State == "" || expected.State == "running"
		if shouldRun && found && status.State == "running" {
			continue
		}
		if !shouldRun {
			switch {
			case found && status.State == "sleeping":
				continue
			case found && status.State == "running":
				if err := source.SetNoIdleWithEpoch(
					ctx, record.User, record.App, gen, false, op.SourceEpoch,
				); err != nil {
					return fmt.Errorf("release source generation %s hold: %w", gen, err)
				}
				if err := source.SleepWithEpoch(
					ctx, record.User, record.App, gen, op.SourceEpoch,
				); err != nil {
					return fmt.Errorf("sleep unexpected running source generation %s: %w", gen, err)
				}
				continue
			case !found:
				if _, err := source.RegisterSleepingWithEpoch(
					ctx, record.User, record.App, gen, op.SourceEpoch,
				); err != nil {
					return fmt.Errorf("register source sleeping generation %s: %w", gen, err)
				}
				continue
			default:
				return fmt.Errorf("source generation %s is in unexpected state %q", gen, status.State)
			}
		}
		var adoptErr error
		if op.SourceEpoch != "" {
			_, adoptErr = source.AdoptForcedContext(ctx, record.User, record.App, gen, op.SourceEpoch)
		} else {
			_, adoptErr = source.AdoptContext(ctx, record.User, record.App, gen)
		}
		if adoptErr != nil {
			return fmt.Errorf("restore source generation %s: %w", gen, adoptErr)
		}
	}
	return nil
}

func commitSource(
	guard *placement.Guard,
	source *backend.AgentClient,
	record placement.Record,
	finished *bool,
) error {
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	if err := source.VerifyServerIdentity(ctx); err != nil {
		return fmt.Errorf("verify retained source before recovery commit: %w", err)
	}
	actual, err := actualInventory(
		ctx, source, record.User, record.App, record.Generations, true,
	)
	if err != nil {
		return fmt.Errorf("read retained source inventory: %w", err)
	}
	if err := guard.CommitStateIdentity(
		ctx, record.Operation.SourceHost, record.Operation.SourceInstanceID, actual,
	); err != nil {
		return err
	}
	*finished = true
	return nil
}

func normalizeDesiredInventory(
	ctx context.Context,
	client *backend.AgentClient,
	user, app string,
	desired []placement.Generation,
	cordonEpoch string,
) ([]placement.Generation, error) {
	for _, generation := range desired {
		expectedState := generation.State
		if expectedState == "" {
			expectedState = "running"
		}
		status, found, err := client.StatusContext(ctx, user, app, generation.Gen)
		if err != nil {
			return nil, err
		}
		if expectedState != "sleeping" {
			continue
		}
		switch {
		case !found:
			if _, err := client.RegisterSleepingWithEpoch(
				ctx, user, app, generation.Gen, cordonEpoch,
			); err != nil {
				return nil, fmt.Errorf("register desired sleeping generation %s: %w", generation.Gen, err)
			}
		case status.State == "running":
			if err := client.SetNoIdleWithEpoch(
				ctx, user, app, generation.Gen, false, cordonEpoch,
			); err != nil {
				return nil, err
			}
			if err := client.SleepWithEpoch(
				ctx, user, app, generation.Gen, cordonEpoch,
			); err != nil {
				return nil, fmt.Errorf("sleep unexpected running generation %s: %w", generation.Gen, err)
			}
		}
	}
	return actualInventory(ctx, client, user, app, desired, true)
}

func actualInventory(
	ctx context.Context,
	client *backend.AgentClient,
	user, app string,
	desired []placement.Generation,
	registerSleeping bool,
) ([]placement.Generation, error) {
	actual := make([]placement.Generation, 0, len(desired))
	for _, generation := range desired {
		status, found, err := client.StatusContext(ctx, user, app, generation.Gen)
		if err != nil {
			return nil, err
		}
		if !found && registerSleeping && generation.State == "sleeping" {
			info, err := client.RegisterSleeping(ctx, user, app, generation.Gen)
			if err != nil {
				return nil, err
			}
			status.State = string(info.State)
			status.SSHHostPublicKey = info.SSHHostPublicKey
			found = true
		}
		if !found {
			return nil, fmt.Errorf("generation %s is missing", generation.Gen)
		}
		expectedState := generation.State
		if expectedState == "" {
			expectedState = "running"
		}
		if status.State != expectedState {
			return nil, fmt.Errorf("generation %s state is %s, want %s", generation.Gen, status.State, expectedState)
		}
		if generation.SSHHostPublicKey == "" ||
			status.SSHHostPublicKey != generation.SSHHostPublicKey {
			return nil, fmt.Errorf("generation %s SSH host identity is not pinned", generation.Gen)
		}
		generation.State = status.State
		generation.SSHHostPublicKey = status.SSHHostPublicKey
		actual = append(actual, generation)
	}
	return actual, nil
}

func generationByID(generations []placement.Generation, gen string) (placement.Generation, bool) {
	for _, generation := range generations {
		if generation.Gen == gen {
			return generation, true
		}
	}
	return placement.Generation{}, false
}

func (c *Controller) participant(
	ctx context.Context,
	name, instanceID string,
) (*backend.AgentClient, bool, error) {
	if name == "" {
		return nil, false, fmt.Errorf("journal participant is missing its host name")
	}
	if client, ok := c.Hosts.Get(name); ok {
		if client.InstanceID == instanceID {
			// Empty IDs are retained only for explicit loopback tests.
			return client, false, nil
		}
	}
	if instanceID == "" {
		return nil, false, fmt.Errorf("journal participant %s is missing immutable GCE identity", name)
	}
	if c.Tombstones == nil {
		return nil, false, nil
	}
	gone, err := c.Tombstones.Gone(ctx, name, instanceID)
	if err != nil {
		return nil, false, err
	}
	if gone {
		return nil, true, nil
	}
	return nil, false, nil
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
