// Package drain cordons a host and migrates its app generations.
package drain

import (
	"context"
	"errors"
	"fmt"
	"sort"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/agent"
	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/genid"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
)

// Controller coordinates agent inventory, placement fencing, and gateway
// session freeze/thaw for a host drain.
type Controller struct {
	Placement    placement.Store
	Hosts        *backend.HostSet
	Gateway      *backend.GatewayClient
	FreezeWindow time.Duration
	LeaseTTL     time.Duration
}

type Result struct {
	Host     string     `json:"host"`
	Cordoned bool       `json:"cordoned"`
	Moved    []MovedApp `json:"moved"`
}

type MovedApp struct {
	User     string   `json:"user"`
	App      string   `json:"app"`
	Target   string   `json:"target"`
	Gens     []string `json:"gens"`
	Sessions int      `json:"sessions"`
	Warnings []string `json:"warnings,omitempty"`
}

type appGroup struct {
	user      string
	app       string
	instances []agent.InstanceInfo
}

type frozenGeneration struct {
	gen      string
	token    string
	sessions int
}

// DrainHost cordons hostID and moves every placed app as one fenced operation.
// Successfully moved apps remain moved if a later app fails; the host remains
// cordoned so an operator can retry safely.
func (c *Controller) DrainHost(ctx context.Context, hostID string) (Result, error) {
	if c.Placement == nil || c.Hosts == nil {
		return Result{}, fmt.Errorf("placement and hosts are required")
	}
	source, ok := c.Hosts.Get(hostID)
	if !ok {
		return Result{}, fmt.Errorf("unknown host %q", hostID)
	}
	sourceEpoch, err := source.Cordon(ctx)
	if err != nil {
		return Result{}, fmt.Errorf("cordon %s: %w", hostID, err)
	}
	result := Result{Host: hostID, Cordoned: true}
	inventory, err := source.Instances(ctx)
	if err != nil {
		return result, fmt.Errorf("inventory %s: %w", hostID, err)
	}
	records, err := c.Placement.ListRecords(ctx)
	if err != nil {
		return result, fmt.Errorf("placement inventory: %w", err)
	}
	seen := make(map[string]bool)
	appSeen := make(map[string]bool)
	recordByApp := make(map[string]placement.Record)
	for _, record := range records {
		recordByApp[record.User+"\x00"+record.App] = record
	}
	for _, instance := range inventory {
		seen[instance.User+"\x00"+instance.App+"\x00"+instance.Gen] = true
		appSeen[instance.User+"\x00"+instance.App] = true
	}
	for _, record := range records {
		if record.HostID != hostID {
			continue
		}
		if len(record.Generations) == 0 && !appSeen[record.User+"\x00"+record.App] {
			return result, fmt.Errorf("placement %s/%s has unknown generation inventory; host cannot be certified empty", record.User, record.App)
		}
		for _, generation := range record.Generations {
			k := record.User + "\x00" + record.App + "\x00" + generation.Gen
			if seen[k] {
				continue
			}
			inventory = append(inventory, agent.InstanceInfo{
				User: record.User, App: record.App, Gen: generation.Gen,
				AgentApp: genid.AgentApp(record.App, generation.Gen),
				Image:    generation.Image, Tier: generation.Tier, State: agent.StateSleeping,
			})
		}
	}
	filtered := inventory[:0]
	for _, instance := range inventory {
		record, ok := recordByApp[instance.User+"\x00"+instance.App]
		if ok && record.HostID != "" && record.HostID != hostID {
			if instance.State != agent.StateSleeping {
				return result, fmt.Errorf("running orphan %s/%s@%s belongs to placement %s", instance.User, instance.App, instance.Gen, record.HostID)
			}
			if err := source.EvictWithEpoch(ctx, instance.User, instance.App, instance.Gen, sourceEpoch); err != nil {
				return result, fmt.Errorf("reap sleeping orphan %s/%s@%s: %w", instance.User, instance.App, instance.Gen, err)
			}
			continue
		}
		filtered = append(filtered, instance)
	}
	inventory = filtered
	groups := groupInstances(inventory)
	for _, group := range groups {
		moved, err := c.moveGroup(ctx, hostID, sourceEpoch, source, group)
		if err != nil {
			return result, fmt.Errorf("drain %s/%s: %w", group.user, group.app, err)
		}
		result.Moved = append(result.Moved, moved)
	}
	remaining, err := source.Instances(ctx)
	if err != nil {
		return result, fmt.Errorf("final inventory %s: %w", hostID, err)
	}
	if len(remaining) != 0 {
		return result, fmt.Errorf("host %s still has %d instances after drain", hostID, len(remaining))
	}
	finalRecords, err := c.Placement.ListRecords(ctx)
	if err != nil {
		return result, fmt.Errorf("final placement inventory: %w", err)
	}
	for _, record := range finalRecords {
		if record.HostID == hostID {
			return result, fmt.Errorf("host %s still owns placement %s/%s", hostID, record.User, record.App)
		}
		if record.Operation.Kind != "" &&
			(record.Operation.SourceHost == hostID || record.Operation.TargetHost == hostID) {
			return result, fmt.Errorf("host %s still participates in operation %s for %s/%s", hostID, record.Operation.Kind, record.User, record.App)
		}
	}
	return result, nil
}

func groupInstances(inventory []agent.InstanceInfo) []appGroup {
	byApp := make(map[string]*appGroup)
	for _, instance := range inventory {
		k := instance.User + "\x00" + instance.App
		group := byApp[k]
		if group == nil {
			group = &appGroup{user: instance.User, app: instance.App}
			byApp[k] = group
		}
		group.instances = append(group.instances, instance)
	}
	out := make([]appGroup, 0, len(byApp))
	for _, group := range byApp {
		sort.Slice(group.instances, func(i, j int) bool {
			return group.instances[i].Gen < group.instances[j].Gen
		})
		out = append(out, *group)
	}
	sort.Slice(out, func(i, j int) bool {
		if out[i].user != out[j].user {
			return out[i].user < out[j].user
		}
		return out[i].app < out[j].app
	})
	return out
}

func (c *Controller) moveGroup(ctx context.Context, sourceID, sourceEpoch string, source *backend.AgentClient, group appGroup) (MovedApp, error) {
	guard, err := placement.AcquireGuard(ctx, c.Placement, group.user, group.app, "drain", c.LeaseTTL)
	if err != nil {
		return MovedApp{}, err
	}
	committed := false
	abandoned := false
	defer func() {
		if !committed && !abandoned {
			releaseGuard(guard)
		}
	}()
	if guard.HostID() != sourceID {
		return MovedApp{}, fmt.Errorf("placement points to %q, not draining host %q", guard.HostID(), sourceID)
	}

	need := agent.Resources{}
	for _, instance := range group.instances {
		if instance.State != agent.StateRunning {
			continue
		}
		resources, err := agent.ResourcesForTier(instance.Tier)
		if err != nil {
			return MovedApp{}, err
		}
		need.VCPUs += resources.VCPUs
		need.MemMiB += resources.MemMiB
	}
	candidates, err := c.Hosts.CandidatesFor(guard.Context(), need, map[string]bool{sourceID: true})
	if err != nil {
		return MovedApp{}, err
	}
	if len(candidates) == 0 {
		return MovedApp{}, fmt.Errorf("no target has capacity for %d vCPU/%d MiB", need.VCPUs, need.MemMiB)
	}
	target := candidates[0]
	var generations []string
	var generationState []placement.Generation
	for _, instance := range group.instances {
		generations = append(generations, instance.Gen)
		generationState = append(generationState, placement.Generation{
			Gen: instance.Gen, Image: instance.Image, Tier: instance.Tier, State: string(instance.State),
		})
	}
	operation := placement.Operation{
		ID: guard.Owner(), Kind: "drain", Phase: "freezing", SourceHost: sourceID,
		SourceEpoch: sourceEpoch, TargetHost: target.ID, Generations: generations,
		Desired: generationState,
	}
	if err := guard.Mark(guard.Context(), operation); err != nil {
		return MovedApp{}, fmt.Errorf("persist drain operation: %w", err)
	}
	var moved []agent.InstanceInfo
	for _, instance := range group.instances {
		if instance.State == agent.StateSleeping {
			if _, err := target.Client.RegisterSleeping(guard.Context(), group.user, group.app, instance.Gen); err != nil {
				for _, registered := range moved {
					_ = target.Client.EvictContext(context.Background(), group.user, group.app, registered.Gen)
				}
				return MovedApp{}, fmt.Errorf("register sleeping generation %q on %s: %w", instance.Gen, target.ID, err)
			}
			moved = append(moved, instance)
		}
	}

	var frozen []frozenGeneration
	for _, instance := range group.instances {
		if instance.State != agent.StateRunning {
			continue
		}
		if c.Gateway == nil {
			if instance.NoIdle {
				return MovedApp{}, fmt.Errorf("active generation %q requires gateway freeze control", instance.Gen)
			}
			continue
		}
		window := c.FreezeWindow
		if window <= 0 {
			window = 30 * time.Second
		}
		token, sessions, err := c.Gateway.Freeze(guard.Context(), group.user, group.app, instance.Gen, window)
		if err != nil {
			c.thawAll(frozen)
			return MovedApp{}, fmt.Errorf("freeze generation %q: %w", instance.Gen, err)
		}
		frozen = append(frozen, frozenGeneration{gen: instance.Gen, token: token, sessions: sessions})
	}

	rollback := func(cause error) (MovedApp, error) {
		if leaseErr := guard.Err(); leaseErr != nil {
			guard.Abandon()
			abandoned = true
			return MovedApp{}, fmt.Errorf("%w (placement lease lost: %v)", cause, leaseErr)
		}
		recoveryCtx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
		defer cancel()
		rollbackErr := c.rollback(recoveryCtx, source, sourceEpoch, target.Client, group, moved)
		if rollbackErr != nil {
			operation.Phase = "rollback-failed"
			_ = markOperation(guard, operation)
			guard.Abandon()
			abandoned = true
			return MovedApp{}, fmt.Errorf("%w (rollback failed: %v)", cause, rollbackErr)
		}
		c.thawAll(frozen)
		return MovedApp{}, cause
	}

	for _, instance := range group.instances {
		if instance.State == agent.StateSleeping {
			continue
		}
		operation.Phase = "moving:" + instance.Gen
		if err := guard.Mark(guard.Context(), operation); err != nil {
			return rollback(fmt.Errorf("persist generation phase %q: %w", instance.Gen, err))
		}
		if instance.State == agent.StateRunning {
			if err := source.SetNoIdleWithEpoch(guard.Context(), group.user, group.app, instance.Gen, false, sourceEpoch); err != nil {
				return rollback(fmt.Errorf("release generation %q hold: %w", instance.Gen, err))
			}
			if err := source.SleepWithEpoch(guard.Context(), group.user, group.app, instance.Gen, sourceEpoch); err != nil {
				statusCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
				status, found, statusErr := source.StatusContext(statusCtx, group.user, group.app, instance.Gen)
				cancel()
				if statusErr != nil {
					operation.Phase = "unknown-sleep:" + instance.Gen
					_ = markOperation(guard, operation)
					guard.Abandon()
					abandoned = true
					return MovedApp{}, fmt.Errorf("sleep generation %q outcome unknown: %w (status: %v)", instance.Gen, err, statusErr)
				}
				if !found || status.State != "sleeping" {
					return rollback(fmt.Errorf("sleep generation %q: %w", instance.Gen, err))
				}
			}
		}
		if err := source.EvictWithEpoch(guard.Context(), group.user, group.app, instance.Gen, sourceEpoch); err != nil {
			statusCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
			_, found, statusErr := source.StatusContext(statusCtx, group.user, group.app, instance.Gen)
			cancel()
			if statusErr != nil {
				operation.Phase = "unknown-evict:" + instance.Gen
				_ = markOperation(guard, operation)
				guard.Abandon()
				abandoned = true
				return MovedApp{}, fmt.Errorf("evict generation %q outcome unknown: %w (status: %v)", instance.Gen, err, statusErr)
			}
			if found {
				return rollback(fmt.Errorf("evict generation %q: %w", instance.Gen, err))
			}
		}
		if instance.State == agent.StateRunning {
			if _, err := target.Client.AdoptContext(guard.Context(), group.user, group.app, instance.Gen); err != nil {
				recoveryCtx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
				status, found, statusErr := target.Client.StatusContext(recoveryCtx, group.user, group.app, instance.Gen)
				if statusErr != nil {
					cancel()
					operation.Phase = "unknown-adopt:" + instance.Gen
					_ = markOperation(guard, operation)
					guard.Abandon()
					abandoned = true
					return MovedApp{}, fmt.Errorf("adopt generation %q outcome unknown: %w (status: %v)", instance.Gen, err, statusErr)
				}
				if found && status.State == "running" {
					cancel()
					moved = append(moved, instance)
					continue
				}
				if leaseErr := guard.Err(); leaseErr != nil {
					guard.Abandon()
					abandoned = true
					return MovedApp{}, fmt.Errorf("target adopt failed after lease loss: %w", leaseErr)
				}
				_, sourceErr := source.AdoptForcedContext(recoveryCtx, group.user, group.app, instance.Gen, sourceEpoch)
				cancel()
				if sourceErr != nil {
					operation.Phase = "source-restore-failed:" + instance.Gen
					_ = markOperation(guard, operation)
					guard.Abandon()
					abandoned = true
					return MovedApp{}, fmt.Errorf("adopt generation %q on %s: %w (source restore failed: %v)", instance.Gen, target.ID, err, sourceErr)
				}
				return rollback(fmt.Errorf("adopt generation %q on %s: %w", instance.Gen, target.ID, err))
			}
		}
		moved = append(moved, instance)
	}

	commitCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	operation.Phase = "ready"
	if err := guard.Mark(commitCtx, operation); err != nil {
		cancel()
		return rollback(fmt.Errorf("persist ready phase: %w", err))
	}
	err = guard.CommitState(commitCtx, target.ID, generationState)
	cancel()
	if err != nil {
		var lost placement.ErrLeaseLost
		if errors.As(err, &lost) {
			guard.Abandon()
			abandoned = true
			return MovedApp{}, err
		}
		checkCtx, checkCancel := context.WithTimeout(context.Background(), 10*time.Second)
		record, ok, checkErr := c.Placement.GetRecord(checkCtx, group.user, group.app)
		checkCancel()
		if checkErr != nil {
			operation.Phase = "unknown-commit"
			_ = markOperation(guard, operation)
			guard.Abandon()
			abandoned = true
			return MovedApp{}, fmt.Errorf("placement commit outcome unknown: %w (read: %v)", err, checkErr)
		}
		if !ok || (record.LeaseOwner != guard.Owner() && record.LeaseOwner != "") ||
			(record.Operation.ID != "" && record.Operation.ID != operation.ID) {
			guard.Abandon()
			abandoned = true
			return MovedApp{}, fmt.Errorf("placement lease lost during commit: %w", err)
		}
		if record.HostID != target.ID || record.LeaseOwner != "" {
			return rollback(fmt.Errorf("commit placement to %s: %w", target.ID, err))
		}
	}
	committed = true

	movedResult := MovedApp{User: group.user, App: group.app, Target: target.ID}
	for _, instance := range group.instances {
		movedResult.Gens = append(movedResult.Gens, instance.Gen)
	}
	for _, freeze := range frozen {
		movedResult.Sessions += freeze.sessions
	}
	for _, instance := range group.instances {
		if instance.State == agent.StateSleeping {
			cleanupCtx, cleanupCancel := context.WithTimeout(context.Background(), 30*time.Second)
			err := source.EvictWithEpoch(cleanupCtx, group.user, group.app, instance.Gen, sourceEpoch)
			cleanupCancel()
			if err != nil {
				movedResult.Warnings = append(movedResult.Warnings,
					fmt.Sprintf("source sleeping generation %s cleanup: %v", instance.Gen, err))
			}
		}
	}
	movedResult.Warnings = append(movedResult.Warnings, c.thawAll(frozen)...)
	return movedResult, nil
}

func (c *Controller) rollback(ctx context.Context, source *backend.AgentClient, sourceEpoch string, target *backend.AgentClient, group appGroup, moved []agent.InstanceInfo) error {
	for i := len(moved) - 1; i >= 0; i-- {
		instance := moved[i]
		if instance.State != agent.StateRunning {
			if err := target.EvictContext(ctx, group.user, group.app, instance.Gen); err != nil {
				return err
			}
			continue
		}
		if err := target.SetNoIdleContext(ctx, group.user, group.app, instance.Gen, false); err != nil {
			return err
		}
		if err := target.SleepContext(ctx, group.user, group.app, instance.Gen); err != nil {
			return err
		}
		if err := target.EvictContext(ctx, group.user, group.app, instance.Gen); err != nil {
			return err
		}
		if _, err := source.AdoptForcedContext(ctx, group.user, group.app, instance.Gen, sourceEpoch); err != nil {
			return err
		}
	}
	return nil
}

func (c *Controller) thawAll(frozen []frozenGeneration) []string {
	if c.Gateway == nil {
		return nil
	}
	var warnings []string
	for _, freeze := range frozen {
		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		if err := c.Gateway.Thaw(ctx, freeze.token); err != nil {
			warnings = append(warnings, fmt.Sprintf(
				"generation %s placement committed; outer session must reconnect: %v", freeze.gen, err))
		}
		cancel()
	}
	return warnings
}

func releaseGuard(guard *placement.Guard) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	_ = guard.Release(ctx)
}

func markOperation(guard *placement.Guard, operation placement.Operation) error {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	return guard.Mark(ctx, operation)
}
