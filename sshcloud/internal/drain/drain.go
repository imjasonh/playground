// Package drain cordons a host and migrates its app generations.
package drain

import (
	"context"
	"fmt"
	"sort"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/agent"
	"github.com/imjasonh/playground/sshcloud/internal/backend"
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
	Host     string      `json:"host"`
	Cordoned bool        `json:"cordoned"`
	Moved    []MovedApp  `json:"moved"`
}

type MovedApp struct {
	User     string   `json:"user"`
	App      string   `json:"app"`
	Target   string   `json:"target"`
	Gens     []string `json:"gens"`
	Sessions int      `json:"sessions"`
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
	if err := source.SetCordoned(ctx, true); err != nil {
		return Result{}, fmt.Errorf("cordon %s: %w", hostID, err)
	}
	result := Result{Host: hostID, Cordoned: true}
	inventory, err := source.Instances(ctx)
	if err != nil {
		return result, fmt.Errorf("inventory %s: %w", hostID, err)
	}
	groups := groupInstances(inventory)
	for _, group := range groups {
		moved, err := c.moveGroup(ctx, hostID, source, group)
		if err != nil {
			return result, fmt.Errorf("drain %s/%s: %w", group.user, group.app, err)
		}
		result.Moved = append(result.Moved, moved)
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

func (c *Controller) moveGroup(ctx context.Context, sourceID string, source *backend.AgentClient, group appGroup) (MovedApp, error) {
	guard, err := placement.AcquireGuard(ctx, c.Placement, group.user, group.app, "drain", c.LeaseTTL)
	if err != nil {
		return MovedApp{}, err
	}
	committed := false
	defer func() {
		if !committed {
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

	var moved []agent.InstanceInfo
	rollback := func(cause error) (MovedApp, error) {
		recoveryCtx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
		defer cancel()
		rollbackErr := c.rollback(recoveryCtx, source, target.Client, group, moved)
		c.thawAll(frozen)
		if rollbackErr != nil {
			return MovedApp{}, fmt.Errorf("%w (rollback failed: %v)", cause, rollbackErr)
		}
		return MovedApp{}, cause
	}

	for _, instance := range group.instances {
		if instance.State == agent.StateRunning {
			if err := source.SetNoIdleContext(guard.Context(), group.user, group.app, instance.Gen, false); err != nil {
				return rollback(fmt.Errorf("release generation %q hold: %w", instance.Gen, err))
			}
			if err := source.SleepContext(guard.Context(), group.user, group.app, instance.Gen); err != nil {
				return rollback(fmt.Errorf("sleep generation %q: %w", instance.Gen, err))
			}
		}
		if err := source.EvictContext(guard.Context(), group.user, group.app, instance.Gen); err != nil {
			return rollback(fmt.Errorf("evict generation %q: %w", instance.Gen, err))
		}
		if instance.State == agent.StateRunning {
			if _, err := target.Client.AdoptContext(guard.Context(), group.user, group.app, instance.Gen); err != nil {
				recoveryCtx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
				_, sourceErr := source.AdoptForcedContext(recoveryCtx, group.user, group.app, instance.Gen)
				cancel()
				if sourceErr != nil {
					return rollback(fmt.Errorf("adopt generation %q on %s: %w (source restore failed: %v)", instance.Gen, target.ID, err, sourceErr))
				}
				return rollback(fmt.Errorf("adopt generation %q on %s: %w", instance.Gen, target.ID, err))
			}
		}
		moved = append(moved, instance)
	}

	commitCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	err = guard.Commit(commitCtx, target.ID)
	cancel()
	if err != nil {
		checkCtx, checkCancel := context.WithTimeout(context.Background(), 10*time.Second)
		record, ok, checkErr := c.Placement.GetRecord(checkCtx, group.user, group.app)
		checkCancel()
		if checkErr != nil || !ok || record.HostID != target.ID || record.LeaseOwner != "" {
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
	c.thawAll(frozen)
	return movedResult, nil
}

func (c *Controller) rollback(ctx context.Context, source, target *backend.AgentClient, group appGroup, moved []agent.InstanceInfo) error {
	for i := len(moved) - 1; i >= 0; i-- {
		instance := moved[i]
		if instance.State != agent.StateRunning {
			if _, err := source.AdoptForcedContext(ctx, group.user, group.app, instance.Gen); err != nil {
				return err
			}
			if err := source.SetNoIdleContext(ctx, group.user, group.app, instance.Gen, false); err != nil {
				return err
			}
			if err := source.SleepContext(ctx, group.user, group.app, instance.Gen); err != nil {
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
		if _, err := source.AdoptForcedContext(ctx, group.user, group.app, instance.Gen); err != nil {
			return err
		}
	}
	return nil
}

func (c *Controller) thawAll(frozen []frozenGeneration) {
	if c.Gateway == nil {
		return
	}
	for _, freeze := range frozen {
		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		_ = c.Gateway.Thaw(ctx, freeze.token)
		cancel()
	}
}

func releaseGuard(guard *placement.Guard) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	_ = guard.Release(ctx)
}
