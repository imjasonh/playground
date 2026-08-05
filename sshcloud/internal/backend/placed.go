package backend

import (
	"context"
	"errors"
	"fmt"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/placement"
)

// PlacedDial resolves (user, app) → host agent via placement, then Ensures.
type PlacedDial struct {
	Placement   placement.Store
	Agents      *HostSet
	DefaultHost string // used when no placement yet; empty falls back to Agents.DefaultHost
	LeaseTTL    time.Duration
}

func (p *PlacedDial) resolve(host, user, app string, allowFallback bool) (*AgentClient, string, error) {
	if p.Agents == nil {
		return nil, "", fmt.Errorf("no agents available for %s/%s", user, app)
	}
	if host == "" {
		host = p.DefaultHost
		if host == "" {
			host = p.Agents.DefaultHost()
		}
		if host == "" {
			return nil, "", fmt.Errorf("no placement for %s/%s and no default host", user, app)
		}
	}
	c, ok := p.Agents.Get(host)
	if !ok && allowFallback {
		replacement := p.DefaultHost
		if replacement == "" || replacement == host {
			replacement = p.Agents.DefaultHost()
		}
		if replacement == "" || replacement == host {
			return nil, "", fmt.Errorf("placed host %q is gone and no replacement is ready for %s/%s", host, user, app)
		}
		c, ok = p.Agents.Get(replacement)
		if !ok {
			return nil, "", fmt.Errorf("replacement host %q is not ready for %s/%s", replacement, user, app)
		}
		host = replacement
	}
	if !ok {
		return nil, "", fmt.Errorf("placed host %q is unavailable for %s/%s", host, user, app)
	}
	return c, host, nil
}

// Addr dials the placed host agent for this app generation.
func (p *PlacedDial) Addr(user, app, gen, image string) (string, error) {
	return p.EnsureAddr(context.Background(), user, app, gen, image, false)
}

// EnsureAddr boots/wakes and returns the guest SSH address.
func (p *PlacedDial) EnsureAddr(ctx context.Context, user, app, gen, image string, noIdle bool) (string, error) {
	return p.EnsureAddrTier(ctx, user, app, gen, image, "", noIdle)
}

// EnsureAddrTier boots/wakes with an explicit resource tier.
func (p *PlacedDial) EnsureAddrTier(ctx context.Context, user, app, gen, image, tier string, noIdle bool) (string, error) {
	if p.Agents == nil {
		return "", fmt.Errorf("no agents available for %s/%s", user, app)
	}
	guard, err := placement.AcquireGuard(ctx, p.Placement, user, app, "ensure", p.LeaseTTL)
	if err != nil {
		return "", err
	}
	committed := false
	defer func() {
		if !committed {
			releasePlacementGuard(guard)
		}
	}()
	excluded := make(map[string]bool)
	originalHost := guard.HostID()
	record, _, err := p.Placement.GetRecord(guard.Context(), user, app)
	if err != nil {
		return "", err
	}
	generations := placement.UpsertGeneration(record.Generations, placement.Generation{
		Gen: gen, Image: image, Tier: tier, State: "running",
	})
	var choices []HostCandidate
	if host := guard.HostID(); host != "" {
		client, ok := p.Agents.Get(host)
		if !ok {
			return "", fmt.Errorf("placed host %q is unavailable for %s/%s; explicit host recovery is required", host, user, app)
		}
		choices = append(choices, HostCandidate{ID: host, Client: client})
		excluded[host] = true
	}
	if len(choices) == 0 {
		candidates, candidateErr := p.Agents.Candidates(guard.Context(), tier, excluded)
		if candidateErr != nil {
			return "", candidateErr
		}
		choices = append(choices, candidates...)
	}
	if len(choices) == 0 {
		return "", fmt.Errorf("no host has capacity for %s/%s tier %s", user, app, tier)
	}
	var (
		in           InstanceView
		host         string
		chosenClient *AgentClient
		lastErr      error
	)
	for _, choice := range choices {
		if originalHost == "" {
			if err := guard.Mark(guard.Context(), placement.Operation{
				Kind: "ensure", Phase: "ensuring", TargetHost: choice.ID,
				Generations: []string{gen}, Desired: generations,
			}); err != nil {
				return "", err
			}
		}
		in, err = choice.Client.EnsureTierContext(guard.Context(), user, app, gen, image, tier, noIdle)
		if err == nil {
			host = choice.ID
			chosenClient = choice.Client
			break
		}
		var capacity ErrAgentCapacity
		if !errors.As(err, &capacity) {
			statusCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
			status, found, statusErr := choice.Client.StatusContext(statusCtx, user, app, gen)
			cancel()
			if statusErr == nil && found && status.State == "running" {
				in, host, chosenClient = status, choice.ID, choice.Client
				break
			}
			if statusErr != nil && originalHost == "" {
				guard.Abandon()
				committed = true
				return "", fmt.Errorf("ensure outcome unknown on %s: %w (status: %v)", choice.ID, err, statusErr)
			}
			return "", err
		}
		lastErr = err
	}
	if host == "" {
		if lastErr != nil {
			return "", lastErr
		}
		return "", fmt.Errorf("no host accepted %s/%s tier %s", user, app, tier)
	}
	for _, generation := range generations {
		if generation.Gen == gen && generation.SSHHostPublicKey != "" &&
			generation.SSHHostPublicKey != in.SSHHostPublicKey {
			return "", fmt.Errorf("SSH host key changed for immutable generation %q", gen)
		}
	}
	generations = placement.UpsertGeneration(generations, placement.Generation{
		Gen: gen, Image: image, Tier: tier, State: "running",
		SSHHostPublicKey: in.SSHHostPublicKey,
	})
	if originalHost == "" {
		if err := guard.Mark(guard.Context(), placement.Operation{
			Kind: "ensure", Phase: "ready", TargetHost: host,
			Generations: []string{gen}, Desired: generations,
		}); err != nil {
			guard.Abandon()
			committed = true
			return "", fmt.Errorf("persist ensured generation identity: %w", err)
		}
	}
	if originalHost != "" {
		commitCtx, commitCancel := context.WithTimeout(context.Background(), 10*time.Second)
		err := guard.CommitState(commitCtx, originalHost, generations)
		commitCancel()
		if err != nil {
			return "", fmt.Errorf("release placement lease: %w", err)
		}
		committed = true
		return in.Addr, nil
	}
	commitCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	commitErr := guard.CommitState(commitCtx, host, generations)
	cancel()
	if commitErr != nil {
		var lost placement.ErrLeaseLost
		if errors.As(commitErr, &lost) {
			guard.Abandon()
			committed = true
			return "", commitErr
		}
		checkCtx, checkCancel := context.WithTimeout(context.Background(), 10*time.Second)
		record, ok, checkErr := p.Placement.GetRecord(checkCtx, user, app)
		checkCancel()
		if checkErr != nil {
			guard.Abandon()
			committed = true
			return "", fmt.Errorf("placement commit outcome unknown: %w (read: %v)", commitErr, checkErr)
		}
		if !ok || (record.LeaseOwner != "" && record.LeaseOwner != guard.Owner()) ||
			(record.Operation.ID != "" && record.Operation.ID != guard.Owner()) {
			guard.Abandon()
			committed = true
			return "", fmt.Errorf("placement lease lost during ensure commit: %w", commitErr)
		}
		if record.HostID != host || record.LeaseOwner != "" {
			cleanupCtx, cleanupCancel := context.WithTimeout(context.Background(), 30*time.Second)
			cleanupErr := chosenClient.StopContext(cleanupCtx, user, app, gen)
			cleanupCancel()
			if cleanupErr != nil {
				guard.Abandon()
				committed = true
				return "", fmt.Errorf("commit placement: %w (cleanup outcome unknown: %v)", commitErr, cleanupErr)
			}
			return "", fmt.Errorf("commit placement: %w", commitErr)
		}
	}
	committed = true
	return in.Addr, nil
}

// Ensure implements cutover.Instances (same host placement; dual-gen burst).
func (p *PlacedDial) Ensure(ctx context.Context, user, app, gen, image, tier string, noIdle bool) error {
	_, err := p.EnsureAddrTier(ctx, user, app, gen, image, tier, noIdle)
	return err
}

// Stop implements cutover.Instances.
func (p *PlacedDial) Stop(ctx context.Context, user, app, gen string) error {
	guard, err := placement.AcquireGuard(ctx, p.Placement, user, app, "stop", p.LeaseTTL)
	if err != nil {
		return err
	}
	committed := false
	defer func() {
		if !committed {
			releasePlacementGuard(guard)
		}
	}()
	if guard.HostID() == "" {
		return fmt.Errorf("no placement for %s/%s", user, app)
	}
	c, _, err := p.resolve(guard.HostID(), user, app, false)
	if err != nil {
		return err
	}
	if err := c.StopContext(guard.Context(), user, app, gen); err != nil {
		return err
	}
	record, _, err := p.Placement.GetRecord(guard.Context(), user, app)
	if err != nil {
		return err
	}
	commitCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	err = guard.CommitState(commitCtx, guard.HostID(), placement.RemoveGeneration(record.Generations, gen))
	cancel()
	if err != nil {
		return err
	}
	committed = true
	return nil
}

// SetNoIdle changes the active-operation hold on the placed generation.
func (p *PlacedDial) SetNoIdle(ctx context.Context, user, app, gen string, noIdle bool) error {
	guard, err := placement.AcquireGuard(ctx, p.Placement, user, app, "no-idle", p.LeaseTTL)
	if err != nil {
		return err
	}
	defer releasePlacementGuard(guard)
	if guard.HostID() == "" {
		return fmt.Errorf("no placement for %s/%s", user, app)
	}
	c, _, err := p.resolve(guard.HostID(), user, app, false)
	if err != nil {
		return err
	}
	return c.SetNoIdleContext(guard.Context(), user, app, gen, noIdle)
}

// StatusView reads the currently placed generation without changing placement.
func (p *PlacedDial) StatusView(ctx context.Context, user, app, gen string) (InstanceView, bool, error) {
	record, ok, err := p.Placement.GetRecord(ctx, user, app)
	if err != nil || !ok {
		return InstanceView{}, false, err
	}
	client, _, err := p.resolve(record.HostID, user, app, false)
	if err != nil {
		return InstanceView{}, false, err
	}
	view, found, err := client.StatusContext(ctx, user, app, gen)
	if err != nil || !found {
		return view, found, err
	}
	for _, generation := range record.Generations {
		if generation.Gen == gen && generation.SSHHostPublicKey != "" &&
			generation.SSHHostPublicKey != view.SSHHostPublicKey {
			return InstanceView{}, false, fmt.Errorf("agent SSH host key does not match durable placement")
		}
	}
	return view, true, nil
}

func releasePlacementGuard(guard *placement.Guard) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	_ = guard.Release(ctx)
}
