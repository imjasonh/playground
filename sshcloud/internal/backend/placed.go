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
	var choices []HostCandidate
	if host := guard.HostID(); host != "" {
		if client, ok := p.Agents.Get(host); ok {
			choices = append(choices, HostCandidate{ID: host, Client: client})
			excluded[host] = true
		}
	}
	candidates, candidateErr := p.Agents.Candidates(guard.Context(), tier, excluded)
	if candidateErr != nil && len(choices) == 0 {
		return "", candidateErr
	}
	choices = append(choices, candidates...)
	if len(choices) == 0 {
		return "", fmt.Errorf("no host has capacity for %s/%s tier %s", user, app, tier)
	}
	var (
		in      InstanceView
		host    string
		lastErr error
	)
	for _, choice := range choices {
		in, err = choice.Client.EnsureTierContext(guard.Context(), user, app, gen, image, tier, noIdle)
		if err == nil {
			host = choice.ID
			break
		}
		var capacity ErrAgentCapacity
		if !errors.As(err, &capacity) {
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
	commitCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	commitErr := guard.Commit(commitCtx, host)
	cancel()
	if commitErr != nil {
		checkCtx, checkCancel := context.WithTimeout(context.Background(), 10*time.Second)
		record, ok, checkErr := p.Placement.GetRecord(checkCtx, user, app)
		checkCancel()
		if checkErr != nil || !ok || record.HostID != host || record.LeaseOwner != "" {
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
	defer releasePlacementGuard(guard)
	if guard.HostID() == "" {
		return fmt.Errorf("no placement for %s/%s", user, app)
	}
	c, _, err := p.resolve(guard.HostID(), user, app, false)
	if err != nil {
		return err
	}
	return c.StopContext(guard.Context(), user, app, gen)
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

func releasePlacementGuard(guard *placement.Guard) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	_ = guard.Release(ctx)
}
