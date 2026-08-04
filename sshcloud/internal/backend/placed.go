package backend

import (
	"context"
	"fmt"

	"github.com/imjasonh/playground/sshcloud/internal/placement"
)

// PlacedDial resolves (user, app) → host agent via placement, then Ensures.
type PlacedDial struct {
	Placement   placement.Store
	Agents      *HostSet
	DefaultHost string // used when no placement yet; empty falls back to Agents.DefaultHost
}

func (p *PlacedDial) agent(ctx context.Context, user, app string) (*AgentClient, string, bool, error) {
	host, ok, err := p.Placement.Get(ctx, user, app)
	if err != nil {
		return nil, "", false, err
	}
	needsPlacement := !ok
	if !ok {
		host = p.DefaultHost
		if host == "" && p.Agents != nil {
			host = p.Agents.DefaultHost()
		}
		if host == "" {
			return nil, "", false, fmt.Errorf("no placement for %s/%s and no DefaultHost", user, app)
		}
	}
	if p.Agents == nil {
		return nil, "", false, fmt.Errorf("unknown host %q for %s/%s", host, user, app)
	}
	c, ok := p.Agents.Get(host)
	if !ok {
		replacement := p.DefaultHost
		if replacement == "" || replacement == host {
			replacement = p.Agents.DefaultHost()
		}
		if replacement == "" || replacement == host {
			return nil, "", false, fmt.Errorf("placed host %q is gone and no replacement is ready for %s/%s", host, user, app)
		}
		c, ok = p.Agents.Get(replacement)
		if !ok {
			return nil, "", false, fmt.Errorf("replacement host %q is not ready for %s/%s", replacement, user, app)
		}
		host = replacement
		needsPlacement = true
	}
	return c, host, needsPlacement, nil
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
	c, host, needsPlacement, err := p.agent(ctx, user, app)
	if err != nil {
		return "", err
	}
	in, err := c.EnsureTierContext(ctx, user, app, gen, image, tier, noIdle)
	if err != nil {
		return "", err
	}
	if needsPlacement {
		if err := p.Placement.Set(ctx, user, app, host); err != nil {
			return "", fmt.Errorf("commit placement: %w", err)
		}
	}
	return in.Addr, nil
}

// Ensure implements cutover.Instances (same host placement; dual-gen burst).
func (p *PlacedDial) Ensure(ctx context.Context, user, app, gen, image, tier string, noIdle bool) error {
	_, err := p.EnsureAddrTier(ctx, user, app, gen, image, tier, noIdle)
	return err
}

// Stop implements cutover.Instances.
func (p *PlacedDial) Stop(ctx context.Context, user, app, gen string) error {
	c, _, needsPlacement, err := p.agent(ctx, user, app)
	if err != nil {
		return err
	}
	if needsPlacement {
		return fmt.Errorf("no placement for %s/%s", user, app)
	}
	return c.StopContext(ctx, user, app, gen)
}

// SetNoIdle changes the active-operation hold on the placed generation.
func (p *PlacedDial) SetNoIdle(ctx context.Context, user, app, gen string, noIdle bool) error {
	c, _, needsPlacement, err := p.agent(ctx, user, app)
	if err != nil {
		return err
	}
	if needsPlacement {
		return fmt.Errorf("no placement for %s/%s", user, app)
	}
	return c.SetNoIdleContext(ctx, user, app, gen, noIdle)
}
