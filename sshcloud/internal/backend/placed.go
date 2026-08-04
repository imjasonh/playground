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

func (p *PlacedDial) agent(ctx context.Context, user, app string) (*AgentClient, error) {
	host, ok, err := p.Placement.Get(ctx, user, app)
	if err != nil {
		return nil, err
	}
	if !ok {
		host = p.DefaultHost
		if host == "" && p.Agents != nil {
			host = p.Agents.DefaultHost()
		}
		if host == "" {
			return nil, fmt.Errorf("no placement for %s/%s and no DefaultHost", user, app)
		}
		if err := p.Placement.Set(ctx, user, app, host); err != nil {
			return nil, err
		}
	}
	if p.Agents == nil {
		return nil, fmt.Errorf("unknown host %q for %s/%s", host, user, app)
	}
	c, ok := p.Agents.Get(host)
	if !ok {
		return nil, fmt.Errorf("unknown host %q for %s/%s", host, user, app)
	}
	return c, nil
}

// Addr dials the placed host agent for this app generation.
func (p *PlacedDial) Addr(user, app, gen, image string) (string, error) {
	return p.EnsureAddr(context.Background(), user, app, gen, image, false)
}

// EnsureAddr boots/wakes and returns the guest SSH address.
func (p *PlacedDial) EnsureAddr(ctx context.Context, user, app, gen, image string, noIdle bool) (string, error) {
	c, err := p.agent(ctx, user, app)
	if err != nil {
		return "", err
	}
	in, err := c.Ensure(user, app, gen, image, noIdle)
	if err != nil {
		return "", err
	}
	return in.Addr, nil
}

// Ensure implements cutover.Instances (same host placement; dual-gen burst).
func (p *PlacedDial) Ensure(ctx context.Context, user, app, gen, image string, noIdle bool) error {
	_, err := p.EnsureAddr(ctx, user, app, gen, image, noIdle)
	return err
}

// Stop implements cutover.Instances.
func (p *PlacedDial) Stop(ctx context.Context, user, app, gen string) error {
	c, err := p.agent(ctx, user, app)
	if err != nil {
		return err
	}
	return c.Stop(user, app, gen)
}
