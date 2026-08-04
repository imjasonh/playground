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

// Addr implements gateway.DialFunc.
func (p *PlacedDial) Addr(user, app string) (string, error) {
	ctx := context.Background()
	host, ok, err := p.Placement.Get(ctx, user, app)
	if err != nil {
		return "", err
	}
	if !ok {
		host = p.DefaultHost
		if host == "" && p.Agents != nil {
			host = p.Agents.DefaultHost()
		}
		if host == "" {
			return "", fmt.Errorf("no placement for %s/%s and no DefaultHost", user, app)
		}
		if err := p.Placement.Set(ctx, user, app, host); err != nil {
			return "", err
		}
	}
	if p.Agents == nil {
		return "", fmt.Errorf("unknown host %q for %s/%s", host, user, app)
	}
	c, ok := p.Agents.Get(host)
	if !ok {
		return "", fmt.Errorf("unknown host %q for %s/%s", host, user, app)
	}
	return c.Addr(user, app)
}
