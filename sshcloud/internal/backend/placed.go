package backend

import (
	"context"
	"fmt"

	"github.com/imjasonh/playground/sshcloud/internal/placement"
)

// PlacedDial resolves (user, app) → host agent via placement, then Ensures.
type PlacedDial struct {
	Placement   placement.Store
	Agents      map[string]*AgentClient // hostID → client
	DefaultHost string                  // used when no placement yet
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
		if host == "" {
			return "", fmt.Errorf("no placement for %s/%s and no DefaultHost", user, app)
		}
		if err := p.Placement.Set(ctx, user, app, host); err != nil {
			return "", err
		}
	}
	c, ok := p.Agents[host]
	if !ok {
		return "", fmt.Errorf("unknown host %q for %s/%s", host, user, app)
	}
	return c.Addr(user, app)
}
