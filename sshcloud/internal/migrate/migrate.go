// Package migrate moves a snapshotted instance from one host agent to another.
package migrate

import (
	"context"
	"fmt"

	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
)

// Hosts is the set of agent clients keyed by host ID.
type Hosts map[string]*backend.AgentClient

// Migrator performs cross-host snapshot migrate.
type Migrator struct {
	Placement placement.Store
	Hosts     Hosts
}

// Result is the outcome of a successful migrate.
type Result struct {
	FromHost string
	ToHost   string
	Addr     string
}

// Migrate sleeps+evicts on the source host, adopts on toHost, and updates placement.
//
//	source: Sleep → Evict (snapshot remains in shared store)
//	target: Adopt (restore + run)
//	placement: Set(toHost)
//
// On adopt failure, attempts rollback Adopt on the source host.
func (m *Migrator) Migrate(ctx context.Context, user, app, toHost string) (Result, error) {
	_ = ctx
	if user == "" || app == "" || toHost == "" {
		return Result{}, fmt.Errorf("user, app, and toHost required")
	}
	target, ok := m.Hosts[toHost]
	if !ok {
		return Result{}, fmt.Errorf("unknown target host %q", toHost)
	}

	fromHost, ok, err := m.Placement.Get(ctx, user, app)
	if err != nil {
		return Result{}, err
	}
	if !ok {
		return Result{}, fmt.Errorf("no placement for %s/%s", user, app)
	}
	if fromHost == toHost {
		st, found, err := target.Status(user, app)
		if err != nil {
			return Result{}, err
		}
		if found && st.State == "running" {
			return Result{FromHost: fromHost, ToHost: toHost, Addr: st.Addr}, nil
		}
		return Result{}, fmt.Errorf("already placed on %s but not running", toHost)
	}
	source, ok := m.Hosts[fromHost]
	if !ok {
		return Result{}, fmt.Errorf("unknown source host %q", fromHost)
	}

	if err := source.Sleep(user, app); err != nil {
		return Result{}, fmt.Errorf("source sleep: %w", err)
	}
	if err := source.Evict(user, app); err != nil {
		return Result{}, fmt.Errorf("source evict: %w", err)
	}

	adopted, err := target.Adopt(user, app)
	if err != nil {
		// Best-effort rollback onto source.
		if _, rollErr := source.Adopt(user, app); rollErr == nil {
			_ = m.Placement.Set(ctx, user, app, fromHost)
		}
		return Result{}, fmt.Errorf("target adopt: %w", err)
	}
	if err := m.Placement.Set(ctx, user, app, toHost); err != nil {
		return Result{}, fmt.Errorf("placement update: %w", err)
	}
	return Result{FromHost: fromHost, ToHost: toHost, Addr: adopted.Addr}, nil
}
