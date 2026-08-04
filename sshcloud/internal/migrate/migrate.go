// Package migrate moves a snapshotted instance from one host agent to another.
package migrate

import (
	"context"
	"fmt"

	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
)

// Migrator performs cross-host snapshot migrate.
type Migrator struct {
	Placement placement.Store
	Hosts     *backend.HostSet
}

// Result is the outcome of a successful migrate.
type Result struct {
	FromHost string
	ToHost   string
	Gen      string
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
	return m.MigrateGeneration(ctx, user, app, "", toHost)
}

// MigrateGeneration migrates one deployed generation. Empty gen selects the
// legacy singleton. Callers must coordinate draining generations separately.
func (m *Migrator) MigrateGeneration(ctx context.Context, user, app, gen, toHost string) (Result, error) {
	if user == "" || app == "" || toHost == "" {
		return Result{}, fmt.Errorf("user, app, and toHost required")
	}
	target, ok := m.Hosts.Get(toHost)
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
		st, found, err := target.StatusContext(ctx, user, app, gen)
		if err != nil {
			return Result{}, err
		}
		if found && st.State == "running" {
			return Result{FromHost: fromHost, ToHost: toHost, Gen: gen, Addr: st.Addr}, nil
		}
		return Result{}, fmt.Errorf("already placed on %s but not running", toHost)
	}
	source, ok := m.Hosts.Get(fromHost)
	if !ok {
		return Result{}, fmt.Errorf("unknown source host %q", fromHost)
	}

	if err := source.SleepContext(ctx, user, app, gen); err != nil {
		return Result{}, fmt.Errorf("source sleep: %w", err)
	}
	if err := source.EvictContext(ctx, user, app, gen); err != nil {
		return Result{}, fmt.Errorf("source evict: %w", err)
	}

	adopted, err := target.AdoptContext(ctx, user, app, gen)
	if err != nil {
		// Best-effort rollback onto source.
		if _, rollErr := source.AdoptContext(ctx, user, app, gen); rollErr == nil {
			_ = m.Placement.Set(ctx, user, app, fromHost)
		}
		return Result{}, fmt.Errorf("target adopt: %w", err)
	}
	if err := m.Placement.Set(ctx, user, app, toHost); err != nil {
		rollbackErr := target.SleepContext(ctx, user, app, gen)
		if rollbackErr == nil {
			rollbackErr = target.EvictContext(ctx, user, app, gen)
		}
		if rollbackErr == nil {
			_, rollbackErr = source.AdoptContext(ctx, user, app, gen)
		}
		if rollbackErr == nil {
			_ = m.Placement.Set(ctx, user, app, fromHost)
			return Result{}, fmt.Errorf("placement update: %w (instance restored on %s)", err, fromHost)
		}
		return Result{}, fmt.Errorf("placement update: %w (rollback failed: %v)", err, rollbackErr)
	}
	return Result{FromHost: fromHost, ToHost: toHost, Gen: gen, Addr: adopted.Addr}, nil
}
