// Package migrate moves a snapshotted instance from one host agent to another.
package migrate

import (
	"context"
	"fmt"
	"sync"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
)

// Migrator performs cross-host snapshot migrate.
type Migrator struct {
	Placement    placement.Store
	Hosts        *backend.HostSet
	Gateway      *backend.GatewayClient
	FreezeWindow time.Duration

	mu  sync.Mutex
	ops map[string]*sync.Mutex
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
	op := m.appLock(user, app)
	op.Lock()
	defer op.Unlock()
	guard, err := placement.AcquireGuard(ctx, m.Placement, user, app, "migrate", placement.DefaultLeaseTTL)
	if err != nil {
		return Result{}, err
	}
	committed := false
	defer func() {
		if !committed {
			releaseGuard(guard)
		}
	}()
	target, ok := m.Hosts.Get(toHost)
	if !ok {
		return Result{}, fmt.Errorf("unknown target host %q", toHost)
	}

	fromHost := guard.HostID()
	if fromHost == "" {
		return Result{}, fmt.Errorf("no placement for %s/%s", user, app)
	}
	if fromHost == toHost {
		st, found, err := target.StatusContext(guard.Context(), user, app, gen)
		if err != nil {
			return Result{}, err
		}
		if found && st.State == "running" {
			releaseGuard(guard)
			committed = true
			return Result{FromHost: fromHost, ToHost: toHost, Gen: gen, Addr: st.Addr}, nil
		}
		return Result{}, fmt.Errorf("already placed on %s but not running", toHost)
	}
	source, ok := m.Hosts.Get(fromHost)
	if !ok {
		return Result{}, fmt.Errorf("unknown source host %q", fromHost)
	}
	freezeToken := ""
	thawed := false
	if m.Gateway != nil {
		window := m.FreezeWindow
		if window <= 0 {
			window = 30 * time.Second
		}
		token, _, err := m.Gateway.Freeze(guard.Context(), user, app, gen, window)
		if err != nil {
			return Result{}, fmt.Errorf("freeze session: %w", err)
		}
		freezeToken = token
		if err := source.SetNoIdleContext(guard.Context(), user, app, gen, false); err != nil {
			return Result{}, fmt.Errorf("release session hold: %w", err)
		}
		defer func() {
			if freezeToken != "" && !thawed {
				thawCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
				_ = m.Gateway.Thaw(thawCtx, freezeToken)
				cancel()
			}
		}()
	}

	if err := source.SleepContext(guard.Context(), user, app, gen); err != nil {
		return Result{}, fmt.Errorf("source sleep: %w", err)
	}
	if err := source.EvictContext(guard.Context(), user, app, gen); err != nil {
		return Result{}, fmt.Errorf("source evict: %w", err)
	}

	adopted, err := target.AdoptContext(guard.Context(), user, app, gen)
	if err != nil {
		// The target may have applied Adopt before its response was lost. Resolve
		// that ambiguity before restoring a second copy on the source.
		recoveryCtx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
		defer cancel()
		if status, found, statusErr := target.StatusContext(recoveryCtx, user, app, gen); statusErr == nil && found && status.State == "running" {
			adopted = status
		} else {
			_, rollbackErr := source.AdoptContext(recoveryCtx, user, app, gen)
			if rollbackErr == nil {
				return Result{}, fmt.Errorf("target adopt: %w (instance restored on %s)", err, fromHost)
			}
			return Result{}, fmt.Errorf("target adopt: %w (source rollback failed: %v)", err, rollbackErr)
		}
	}
	commitCtx, cancelCommit := context.WithTimeout(context.Background(), 10*time.Second)
	err = guard.Commit(commitCtx, toHost)
	cancelCommit()
	if err != nil {
		checkCtx, checkCancel := context.WithTimeout(context.Background(), 10*time.Second)
		record, ok, checkErr := m.Placement.GetRecord(checkCtx, user, app)
		checkCancel()
		if checkErr == nil && ok && record.HostID == toHost && record.LeaseOwner == "" {
			committed = true
			err = nil
		}
	}
	if err != nil {
		recoveryCtx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
		defer cancel()
		rollbackErr := target.SleepContext(recoveryCtx, user, app, gen)
		if rollbackErr == nil {
			rollbackErr = target.EvictContext(recoveryCtx, user, app, gen)
		}
		if rollbackErr == nil {
			_, rollbackErr = source.AdoptContext(recoveryCtx, user, app, gen)
		}
		if rollbackErr == nil {
			return Result{}, fmt.Errorf("placement update: %w (instance restored on %s)", err, fromHost)
		}
		return Result{}, fmt.Errorf("placement update: %w (rollback failed: %v)", err, rollbackErr)
	}
	committed = true
	if freezeToken != "" {
		thawCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		if err := m.Gateway.Thaw(thawCtx, freezeToken); err != nil {
			cancel()
			return Result{}, fmt.Errorf("migration committed but thaw failed: %w", err)
		}
		cancel()
		thawed = true
	}
	return Result{FromHost: fromHost, ToHost: toHost, Gen: gen, Addr: adopted.Addr}, nil
}

func (m *Migrator) appLock(user, app string) *sync.Mutex {
	key := user + "/" + app
	m.mu.Lock()
	defer m.mu.Unlock()
	if m.ops == nil {
		m.ops = make(map[string]*sync.Mutex)
	}
	op := m.ops[key]
	if op == nil {
		op = &sync.Mutex{}
		m.ops[key] = op
	}
	return op
}

func releaseGuard(guard *placement.Guard) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	_ = guard.Release(ctx)
}
