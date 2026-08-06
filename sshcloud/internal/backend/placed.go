package backend

import (
	"context"
	"errors"
	"fmt"
	"sync"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/agent"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
	"github.com/imjasonh/playground/sshcloud/internal/quota"
)

// PlacedDial resolves (user, app) → host agent via placement, then Ensures.
type PlacedDial struct {
	Placement       placement.Store
	Agents          *HostSet
	LeaseTTL        time.Duration
	Quotas          quota.Store
	MaxAwakePerUser int
	WakesPerHour    int
	startMu         sync.Mutex
	startUsers      map[string]*sync.Mutex
}

func (p *PlacedDial) resolve(host, hostInstanceID, user, app string) (*AgentClient, string, error) {
	if p.Agents == nil {
		return nil, "", fmt.Errorf("no agents available for %s/%s", user, app)
	}
	if host == "" {
		return nil, "", fmt.Errorf("no placement for %s/%s", user, app)
	}
	c, ok := p.Agents.Get(host)
	if !ok {
		return nil, "", fmt.Errorf("placed host %q is unavailable for %s/%s", host, user, app)
	}
	if hostInstanceID != "" && c.InstanceID != hostInstanceID {
		return nil, "", fmt.Errorf("placed host %q incarnation changed for %s/%s", host, user, app)
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
	return p.EnsureAddrTierWithOptions(ctx, user, app, gen, image, tier, noIdle, StartOptions{
		Purpose: "session", RequestID: placement.NewLeaseOwner("session"),
	})
}

type StartOptions struct {
	Purpose   string
	RequestID string
}

func (p *PlacedDial) EnsureAddrTierWithOptions(ctx context.Context, user, app, gen, image, tier string, noIdle bool, options StartOptions) (string, error) {
	if p.Agents == nil {
		return "", fmt.Errorf("no agents available for %s/%s", user, app)
	}
	if options.RequestID == "" {
		return "", fmt.Errorf("stable start operation ID is required")
	}
	unlockStart := p.lockStart(user)
	defer unlockStart()
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
		if guard.HostInstanceID() != "" && client.InstanceID != guard.HostInstanceID() {
			return "", fmt.Errorf("placed host %q incarnation changed for %s/%s; explicit recovery is required", host, user, app)
		}
		choices = append(choices, HostCandidate{ID: host, InstanceID: client.InstanceID, Client: client})
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
	alreadyRunning := false
	if originalHost != "" {
		status, found, err := choices[0].Client.StatusContext(guard.Context(), user, app, gen)
		if err != nil {
			return "", err
		}
		alreadyRunning = found && status.State == "running"
	}
	if !alreadyRunning {
		if err := p.admitStart(guard.Context(), user, app, gen, options); err != nil {
			return "", err
		}
	}
	var (
		in           InstanceView
		host         string
		chosenClient *AgentClient
		lastErr      error
	)
	for _, choice := range choices {
		if err := guard.Mark(guard.Context(), placement.Operation{
			Kind: "ensure", Phase: "ensuring", TargetHost: choice.ID,
			TargetInstanceID: choice.InstanceID,
			Generations:      []string{gen}, Desired: generations,
		}); err != nil {
			return "", err
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
	if err := chosenClient.VerifyServerIdentity(guard.Context()); err != nil {
		guard.Abandon()
		committed = true
		return "", fmt.Errorf("verify ensured host before placement commit: %w", err)
	}
	if err := guard.Mark(guard.Context(), placement.Operation{
		Kind: "ensure", Phase: "ready", TargetHost: host,
		TargetInstanceID: chosenClient.InstanceID,
		Generations:      []string{gen}, Desired: generations,
	}); err != nil {
		guard.Abandon()
		committed = true
		return "", fmt.Errorf("persist ensured generation identity: %w", err)
	}
	if originalHost != "" {
		commitCtx, commitCancel := context.WithTimeout(context.Background(), 10*time.Second)
		err := guard.CommitStateIdentity(commitCtx, originalHost, chosenClient.InstanceID, generations)
		commitCancel()
		if err != nil {
			return "", fmt.Errorf("release placement lease: %w", err)
		}
		committed = true
		return in.Addr, nil
	}
	commitCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	commitErr := guard.CommitStateIdentity(commitCtx, host, chosenClient.InstanceID, generations)
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
		if record.HostID != host || record.HostInstanceID != chosenClient.InstanceID || record.LeaseOwner != "" {
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
	_, err := p.EnsureAddrTierWithOptions(ctx, user, app, gen, image, tier, noIdle, StartOptions{
		Purpose: "deploy", RequestID: gen,
	})
	return err
}

// Stop implements cutover.Instances.
func (p *PlacedDial) Stop(ctx context.Context, user, app, gen string) error {
	guard, err := placement.AcquireGuard(ctx, p.Placement, user, app, "stop", p.LeaseTTL)
	if err != nil {
		return err
	}
	finished := false
	journaled := false
	defer func() {
		if finished {
			return
		}
		if journaled {
			// Once Stop may have crossed an irreversible boundary, only the
			// reconciler may clear its durable operation record.
			guard.Abandon()
		} else {
			releasePlacementGuard(guard)
		}
	}()
	if guard.HostID() == "" {
		return fmt.Errorf("no placement for %s/%s", user, app)
	}
	c, _, err := p.resolve(guard.HostID(), guard.HostInstanceID(), user, app)
	if err != nil {
		return err
	}
	record, _, err := p.Placement.GetRecord(guard.Context(), user, app)
	if err != nil {
		return err
	}
	desired := placement.RemoveGeneration(record.Generations, gen)
	operation := placement.Operation{
		ID: guard.Owner(), Kind: "stop", Phase: "prepared",
		SourceHost: guard.HostID(), SourceInstanceID: c.InstanceID,
		Generations: []string{gen}, Desired: desired,
	}
	// Treat an error from Mark as ambiguous: Firestore may have committed the
	// journal even when the response was lost. Abandoning preserves either the
	// journal or the lease for conservative recovery.
	journaled = true
	if err := guard.Mark(guard.Context(), operation); err != nil {
		return fmt.Errorf("persist stop operation: %w", err)
	}
	operation.Phase = "stopping"
	if err := guard.Mark(guard.Context(), operation); err != nil {
		return fmt.Errorf("persist stop boundary: %w", err)
	}
	if err := c.StopContext(guard.Context(), user, app, gen); err != nil {
		operation.Phase = "unknown-stop"
		_ = markPlacementOperation(guard, operation)
		return fmt.Errorf("stop outcome unknown on %s@%s: %w", guard.HostID(), c.InstanceID, err)
	}
	if err := c.VerifyServerIdentity(guard.Context()); err != nil {
		operation.Phase = "stopped-unverified-host"
		_ = markPlacementOperation(guard, operation)
		return fmt.Errorf("verify stopped host identity: %w", err)
	}
	operation.Phase = "stopped"
	if err := guard.Mark(guard.Context(), operation); err != nil {
		return fmt.Errorf("persist completed stop: %w", err)
	}
	commitCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	err = guard.CommitStateIdentity(commitCtx, guard.HostID(), c.InstanceID, desired)
	cancel()
	if err != nil {
		checkCtx, checkCancel := context.WithTimeout(context.Background(), 10*time.Second)
		current, ok, checkErr := p.Placement.GetRecord(checkCtx, user, app)
		checkCancel()
		if checkErr == nil && ok && current.HostID == guard.HostID() &&
			current.HostInstanceID == c.InstanceID && current.LeaseOwner == "" &&
			current.Operation.Kind == "" && sameGenerations(current.Generations, desired) {
			finished = true
			return nil
		}
		if checkErr != nil {
			return fmt.Errorf("stop placement commit outcome unknown: %w (read: %v)", err, checkErr)
		}
		return fmt.Errorf("stop placement commit unresolved: %w", err)
	}
	finished = true
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
	c, _, err := p.resolve(guard.HostID(), guard.HostInstanceID(), user, app)
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
	client, _, err := p.resolve(record.HostID, record.HostInstanceID, user, app)
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

func (p *PlacedDial) lockStart(user string) func() {
	p.startMu.Lock()
	if p.startUsers == nil {
		p.startUsers = make(map[string]*sync.Mutex)
	}
	lock := p.startUsers[user]
	if lock == nil {
		lock = &sync.Mutex{}
		p.startUsers[user] = lock
	}
	p.startMu.Unlock()
	lock.Lock()
	return lock.Unlock
}

func (p *PlacedDial) admitStart(ctx context.Context, user, app, gen string, options StartOptions) error {
	inventories, err := p.Agents.Inventories(ctx)
	if err != nil {
		return err
	}
	awake := 0
	oldGenerationAwake := false
	for _, inventory := range inventories {
		for _, instance := range inventory {
			if instance.User == user && instance.State == agent.StateRunning {
				awake++
				if instance.App == app && instance.Gen != gen {
					oldGenerationAwake = true
				}
			}
		}
	}
	maxAwake := p.MaxAwakePerUser
	if maxAwake <= 0 {
		maxAwake = 2
	}
	if options.Purpose == "deploy" && oldGenerationAwake {
		maxAwake++ // one controlled old+new cutover burst
	}
	if awake >= maxAwake {
		return quota.ErrExceeded{Kind: "awake_vms", Limit: maxAwake}
	}
	if p.Quotas == nil {
		return nil
	}
	wakes := p.WakesPerHour
	if wakes <= 0 {
		wakes = 30
	}
	eventID := options.RequestID
	return p.Quotas.Take(ctx, quota.Request{
		Kind: "wake", Subject: user, EventID: eventID, At: time.Now(),
		Limit: quota.Limit{Max: wakes, Window: time.Hour},
	})
}

func releasePlacementGuard(guard *placement.Guard) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	_ = guard.Release(ctx)
}

func markPlacementOperation(guard *placement.Guard, operation placement.Operation) error {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	return guard.Mark(ctx, operation)
}

func sameGenerations(a, b []placement.Generation) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}
