package cutover_test

import (
	"context"
	"errors"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/cutover"
	"github.com/imjasonh/playground/sshcloud/internal/session"
	"github.com/imjasonh/playground/sshcloud/internal/store"
)

type faultStore struct {
	store.Store
	upsertErr error
	failAt    int
	upserts   int
}

func (s *faultStore) UpsertApp(ctx context.Context, app store.App) error {
	s.upserts++
	if s.upsertErr != nil && (s.failAt == 0 || s.upserts == s.failAt) {
		return s.upsertErr
	}
	return s.Store.UpsertApp(ctx, app)
}

type faultInstances struct {
	mu sync.Mutex

	ensureErr  error
	holdErrGen string
	stopErr    error
	ensured    []string
	stopped    []string

	ensureEntered chan struct{}
	releaseEnsure chan struct{}
}

func (f *faultInstances) Ensure(_ context.Context, user, app, gen, _, _ string, _ bool) error {
	f.mu.Lock()
	f.ensured = append(f.ensured, user+"/"+app+"@"+gen)
	entered, release := f.ensureEntered, f.releaseEnsure
	err := f.ensureErr
	f.mu.Unlock()
	if entered != nil {
		select {
		case entered <- struct{}{}:
		default:
		}
	}
	if release != nil {
		<-release
	}
	return err
}

func (f *faultInstances) Stop(_ context.Context, user, app, gen string) error {
	f.mu.Lock()
	defer f.mu.Unlock()
	f.stopped = append(f.stopped, user+"/"+app+"@"+gen)
	return f.stopErr
}

func (f *faultInstances) SetNoIdle(_ context.Context, _, _, gen string, noIdle bool) error {
	if noIdle && gen == f.holdErrGen {
		return errors.New("injected hold failure")
	}
	return nil
}

func (f *faultInstances) calls() (ensured, stopped []string) {
	f.mu.Lock()
	defer f.mu.Unlock()
	return append([]string(nil), f.ensured...), append([]string(nil), f.stopped...)
}

func faultSetup(t *testing.T) (context.Context, *store.Memory, *session.Registry) {
	t.Helper()
	ctx := context.Background()
	mem := store.NewMemory()
	if err := mem.CreateUser(ctx, "alice", "SHA256:alice"); err != nil {
		t.Fatal(err)
	}
	return ctx, mem, session.NewRegistry()
}

func chaosImage(hexDigit string) string {
	return "ghcr.io/example/app@sha256:" + strings.Repeat(hexDigit, 64)
}

func TestDeployPersistenceFailureCleansNewGeneration(t *testing.T) {
	t.Parallel()
	ctx, mem, sessions := faultSetup(t)
	old := store.App{
		Owner: "alice", Name: "myapp", Image: chaosImage("a"),
		Tier: "tiny", ActiveGen: "gold",
	}
	if err := mem.UpsertApp(ctx, old); err != nil {
		t.Fatal(err)
	}
	fault := &faultStore{Store: mem, upsertErr: errors.New("injected store failure"), failAt: 2}
	instances := &faultInstances{}
	controller := cutover.New(fault, sessions, instances)

	_, err := controller.Deploy(ctx, cutover.Request{
		User: "alice", App: "myapp", Image: chaosImage("b"),
		Tier: "tiny", Strategy: store.StrategyKick,
	})
	if err == nil {
		t.Fatal("expected persistence failure")
	}
	ensured, stopped := instances.calls()
	if len(ensured) != 1 || len(stopped) != 1 {
		t.Fatalf("new generation was not compensated: ensured=%v stopped=%v", ensured, stopped)
	}
	got, _ := mem.GetApp(ctx, "alice", "myapp")
	if got.ActiveGen != old.ActiveGen || got.Image != old.Image {
		t.Fatalf("failed deploy changed routing: %+v", got)
	}
}

func TestDrainHoldFailureLeavesOldRoutingAndCleansNew(t *testing.T) {
	t.Parallel()
	ctx, mem, sessions := faultSetup(t)
	old := store.App{
		Owner: "alice", Name: "myapp", Image: chaosImage("c"),
		Tier: "tiny", ActiveGen: "gold",
	}
	if err := mem.UpsertApp(ctx, old); err != nil {
		t.Fatal(err)
	}
	sessionID, err := sessions.Admit("alice", "myapp", "gold")
	if err != nil {
		t.Fatal(err)
	}
	defer sessions.Release(sessionID)
	instances := &faultInstances{holdErrGen: "gold"}
	controller := cutover.New(mem, sessions, instances)

	_, err = controller.Deploy(ctx, cutover.Request{
		User: "alice", App: "myapp", Image: chaosImage("d"),
		Tier: "tiny", Strategy: store.StrategyDrain,
	})
	if err == nil {
		t.Fatal("expected old-generation hold failure")
	}
	_, stopped := instances.calls()
	if len(stopped) != 1 {
		t.Fatalf("new generation was not stopped: %v", stopped)
	}
	got, _ := mem.GetApp(ctx, "alice", "myapp")
	if got.ActiveGen != "gold" || got.DrainingGen != "" || got.Image != old.Image {
		t.Fatalf("failed drain changed routing: %+v", got)
	}
}

func TestDeployAndAdmissionLinearizeAtCommit(t *testing.T) {
	t.Parallel()
	ctx, mem, sessions := faultSetup(t)
	if err := mem.UpsertApp(ctx, store.App{
		Owner: "alice", Name: "myapp", Image: chaosImage("e"),
		Tier: "tiny", ActiveGen: "gold",
	}); err != nil {
		t.Fatal(err)
	}
	instances := &faultInstances{
		ensureEntered: make(chan struct{}, 1),
		releaseEnsure: make(chan struct{}),
	}
	controller := cutover.New(mem, sessions, instances)
	deployDone := make(chan cutover.Result, 1)
	deployErr := make(chan error, 1)
	go func() {
		result, err := controller.Deploy(ctx, cutover.Request{
			User: "alice", App: "myapp", Image: chaosImage("f"),
			Tier: "tiny", Strategy: store.StrategyKick,
		})
		if err != nil {
			deployErr <- err
			return
		}
		deployDone <- result
	}()
	select {
	case <-instances.ensureEntered:
	case <-time.After(2 * time.Second):
		t.Fatal("deploy did not reach Ensure")
	}

	type admission struct {
		id    session.ID
		gen   string
		image string
		err   error
	}
	admitted := make(chan admission, 1)
	admitStarted := make(chan struct{})
	go func() {
		close(admitStarted)
		id, gen, image, _, err := controller.Admit(ctx, "alice", "myapp")
		admitted <- admission{id: id, gen: gen, image: image, err: err}
	}()
	<-admitStarted
	select {
	case got := <-admitted:
		t.Fatalf("admission escaped in-flight deploy lock: %+v", got)
	case <-time.After(25 * time.Millisecond):
	}
	close(instances.releaseEnsure)

	var deployed cutover.Result
	select {
	case err := <-deployErr:
		t.Fatal(err)
	case deployed = <-deployDone:
	case <-time.After(2 * time.Second):
		t.Fatal("deploy did not finish")
	}
	select {
	case got := <-admitted:
		if got.err != nil {
			t.Fatal(got.err)
		}
		defer sessions.Release(got.id)
		if got.gen != deployed.ActiveGen || got.image != chaosImage("f") {
			t.Fatalf("admission was not pinned to committed deploy: %+v deploy=%+v", got, deployed)
		}
	case <-time.After(2 * time.Second):
		t.Fatal("admission did not resume")
	}
}

func TestReconcileRetainsDrainUntilStopSucceeds(t *testing.T) {
	t.Parallel()
	ctx, mem, sessions := faultSetup(t)
	if err := mem.UpsertApp(ctx, store.App{
		Owner: "alice", Name: "myapp", Image: chaosImage("a"), Tier: "tiny",
		ActiveGen: "gnew", DrainingGen: "gold", DrainUntilUnix: time.Now().Add(time.Minute).Unix(),
	}); err != nil {
		t.Fatal(err)
	}
	instances := &faultInstances{stopErr: errors.New("injected stop failure")}
	controller := cutover.New(mem, sessions, instances)
	if err := controller.Reconcile(ctx); err == nil {
		t.Fatal("expected cleanup failure")
	}
	app, _ := mem.GetApp(ctx, "alice", "myapp")
	if app.DrainingGen != "gold" {
		t.Fatalf("cleanup reference was lost: %+v", app)
	}
	instances.mu.Lock()
	instances.stopErr = nil
	instances.mu.Unlock()
	if err := controller.Reconcile(ctx); err != nil {
		t.Fatal(err)
	}
	app, _ = mem.GetApp(ctx, "alice", "myapp")
	if app.DrainingGen != "" {
		t.Fatalf("drain was not reconciled: %+v", app)
	}
}
