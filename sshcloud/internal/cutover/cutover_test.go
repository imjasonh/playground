package cutover_test

import (
	"context"
	"strconv"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/cutover"
	"github.com/imjasonh/playground/sshcloud/internal/session"
	"github.com/imjasonh/playground/sshcloud/internal/store"
)

type fakeInst struct {
	mu      sync.Mutex
	ensured []string
	images  []string
	noIdle  []bool
	stopped []string
	holds   []string
}

func (f *fakeInst) Ensure(_ context.Context, user, app, gen, image, tier string, noIdle bool) error {
	f.mu.Lock()
	defer f.mu.Unlock()
	f.ensured = append(f.ensured, user+"/"+app+"@"+gen)
	f.images = append(f.images, image)
	f.noIdle = append(f.noIdle, noIdle)
	return nil
}

func (f *fakeInst) SetNoIdle(_ context.Context, user, app, gen string, noIdle bool) error {
	f.mu.Lock()
	defer f.mu.Unlock()
	f.holds = append(f.holds, user+"/"+app+"@"+gen+"="+strconv.FormatBool(noIdle))
	return nil
}

func (f *fakeInst) Stop(_ context.Context, user, app, gen string) error {
	f.mu.Lock()
	defer f.mu.Unlock()
	f.stopped = append(f.stopped, user+"/"+app+"@"+gen)
	return nil
}

func setup(t *testing.T) (context.Context, *store.Memory, *session.Registry, *fakeInst, *cutover.Controller) {
	t.Helper()
	ctx := context.Background()
	st := store.NewMemory()
	if err := st.CreateUser(ctx, "alice", "SHA256:a"); err != nil {
		t.Fatal(err)
	}
	if err := st.UpsertApp(ctx, store.App{Owner: "alice", Name: "myapp", Image: "ghcr.io/example/old@sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", Tier: "tiny"}); err != nil {
		t.Fatal(err)
	}
	sess := session.NewRegistry()
	fi := &fakeInst{}
	c := cutover.New(st, sess, fi)
	c.Timeout = 30 * time.Millisecond
	return ctx, st, sess, fi, c
}

func TestKickCutover(t *testing.T) {
	ctx, st, sess, fi, c := setup(t)
	old, err := sess.Admit("alice", "myapp", "")
	if err != nil {
		t.Fatal(err)
	}
	var cancelled atomic.Bool
	_, cancel := contextWithCancelFlag(&cancelled)
	sess.BindCancel(old, cancel)

	newImg := "ghcr.io/example/new@sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
	res, err := c.Deploy(ctx, cutover.Request{
		User: "alice", App: "myapp",
		Image:    newImg,
		Strategy: store.StrategyKick,
	})
	if err != nil {
		t.Fatal(err)
	}
	if res.ActiveGen == "" || res.DrainingGen != "" {
		t.Fatalf("result %+v", res)
	}
	if !cancelled.Load() {
		t.Fatal("expected kick cancel")
	}
	app, _ := st.GetApp(ctx, "alice", "myapp")
	if app.ActiveGen != res.ActiveGen || app.DrainingGen != "" {
		t.Fatalf("app %+v", app)
	}
	if app.Image != newImg || app.PreviousImage == "" {
		t.Fatalf("images %+v", app)
	}
	if len(fi.stopped) == 0 {
		t.Fatal("expected stop of old generation")
	}
	if len(fi.images) == 0 || fi.images[0] != newImg {
		t.Fatalf("expected image on boot: %v", fi.images)
	}
}

func TestDrainWaitsForRelease(t *testing.T) {
	ctx, st, sess, fi, c := setup(t)
	app, _ := st.GetApp(ctx, "alice", "myapp")
	app.ActiveGen = "gold"
	if err := st.UpsertApp(ctx, *app); err != nil {
		t.Fatal(err)
	}
	sid, err := sess.Admit("alice", "myapp", "gold")
	if err != nil {
		t.Fatal(err)
	}

	res, err := c.Deploy(ctx, cutover.Request{
		User: "alice", App: "myapp",
		Image:    "ghcr.io/example/new@sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
		Strategy: store.StrategyDrain,
		Timeout:  time.Hour,
	})
	if err != nil {
		t.Fatal(err)
	}
	if res.DrainingGen != "gold" || res.ActiveGen == "" || res.ActiveGen == "gold" {
		t.Fatalf("result %+v", res)
	}
	newSess, err := sess.Admit("alice", "myapp", res.ActiveGen)
	if err != nil {
		t.Fatal(err)
	}
	_ = fi.SetNoIdle(ctx, "alice", "myapp", res.ActiveGen, true)
	fi.mu.Lock()
	holdsBeforeRelease := len(fi.holds)
	fi.mu.Unlock()

	sess.Release(sid)
	c.OnRelease(ctx, "alice", "myapp", "gold")
	fi.mu.Lock()
	holdsAfterRelease := len(fi.holds)
	fi.mu.Unlock()
	if holdsAfterRelease != holdsBeforeRelease {
		t.Fatalf("finishing old drain cleared active generation hold: %v", fi.holds)
	}

	app, _ = st.GetApp(ctx, "alice", "myapp")
	if app.DrainingGen != "" || app.DrainUntilUnix != 0 {
		t.Fatalf("drain not finished: %+v", app)
	}
	stopped := false
	for _, s := range fi.stopped {
		if s == "alice/myapp@gold" {
			stopped = true
		}
	}
	if !stopped {
		t.Fatalf("stopped=%v", fi.stopped)
	}
	sess.Release(newSess)
}

func TestDrainTimeoutKicks(t *testing.T) {
	ctx, _, sess, _, c := setup(t)
	appStore := c.Store
	app, _ := appStore.GetApp(ctx, "alice", "myapp")
	app.ActiveGen = "gold"
	_ = appStore.UpsertApp(ctx, *app)
	sid, err := sess.Admit("alice", "myapp", "gold")
	if err != nil {
		t.Fatal(err)
	}
	var cancelled atomic.Bool
	_, cancel := contextWithCancelFlag(&cancelled)
	sess.BindCancel(sid, cancel)

	_, err = c.Deploy(ctx, cutover.Request{
		User: "alice", App: "myapp", Strategy: store.StrategyDrain, Timeout: 20 * time.Millisecond,
		Image: "ghcr.io/example/new@sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
	})
	if err != nil {
		t.Fatal(err)
	}
	deadline := time.Now().Add(2 * time.Second)
	for time.Now().Before(deadline) {
		if cancelled.Load() {
			break
		}
		time.Sleep(10 * time.Millisecond)
	}
	if !cancelled.Load() {
		t.Fatal("expected timeout kick")
	}
}

func TestDrainNoSessionIsImmediate(t *testing.T) {
	ctx, st, _, fi, c := setup(t)
	res, err := c.Deploy(ctx, cutover.Request{
		User: "alice", App: "myapp", Strategy: store.StrategyDrain,
		Image: "ghcr.io/example/new@sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
	})
	if err != nil {
		t.Fatal(err)
	}
	if res.DrainingGen != "" || res.ActiveGen == "" {
		t.Fatalf("result %+v", res)
	}
	app, _ := st.GetApp(ctx, "alice", "myapp")
	if app.DrainingGen != "" || app.ActiveGen != res.ActiveGen {
		t.Fatalf("app %+v", app)
	}
	if len(fi.stopped) == 0 {
		t.Fatal("expected stop of empty old gen")
	}
}

func TestSameImageAndTierDeployIsIdempotent(t *testing.T) {
	ctx, st, _, fi, c := setup(t)
	img := "ghcr.io/example/new@sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
	first, err := c.Deploy(ctx, cutover.Request{
		User: "alice", App: "myapp", Image: img, Tier: "tiny", Strategy: store.StrategyKick,
	})
	if err != nil {
		t.Fatal(err)
	}
	fi.mu.Lock()
	boots := len(fi.ensured)
	fi.mu.Unlock()

	second, err := c.Deploy(ctx, cutover.Request{
		User: "alice", App: "myapp", Image: img, Tier: "tiny", Strategy: store.StrategyDrain,
	})
	if err != nil {
		t.Fatal(err)
	}
	fi.mu.Lock()
	gotBoots := len(fi.ensured)
	fi.mu.Unlock()
	if gotBoots != boots {
		t.Fatalf("same image+tier deploy touched runtime: %d → %d", boots, gotBoots)
	}
	if second.ActiveGen != first.ActiveGen {
		t.Fatalf("generation changed: %s → %s", first.ActiveGen, second.ActiveGen)
	}
	app, _ := st.GetApp(ctx, "alice", "myapp")
	if app.SessionStrategy != store.StrategyKick || second.Strategy != store.StrategyKick {
		t.Fatalf("same image+tier deploy mutated strategy: app=%+v result=%+v", app, second)
	}
}

func contextWithCancelFlag(flag *atomic.Bool) (context.Context, context.CancelFunc) {
	ctx, cancel := context.WithCancel(context.Background())
	return ctx, func() {
		flag.Store(true)
		cancel()
	}
}
