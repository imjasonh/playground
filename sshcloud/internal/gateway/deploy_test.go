package gateway_test

import (
	"bytes"
	"context"
	"errors"
	"io"
	"strings"
	"testing"

	"github.com/imjasonh/playground/sshcloud/internal/cutover"
	"github.com/imjasonh/playground/sshcloud/internal/gateway"
	"github.com/imjasonh/playground/sshcloud/internal/session"
	"github.com/imjasonh/playground/sshcloud/internal/store"
)

func TestRunDeployCreatesApp(t *testing.T) {
	ctx := context.Background()
	st := store.NewMemory()
	if err := st.CreateUser(ctx, "alice", "SHA256:alice"); err != nil {
		t.Fatal(err)
	}
	hub := &gateway.Hub{Store: st, Sessions: session.NewRegistry()}

	digest := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
	script := strings.Join([]string{
		"myapp",
		"ghcr.io/example/app@sha256:" + digest,
		"", // default tiny
		"", // default drain
		"", // press enter
	}, "\n") + "\n"

	var out bytes.Buffer
	rw := struct {
		io.Reader
		io.Writer
	}{Reader: strings.NewReader(script), Writer: &out}

	gateway.RunDeploy(ctx, rw, hub, "SHA256:alice", "alice", "")

	got := out.String()
	if !strings.Contains(got, "Created myapp") {
		t.Fatalf("output missing create: %q", got)
	}
	if !strings.Contains(got, "drain") {
		t.Fatalf("output missing strategy: %q", got)
	}

	app, err := st.GetApp(ctx, "alice", "myapp")
	if err != nil || app == nil {
		t.Fatalf("GetApp: %v %#v", err, app)
	}
	if app.Image != "ghcr.io/example/app@sha256:"+digest {
		t.Fatalf("image = %q", app.Image)
	}
	if app.Tier != "tiny" || app.SessionStrategy != store.StrategyDrain {
		t.Fatalf("app = %+v", app)
	}

	// Deep-link route should now resolve to the app.
	r, err := hub.HandleConnect(ctx, gateway.Connect{SSHUser: "myapp", KeyFingerprint: "SHA256:alice"})
	if err != nil || r.Action != gateway.ActionProxyApp || r.App != "myapp" {
		t.Fatalf("connect myapp: %+v %v", r, err)
	}
	hub.ReleaseSession(r.Session)
}

func TestRunDeployRejectsUnpinned(t *testing.T) {
	ctx := context.Background()
	st := store.NewMemory()
	if err := st.CreateUser(ctx, "alice", "SHA256:alice"); err != nil {
		t.Fatal(err)
	}
	hub := &gateway.Hub{Store: st, Sessions: session.NewRegistry()}

	digest := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
	// bad image, then good; empty tier/strategy; enter
	script := strings.Join([]string{
		"myapp",
		"ghcr.io/example/app:latest",
		"ghcr.io/example/app@sha256:" + digest,
		"small",
		"2",
		"",
	}, "\n") + "\n"

	var out bytes.Buffer
	rw := struct {
		io.Reader
		io.Writer
	}{Reader: strings.NewReader(script), Writer: &out}

	gateway.RunDeploy(ctx, rw, hub, "SHA256:alice", "alice", "")
	if !strings.Contains(out.String(), "digest-pinned") {
		t.Fatalf("expected digest error; got %q", out.String())
	}
	app, err := st.GetApp(ctx, "alice", "myapp")
	if err != nil || app == nil {
		t.Fatal("expected app after retry")
	}
	if app.Tier != "small" || app.SessionStrategy != store.StrategyKick {
		t.Fatalf("app = %+v", app)
	}
}

func TestRunDeployUpdateConfirm(t *testing.T) {
	ctx := context.Background()
	st := store.NewMemory()
	if err := st.CreateUser(ctx, "alice", "SHA256:alice"); err != nil {
		t.Fatal(err)
	}
	digest1 := "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
	digest2 := "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
	if err := st.UpsertApp(ctx, store.App{
		Owner: "alice", Name: "myapp",
		Image: "ghcr.io/example/app@sha256:" + digest1,
		Tier:  "tiny",
	}); err != nil {
		t.Fatal(err)
	}
	hub := &gateway.Hub{Store: st, Sessions: session.NewRegistry()}

	script := strings.Join([]string{
		"myapp",
		"y",
		"ghcr.io/example/app@sha256:" + digest2,
		"tiny",
		"1",
		"",
	}, "\n") + "\n"

	var out bytes.Buffer
	rw := struct {
		io.Reader
		io.Writer
	}{Reader: strings.NewReader(script), Writer: &out}

	gateway.RunDeploy(ctx, rw, hub, "SHA256:alice", "alice", "")
	if !strings.Contains(out.String(), "Updated myapp") {
		t.Fatalf("output: %q", out.String())
	}
	app, _ := st.GetApp(ctx, "alice", "myapp")
	if app == nil || !strings.Contains(app.Image, digest2) {
		t.Fatalf("app = %+v", app)
	}
}

type nopInst struct{}

func (nopInst) Ensure(context.Context, string, string, string, string, string, bool) error {
	return nil
}
func (nopInst) Stop(context.Context, string, string, string) error { return nil }
func (nopInst) SetNoIdle(context.Context, string, string, string, bool) error {
	return nil
}

func TestRunDeployCutoverSetsGen(t *testing.T) {
	ctx := context.Background()
	st := store.NewMemory()
	if err := st.CreateUser(ctx, "alice", "SHA256:alice"); err != nil {
		t.Fatal(err)
	}
	sess := session.NewRegistry()
	ctrl := cutover.New(st, sess, nopInst{})
	hub := &gateway.Hub{Store: st, Sessions: sess, Cutover: ctrl}

	digest := "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
	script := strings.Join([]string{
		"myapp",
		"ghcr.io/example/app@sha256:" + digest,
		"",
		"2",
		"",
	}, "\n") + "\n"

	var out bytes.Buffer
	rw := struct {
		io.Reader
		io.Writer
	}{Reader: strings.NewReader(script), Writer: &out}

	gateway.RunDeploy(ctx, rw, hub, "SHA256:alice", "alice", "")
	if !strings.Contains(out.String(), "generation:") {
		t.Fatalf("output: %q", out.String())
	}
	app, err := st.GetApp(ctx, "alice", "myapp")
	if err != nil || app == nil || app.ActiveGen == "" {
		t.Fatalf("app %+v err=%v", app, err)
	}
	if app.Image != "ghcr.io/example/app@sha256:"+digest {
		t.Fatalf("image %q", app.Image)
	}

	r, err := hub.HandleConnect(ctx, gateway.Connect{SSHUser: "myapp", KeyFingerprint: "SHA256:alice"})
	if err != nil || r.Action != gateway.ActionProxyApp || r.Gen != app.ActiveGen {
		t.Fatalf("connect: %+v %v", r, err)
	}
	hub.ReleaseSession(r.Session)
}

type failInst struct{}

func (failInst) Ensure(context.Context, string, string, string, string, string, bool) error {
	return errors.New("boot failed")
}
func (failInst) Stop(context.Context, string, string, string) error { return nil }
func (failInst) SetNoIdle(context.Context, string, string, string, bool) error {
	return nil
}

func TestFailedInitialDeployLeavesNoPhantomApp(t *testing.T) {
	ctx := context.Background()
	st := store.NewMemory()
	if err := st.CreateUser(ctx, "alice", "SHA256:alice"); err != nil {
		t.Fatal(err)
	}
	sess := session.NewRegistry()
	hub := &gateway.Hub{Store: st, Sessions: sess, Cutover: cutover.New(st, sess, failInst{})}
	digest := strings.Repeat("d", 64)
	var out bytes.Buffer
	rw := struct {
		io.Reader
		io.Writer
	}{Reader: strings.NewReader(""), Writer: &out}

	code := gateway.RunDeploy(ctx, rw, hub, "SHA256:alice", "alice",
		"myapp --image=ghcr.io/example/app@sha256:"+digest+" --tier=tiny --strategy=kick --yes")
	if code == 0 || !strings.Contains(out.String(), "boot failed") {
		t.Fatalf("code=%d output=%q", code, out.String())
	}
	app, err := st.GetApp(ctx, "alice", "myapp")
	if err != nil || app != nil {
		t.Fatalf("failed deploy persisted app: %+v, %v", app, err)
	}
}
