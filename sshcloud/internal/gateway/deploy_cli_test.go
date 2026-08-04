package gateway_test

import (
	"bytes"
	"context"
	"io"
	"strings"
	"testing"

	"github.com/imjasonh/playground/sshcloud/internal/cutover"
	"github.com/imjasonh/playground/sshcloud/internal/gateway"
	"github.com/imjasonh/playground/sshcloud/internal/session"
	"github.com/imjasonh/playground/sshcloud/internal/store"
)

func TestRunDeployExecArgs(t *testing.T) {
	ctx := context.Background()
	st := store.NewMemory()
	if err := st.CreateUser(ctx, "demo", "SHA256:demo"); err != nil {
		t.Fatal(err)
	}
	sess := session.NewRegistry()
	var ensured string
	hub := &gateway.Hub{
		Store:    st,
		Sessions: sess,
		Cutover: cutover.New(st, sess, &cliInst{onEnsure: func(_, _, _, image string, _ bool) {
			ensured = image
		}}),
	}
	digest := "abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789"
	img := "ghcr.io/example/fortune@sha256:" + digest
	var out bytes.Buffer
	rw := struct {
		io.Reader
		io.Writer
	}{Reader: strings.NewReader(""), Writer: &out}

	code := gateway.RunDeploy(ctx, rw, hub, "demo",
		"fortune --image="+img+" --tier=tiny --strategy=kick --yes")
	if code != 0 {
		t.Fatalf("exit %d out=%q", code, out.String())
	}
	if !strings.Contains(out.String(), "Created fortune") && !strings.Contains(out.String(), "Deployed fortune") && !strings.Contains(out.String(), "✓") {
		t.Fatalf("output %q", out.String())
	}
	if ensured != img {
		t.Fatalf("ensure image %q", ensured)
	}
	app, err := st.GetApp(ctx, "demo", "fortune")
	if err != nil || app == nil || app.Image != img || app.ActiveGen == "" {
		t.Fatalf("app %+v %v", app, err)
	}

	// Update without --yes fails.
	out.Reset()
	code = gateway.RunDeploy(ctx, rw, hub, "demo", "fortune --image="+img+" --strategy=kick")
	if code == 0 || !strings.Contains(out.String(), "--yes") {
		t.Fatalf("expected --yes required, code=%d out=%q", code, out.String())
	}

	out.Reset()
	code = gateway.RunDeploy(ctx, rw, hub, "demo", "fortune --image="+img+" --strategy=kick --yes")
	if code != 0 || !strings.Contains(out.String(), "Updated fortune") {
		t.Fatalf("update: code=%d out=%q", code, out.String())
	}
}

type cliInst struct {
	onEnsure func(user, app, gen, image string, noIdle bool)
}

func (c *cliInst) Ensure(_ context.Context, user, app, gen, image, _ string, noIdle bool) error {
	if c.onEnsure != nil {
		c.onEnsure(user, app, gen, image, noIdle)
	}
	return nil
}
func (c *cliInst) Stop(context.Context, string, string, string) error { return nil }
func (c *cliInst) SetNoIdle(context.Context, string, string, string, bool) error {
	return nil
}
