package gateway_test

import (
	"bytes"
	"context"
	"io"
	"log"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/google/go-containerregistry/pkg/registry"

	"github.com/imjasonh/playground/sshcloud/internal/apppack"
	"github.com/imjasonh/playground/sshcloud/internal/cutover"
	"github.com/imjasonh/playground/sshcloud/internal/gateway"
	"github.com/imjasonh/playground/sshcloud/internal/ocirootfs"
	"github.com/imjasonh/playground/sshcloud/internal/session"
	"github.com/imjasonh/playground/sshcloud/internal/store"
)

// TestDeployFortuneE2E exercises the normal deploy path with the fortune sample
// app: build OCI image → RunDeploy → cutover Ensure(image) → materialize rootfs.
func TestDeployFortuneE2E(t *testing.T) {
	if _, err := exec.LookPath("mkfs.ext4"); err != nil {
		t.Skip("mkfs.ext4 not available")
	}

	bin := filepath.Join(t.TempDir(), "fortune")
	cmd := exec.Command("go", "build", "-o", bin, "github.com/imjasonh/playground/sshcloud/cmd/fortune")
	cmd.Env = append(os.Environ(), "CGO_ENABLED=0", "GOOS=linux", "GOARCH=amd64")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("build fortune: %v\n%s", err, out)
	}
	img, err := apppack.Build(apppack.Spec{
		Binary:    bin,
		GuestPath: "/fortune",
		// Defaults on the binary cover listen/ca; keep cmd empty to match ko image.
	})
	if err != nil {
		t.Fatal(err)
	}
	srv := httptest.NewServer(registry.New(registry.Logger(log.New(io.Discard, "", 0))))
	t.Cleanup(srv.Close)
	host := strings.TrimPrefix(srv.URL, "http://")
	ref, err := apppack.Push(img, host+"/sshcloud/fortune:e2e")
	if err != nil {
		t.Fatal(err)
	}

	ctx := context.Background()
	st := store.NewMemory()
	if err := st.CreateUser(ctx, "alice", "SHA256:alice"); err != nil {
		t.Fatal(err)
	}
	sess := session.NewRegistry()
	var ensuredImage string
	fi := &recordingInstances{onEnsure: func(_, _, _, image string, _ bool) {
		ensuredImage = image
	}}
	hub := &gateway.Hub{
		Store:    st,
		Sessions: sess,
		Cutover:  cutover.New(st, sess, fi),
	}

	script := strings.Join([]string{
		"fortune",
		ref,
		"",  // tiny
		"2", // kick (simpler for e2e; no drain timer)
		"",  // enter
	}, "\n") + "\n"
	var out bytes.Buffer
	rw := struct {
		io.Reader
		io.Writer
	}{Reader: strings.NewReader(script), Writer: &out}

	gateway.RunDeploy(ctx, rw, hub, "SHA256:alice", "alice", "")

	got := out.String()
	if !strings.Contains(got, "Created fortune") {
		t.Fatalf("deploy output: %q", got)
	}
	if ensuredImage != ref {
		t.Fatalf("cutover Ensure image=%q want %q", ensuredImage, ref)
	}
	app, err := st.GetApp(ctx, "alice", "fortune")
	if err != nil || app == nil || app.Image != ref || app.ActiveGen == "" {
		t.Fatalf("app after deploy: %+v %v", app, err)
	}

	// Deep link works only after deploy.
	r, err := hub.HandleConnect(ctx, gateway.Connect{SSHUser: "fortune", KeyFingerprint: "SHA256:alice"})
	if err != nil || r.Action != gateway.ActionProxyApp || r.App != "fortune" || r.Gen != app.ActiveGen {
		t.Fatalf("connect: %+v %v", r, err)
	}
	hub.ReleaseSession(r.Session)

	// Same digest materializes to a bootable rootfs (agent path).
	res, err := ocirootfs.Materialize(ctx, ref, ocirootfs.Options{CacheDir: t.TempDir(), SizeMB: 64})
	if err != nil {
		t.Fatal(err)
	}
	if err := res.Spec.Validate(); err != nil {
		t.Fatal(err)
	}
	if res.Spec.Entrypoint[0] != "/fortune" {
		t.Fatalf("entrypoint %+v", res.Spec.Entrypoint)
	}
}

type recordingInstances struct {
	onEnsure func(user, app, gen, image string, noIdle bool)
}

func (r *recordingInstances) Ensure(_ context.Context, user, app, gen, image, _ string, noIdle bool) error {
	if r.onEnsure != nil {
		r.onEnsure(user, app, gen, image, noIdle)
	}
	return nil
}

func (r *recordingInstances) Stop(context.Context, string, string, string) error { return nil }
func (r *recordingInstances) SetNoIdle(context.Context, string, string, string, bool) error {
	return nil
}
