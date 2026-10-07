package e2e_test

import (
	"archive/tar"
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strings"
	"sync"
	"syscall"
	"testing"
	"time"

	"github.com/google/go-containerregistry/pkg/name"
	"github.com/google/go-containerregistry/pkg/v1/remote"

	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
	"github.com/imjasonh/playground/kube/internal/image/imagetest"
	"github.com/imjasonh/playground/kube/internal/yaml"
)

// installation is what an example's generate command wrote.
type installation struct {
	objects []map[string]any
	// image and args are the Deployment's container image and arguments.
	image string
	args  []string
	// namespace and serviceAccount are the Deployment's.
	namespace, serviceAccount string
	// tokens are the service account tokens in the Deployment's projected
	// volume.
	tokens []projectedToken
	// serveAddr is where runInstalled's program serves its kube.Serve
	// handler.
	serveAddr string
}

type projectedToken struct {
	Audience string `json:"audience"`
	Path     string `json:"path"`
}

// generateExample runs the generate command of a program in the kube
// module, such as examples/website, and returns what it wrote.
func generateExample(t *testing.T, reg, program, namespace string, extra ...string) installation {
	t.Helper()
	args := append([]string{
		"run", "github.com/imjasonh/playground/kube/" + program, "generate",
		"-registry=" + reg + "/e2e", "-base=" + reg + "/chainguard/static:latest",
		"-platform=linux/amd64", "-namespace=" + namespace,
	}, extra...)
	cmd := exec.CommandContext(t.Context(), "go", args...)
	var stdout, stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = &stdout, &stderr
	if err := cmd.Run(); err != nil {
		t.Fatalf("generate: %v\n%s", err, stderr.String())
	}
	t.Logf("generate wrote to stderr:\n%s", stderr.String())
	var in installation
	for _, doc := range strings.Split(stdout.String(), "\n---\n") {
		v, err := yaml.Parse([]byte(doc))
		if err != nil {
			t.Fatalf("parsing %q: %v", doc, err)
		}
		obj := v.(map[string]any)
		in.objects = append(in.objects, obj)
		if obj["kind"] == "Deployment" {
			var d struct {
				Metadata struct {
					Namespace string `json:"namespace"`
				} `json:"metadata"`
				Spec struct {
					Template struct {
						Spec struct {
							ServiceAccountName string `json:"serviceAccountName"`
							Containers         []struct {
								Image string   `json:"image"`
								Args  []string `json:"args"`
							} `json:"containers"`
							Volumes []struct {
								Projected struct {
									Sources []struct {
										ServiceAccountToken *projectedToken `json:"serviceAccountToken"`
									} `json:"sources"`
								} `json:"projected"`
							} `json:"volumes"`
						} `json:"spec"`
					} `json:"template"`
				} `json:"spec"`
			}
			b, _ := json.Marshal(obj)
			_ = json.Unmarshal(b, &d)
			c := d.Spec.Template.Spec.Containers[0]
			in.image, in.args = c.Image, c.Args
			in.namespace, in.serviceAccount = d.Metadata.Namespace, d.Spec.Template.Spec.ServiceAccountName
			for _, v := range d.Spec.Template.Spec.Volumes {
				for _, s := range v.Projected.Sources {
					if s.ServiceAccountToken != nil {
						in.tokens = append(in.tokens, *s.ServiceAccountToken)
					}
				}
			}
		}
	}
	if in.image == "" {
		t.Fatalf("no Deployment in:\n%s", stdout.String())
	}
	return in
}

// apply applies the installation's objects as an administrator would with
// kubectl apply.
func (in installation) apply(t *testing.T, c *client.Client) {
	t.Helper()
	for _, obj := range in.objects {
		meta := obj["metadata"].(map[string]any)
		ns, _ := meta["namespace"].(string)
		path := client.Path(obj["apiVersion"].(string), strings.ToLower(obj["kind"].(string))+"s", ns, meta["name"].(string))
		if err := c.Apply(t.Context(), path, "kubectl", true, obj, nil); err != nil {
			t.Fatalf("applying %s %s: %v", obj["kind"], meta["name"], err)
		}
	}
}

// executable writes the program in the installation's image, for this
// test's platform, to a file.
func (in installation) executable(t *testing.T, program string) string {
	t.Helper()
	ref, err := name.ParseReference(in.image)
	if err != nil {
		t.Fatal(err)
	}
	idx, err := remote.Index(ref, remote.WithContext(t.Context()))
	if err != nil {
		t.Fatal(err)
	}
	man, err := idx.IndexManifest()
	if err != nil {
		t.Fatal(err)
	}
	img, err := idx.Image(man.Manifests[0].Digest)
	if err != nil {
		t.Fatal(err)
	}
	layers, err := img.Layers()
	if err != nil {
		t.Fatal(err)
	}
	rc, err := layers[len(layers)-1].Uncompressed()
	if err != nil {
		t.Fatal(err)
	}
	defer rc.Close()
	tr := tar.NewReader(rc)
	for {
		h, err := tr.Next()
		if err != nil {
			t.Fatalf("no app/%s in the image's last layer: %v", program, err)
		}
		if h.Name != "app/"+program {
			continue
		}
		exe := filepath.Join(t.TempDir(), program)
		b, _ := io.ReadAll(tr)
		if err := os.WriteFile(exe, b, 0o700); err != nil { // #nosec G306 -- an executable the test runs.
			t.Fatal(err)
		}
		return exe
	}
}

// serviceAccountToken returns a token from the API server for a service
// account, for audiences, or for the API server when there are none.
func serviceAccountToken(t *testing.T, c *client.Client, namespace, name string, audiences ...string) string {
	t.Helper()
	var tr struct {
		Status struct {
			Token string `json:"token"`
		} `json:"status"`
	}
	spec := map[string]any{}
	if len(audiences) > 0 {
		spec["audiences"] = audiences
	}
	if err := c.Create(t.Context(), client.Path("v1", "serviceaccounts", namespace, name, "token"), map[string]any{
		"apiVersion": "authentication.k8s.io/v1", "kind": "TokenRequest", "spec": spec,
	}, &tr); err != nil {
		t.Fatal(err)
	}
	return tr.Status.Token
}

// serviceAccountKubeconfig writes a kubeconfig that authenticates as a
// service account, with a token from the API server.
func serviceAccountKubeconfig(t *testing.T, c *client.Client, namespace, name string) string {
	t.Helper()
	token := serviceAccountToken(t, c, namespace, name)
	admin, err := os.ReadFile(e2e.Env(t).Kubeconfig)
	if err != nil {
		t.Fatal(err)
	}
	var kc struct {
		Clusters []struct {
			Cluster map[string]any `json:"cluster"`
		} `json:"clusters"`
	}
	if err := yaml.Unmarshal(admin, &kc); err != nil {
		t.Fatal(err)
	}
	cluster := kc.Clusters[0].Cluster
	path := filepath.Join(t.TempDir(), "kubeconfig")
	body := fmt.Sprintf(`apiVersion: v1
kind: Config
current-context: sa
clusters:
- name: e2e
  cluster:
    server: %s
    certificate-authority-data: %s
contexts:
- name: sa
  context:
    cluster: e2e
    user: sa
    namespace: %s
users:
- name: sa
  user:
    token: %s
`, cluster["server"], cluster["certificate-authority-data"], namespace, token)
	if err := os.WriteFile(path, []byte(body), 0o600); err != nil {
		t.Fatal(err)
	}
	return path
}

type syncBuffer struct {
	mu sync.Mutex
	b  bytes.Buffer
}

func (s *syncBuffer) Write(p []byte) (int, error) {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.b.Write(p)
}

func (s *syncBuffer) String() string {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.b.String()
}

// mountTokens writes the tokens of the Deployment's projected volume to a
// directory, as the kubelet does, with tokens from the API server for the
// Deployment's service account. Unlike the kubelet's, they aren't bound to
// a Pod.
func (in installation) mountTokens(t *testing.T) string {
	t.Helper()
	dir := t.TempDir()
	c := e2e.Client(t)
	for _, tok := range in.tokens {
		token := serviceAccountToken(t, c, in.namespace, in.serviceAccount, tok.Audience)
		if err := os.WriteFile(filepath.Join(dir, tok.Path), []byte(token), 0o600); err != nil {
			t.Fatal(err)
		}
	}
	return dir
}

// runInstalled runs the installation's program the way its Deployment
// does, with its service account's permissions, except that it listens on
// the loopback interface and gives the API server a URL for its webhooks
// instead of a Service. It returns the program's output.
func (in installation) runInstalled(t *testing.T, exe, kubeconfig string) *syncBuffer {
	t.Helper()
	httpAddr, hookAddr := freeAddr(t), freeAddr(t)
	args := []string{"-kubeconfig=" + kubeconfig}
	for _, a := range in.args {
		switch {
		case strings.HasPrefix(a, "-addr="):
			a = "-addr=" + httpAddr
		case strings.HasPrefix(a, "-webhook-addr="):
			a = "-webhook-addr=" + hookAddr
		case strings.HasPrefix(a, "-webhook-service="):
			a = "-webhook-url=https://" + hookAddr
		case strings.HasPrefix(a, "-serve-addr="):
			a = "-serve-addr=" + in.serveAddr
		case strings.HasPrefix(a, "-token-dir="):
			a = "-token-dir=" + in.mountTokens(t)
		}
		args = append(args, a)
	}
	cmd := exec.Command(exe, args...) // #nosec G204 -- the program the test built.
	out := &syncBuffer{}
	cmd.Stdout, cmd.Stderr = out, out
	if err := cmd.Start(); err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() {
		_ = cmd.Process.Signal(syscall.SIGTERM)
		done := make(chan error, 1)
		go func() { done <- cmd.Wait() }()
		select {
		case <-done:
		case <-time.After(30 * time.Second):
			_ = cmd.Process.Kill()
			t.Error("the program didn't stop within 30s")
		}
		t.Logf("program output:\n%s", out.String())
	})
	e2e.Eventually(t, time.Minute, func() error {
		resp, err := http.Get("http://" + httpAddr + "/readyz")
		if err != nil {
			return err
		}
		resp.Body.Close()
		if resp.StatusCode != http.StatusOK {
			return fmt.Errorf("/readyz returned %s; output:\n%s", resp.Status, out.String())
		}
		return nil
	})
	return out
}

func noPermissionErrors(t *testing.T, out *syncBuffer) {
	t.Helper()
	// The client reports a denial as "... is forbidden: ... (403 Forbidden)".
	// A bare "403" could be part of a port or a timestamp.
	if s := out.String(); strings.Contains(strings.ToLower(s), "forbidden") {
		t.Errorf("the program was denied something:\n%s", s)
	}
}

// eventFrom waits for an Event in namespace from controller. The program
// writes events in the background, so a denial can come after its other
// writes succeed.
func eventFrom(t *testing.T, c *client.Client, namespace, controller string) {
	t.Helper()
	e2e.Eventually(t, 30*time.Second, func() error {
		var events struct {
			Items []struct {
				ReportingController string `json:"reportingController"`
			} `json:"items"`
		}
		if err := c.Get(t.Context(), client.Path("events.k8s.io/v1", "events", namespace, ""), &events); err != nil {
			return err
		}
		for _, e := range events.Items {
			if e.ReportingController == controller {
				return nil
			}
		}
		return fmt.Errorf("no Events from %s in %s", controller, namespace)
	})
}

// TestGenerateWebsite installs the website example from what its generate
// command wrote, and runs the image's program with the generated RBAC
// rules: the API server enforces them, so a missing rule fails the test.
func TestGenerateWebsite(t *testing.T) {
	c := e2e.Client(t)
	reg := imagetest.Registry(t)
	imagetest.Base(t, reg+"/chainguard/static:latest", "linux/amd64")
	in := generateExample(t, reg, "examples/website", "website-system")
	if !slices.Contains(in.args, "-leader-elect") {
		t.Errorf("args = %q, want -leader-elect for two replicas", in.args)
	}
	in.apply(t, c)
	exe := in.executable(t, "website")
	out := in.runInstalled(t, exe, serviceAccountKubeconfig(t, c, "website-system", "website"))

	ns := e2e.Namespace(t, c)
	if err := c.Create(t.Context(), client.Path("examples.kube.imjasonh.github.io/v1", "websites", ns, ""), map[string]any{
		"apiVersion": "examples.kube.imjasonh.github.io/v1", "kind": "Website",
		"metadata": map[string]any{"name": "blog"}, "spec": map[string]any{"image": reg + "/chainguard/static:latest", "port": 8080},
	}, nil); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 30*time.Second, func() error {
		for _, p := range []string{client.Path("apps/v1", "deployments", ns, "blog"), client.Path("v1", "services", ns, "blog")} {
			if err := c.Get(t.Context(), p, &map[string]any{}); err != nil {
				return err
			}
		}
		var site struct {
			Status struct {
				ObservedGeneration int64  `json:"observedGeneration"`
				URL                string `json:"url"`
			} `json:"status"`
		}
		if err := c.Get(t.Context(), client.Path("examples.kube.imjasonh.github.io/v1", "websites", ns, "blog"), &site); err != nil {
			return err
		}
		if site.Status.ObservedGeneration != 1 || site.Status.URL == "" {
			return fmt.Errorf("status = %+v", site.Status)
		}
		return nil
	})
	var leases struct {
		Items []any `json:"items"`
	}
	if err := c.Get(t.Context(), client.Path("coordination.k8s.io/v1", "leases", "website-system", ""), &leases); err != nil || len(leases.Items) == 0 {
		t.Errorf("leases in website-system: %d, %v", len(leases.Items), err)
	}
	eventFrom(t, c, ns, "website")
	noPermissionErrors(t, out)
}

// TestGenerateOneNamespace installs the website example to watch one
// namespace. The rules for namespaced resources are in a Role there, and
// the API server enforces them, so the program reconciles Websites in that
// namespace with no rules for any other.
func TestGenerateOneNamespace(t *testing.T) {
	c := e2e.Client(t)
	reg := imagetest.Registry(t)
	imagetest.Base(t, reg+"/chainguard/static:latest", "linux/amd64")
	watched, other := e2e.Namespace(t, c), e2e.Namespace(t, c)
	in := generateExample(t, reg, "examples/website", "website-one", "-replicas=1", "-watch-namespace="+watched)
	if !slices.Contains(in.args, "-namespace="+watched) {
		t.Errorf("args = %q, want -namespace=%s", in.args, watched)
	}
	for _, obj := range in.objects {
		b, _ := json.Marshal(obj)
		if obj["kind"] == "ClusterRole" && strings.Contains(string(b), `"deployments"`) {
			t.Errorf("the ClusterRole has rules for Deployments, which are namespaced: %s", b)
		}
	}
	in.apply(t, c)
	exe := in.executable(t, "website")
	out := in.runInstalled(t, exe, serviceAccountKubeconfig(t, c, "website-one", "website"))

	for _, ns := range []string{watched, other} {
		if err := c.Create(t.Context(), client.Path("examples.kube.imjasonh.github.io/v1", "websites", ns, ""), map[string]any{
			"apiVersion": "examples.kube.imjasonh.github.io/v1", "kind": "Website",
			"metadata": map[string]any{"name": "blog"}, "spec": map[string]any{"image": reg + "/chainguard/static:latest", "port": 8080},
		}, nil); err != nil {
			t.Fatal(err)
		}
	}
	e2e.Eventually(t, 30*time.Second, func() error {
		for _, p := range []string{client.Path("apps/v1", "deployments", watched, "blog"), client.Path("v1", "services", watched, "blog")} {
			if err := c.Get(t.Context(), p, &map[string]any{}); err != nil {
				return err
			}
		}
		return nil
	})
	if err := e2e.Get(t.Context(), c, client.Path("apps/v1", "deployments", other, "blog"), &map[string]any{}); err == nil {
		t.Errorf("the program reconciled a Website in %s, which it doesn't watch", other)
	}
	eventFrom(t, c, watched, "website")
	noPermissionErrors(t, out)
}

// TestGenerateOwnedType installs the imagereport example, which owns
// ImageReports without reconciling them. Its rules let it create the missing
// CRD and get that CRD, but not change it.
func TestGenerateOwnedType(t *testing.T) {
	c := e2e.Client(t)
	reg := imagetest.Registry(t)
	imagetest.Base(t, reg+"/chainguard/static:latest", "linux/amd64")
	in := generateExample(t, reg, "examples/imagereport", "imagereport", "-replicas=1")
	const crd = "imagereports.examples.kube.imjasonh.github.io"
	var crdRules []any
	for _, obj := range in.objects {
		if obj["kind"] != "ClusterRole" {
			continue
		}
		for _, r := range obj["rules"].([]any) {
			if b, _ := json.Marshal(r); strings.Contains(string(b), `"customresourcedefinitions"`) {
				crdRules = append(crdRules, r)
			}
		}
	}
	want := `[{"apiGroups":["apiextensions.k8s.io"],"resources":["customresourcedefinitions"],"verbs":["create"]},` +
		`{"apiGroups":["apiextensions.k8s.io"],"resourceNames":["` + crd + `"],"resources":["customresourcedefinitions"],"verbs":["get"]}]`
	if b, _ := json.Marshal(crdRules); string(b) != want {
		t.Errorf("rules for CRDs =\n%s\nwant\n%s", b, want)
	}
	in.apply(t, c)
	exe := in.executable(t, "imagereport")
	out := in.runInstalled(t, exe, serviceAccountKubeconfig(t, c, "imagereport", "imagereport"))

	ns := e2e.Namespace(t, c)
	if err := c.Create(t.Context(), client.Path("v1", "pods", ns, ""), map[string]any{
		"apiVersion": "v1", "kind": "Pod", "metadata": map[string]any{"name": "app"},
		"spec": map[string]any{"containers": []any{map[string]any{"name": "app", "image": "ghcr.io/example/app:v1"}}},
	}, nil); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 30*time.Second, func() error {
		var report struct {
			Images []struct {
				Image string `json:"image"`
			} `json:"images"`
		}
		if err := e2e.Get(t.Context(), c, client.Path("examples.kube.imjasonh.github.io/v1", "imagereports", ns, "images"), &report); err != nil {
			return err
		}
		if len(report.Images) != 1 || report.Images[0].Image != "ghcr.io/example/app:v1" {
			return fmt.Errorf("report images = %+v", report.Images)
		}
		return nil
	})
	var meta crdMeta
	if err := e2e.Get(t.Context(), c, "/apis/apiextensions.k8s.io/v1/customresourcedefinitions/"+crd, &meta); err != nil {
		t.Fatal(err)
	}
	if meta.managedBy() != "imagereport" {
		t.Errorf("the CRD is managed by %q, want imagereport", meta.managedBy())
	}
	noPermissionErrors(t, out)
}

// TestGenerateWebhooks installs the podpolicy example, whose admission
// webhooks need a Service, a certificate Secret, and webhook
// configurations, and passes it a flag after --.
func TestGenerateWebhooks(t *testing.T) {
	c := e2e.Client(t)
	reg := imagetest.Registry(t)
	imagetest.Base(t, reg+"/chainguard/static:latest", "linux/amd64")
	in := generateExample(t, reg, "examples/podpolicy", "podpolicy", "--", "-registries=ghcr.io/example/")
	kinds := map[string]bool{}
	for _, obj := range in.objects {
		kinds[obj["kind"].(string)] = true
		if b, _ := json.Marshal(obj); strings.Contains(string(b), `"events.k8s.io"`) {
			t.Errorf("podpolicy records no events, but its %s has a rule for them: %s", obj["kind"], b)
		}
	}
	if !kinds["Service"] || !kinds["Role"] || slices.Contains(in.args, "-leader-elect") || !slices.Contains(in.args, "-registries=ghcr.io/example/") {
		t.Errorf("kinds = %v, args = %q", kinds, in.args)
	}
	t.Cleanup(func() {
		// The program registered webhooks that fail every Pod request once
		// it stops. Cleanups run in reverse order, so it has stopped.
		ctx := context.WithoutCancel(t.Context())
		for _, r := range []string{"validatingwebhookconfigurations", "mutatingwebhookconfigurations"} {
			_ = c.Delete(ctx, client.Path("admissionregistration.k8s.io/v1", r, "", "podpolicy"), client.DeleteOptions{})
		}
	})
	in.apply(t, c)
	exe := in.executable(t, "podpolicy")
	out := in.runInstalled(t, exe, serviceAccountKubeconfig(t, c, "podpolicy", "podpolicy"))

	ns := e2e.Namespace(t, c)
	pod := func(name, img string) map[string]any {
		return map[string]any{
			"apiVersion": "v1", "kind": "Pod", "metadata": map[string]any{"name": name},
			"spec": map[string]any{"containers": []any{map[string]any{"name": "app", "image": img}}},
		}
	}
	err := c.Create(t.Context(), client.Path("v1", "pods", ns, ""), pod("denied", "docker.io/library/nginx"), nil)
	if err == nil || !strings.Contains(err.Error(), "isn't from an allowed registry") {
		t.Errorf("creating a Pod from another registry: %v", err)
	}
	var created struct {
		Spec struct {
			Containers []struct {
				Resources struct {
					Requests map[string]string `json:"requests"`
				} `json:"resources"`
			} `json:"containers"`
		} `json:"spec"`
	}
	if err := c.Create(t.Context(), client.Path("v1", "pods", ns, ""), pod("allowed", "ghcr.io/example/app:v1"), &created); err != nil {
		t.Fatal(err)
	}
	if got := created.Spec.Containers[0].Resources.Requests; got["cpu"] != "100m" {
		t.Errorf("requests = %v, want the default cpu", got)
	}
	noPermissionErrors(t, out)
}
