package e2e_test

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"os/exec"
	"slices"
	"strings"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
	"github.com/imjasonh/playground/kube/internal/image/imagetest"
)

// TestGenerateVolume installs the eventlog example, which declares a
// kube.Volume, and runs the image's program with the generated RBAC rules
// and a directory in place of the volume. There's no kubelet, so the claim
// stays unbound; the kind test mounts it.
func TestGenerateVolume(t *testing.T) {
	c := e2e.Client(t)
	reg := imagetest.Registry(t)
	imagetest.Base(t, reg+"/chainguard/static:latest", "linux/amd64")

	cmd := exec.CommandContext(t.Context(), "go", "run", "github.com/imjasonh/playground/kube/examples/eventlog", "generate",
		"-registry="+reg+"/e2e", "-platform=linux/amd64", "-replicas=2")
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	if err := cmd.Run(); err == nil || !strings.Contains(stderr.String(), "keeps state in a volume at /var/lib/eventlog, which one replica writes") {
		t.Errorf("generate -replicas=2: %v\n%s", err, stderr.String())
	}

	in := generateExample(t, reg, "examples/eventlog", "eventlog", "-volume-size=2Gi")
	byKind := map[string]string{}
	for _, obj := range in.objects {
		b, _ := json.Marshal(obj)
		byKind[obj["kind"].(string)] = string(b)
	}
	for kind, want := range map[string]string{
		"PersistentVolumeClaim": `"spec":{"accessModes":["ReadWriteOnce"],"resources":{"requests":{"storage":"2Gi"}}}`,
		"Deployment":            `"strategy":{"type":"Recreate"}`,
		"ClusterRole":           `{"apiGroups":[""],"resources":["events"],"verbs":["get","list","watch"]}`,
	} {
		if !strings.Contains(byKind[kind], want) {
			t.Errorf("%s = %s, want %s", kind, byKind[kind], want)
		}
	}
	if !strings.Contains(byKind["Deployment"], `"replicas":1`) || byKind["PodDisruptionBudget"] != "" || slices.Contains(in.args, "-leader-elect") {
		t.Errorf("the program doesn't run one replica without leader election: args %q, Deployment %s, PodDisruptionBudget %s", in.args, byKind["Deployment"], byKind["PodDisruptionBudget"])
	}
	// The program serves, but no other Pod takes its connections while it
	// stops, so it doesn't wait before it stops.
	if strings.Contains(byKind["Deployment"], "preStop") {
		t.Errorf("the Deployment has a preStop hook: %s", byKind["Deployment"])
	}
	in.apply(t, c)
	in.args = append(in.args, "-dir="+t.TempDir())
	in.serveAddr = freeAddr(t)
	out := in.runInstalled(t, in.executable(t, "eventlog"), serviceAccountKubeconfig(t, c, "eventlog", "eventlog"))

	ns := e2e.Namespace(t, c)
	if err := c.Create(t.Context(), client.Path("v1", "serviceaccounts", ns, ""), map[string]any{
		"apiVersion": "v1", "kind": "ServiceAccount", "metadata": map[string]any{"name": "ci"},
	}, nil); err != nil {
		t.Fatal(err)
	}
	var tr struct {
		Status struct {
			Token string `json:"token"`
		} `json:"status"`
	}
	if err := c.Create(t.Context(), client.Path("v1", "serviceaccounts", ns, "ci", "token"), map[string]any{
		"apiVersion": "authentication.k8s.io/v1", "kind": "TokenRequest", "spec": map[string]any{"audiences": []string{"eventlog"}},
	}, &tr); err != nil {
		t.Fatal(err)
	}
	event := client.Path("v1", "events", ns, "hello")
	if err := c.Create(t.Context(), client.Path("v1", "events", ns, ""), map[string]any{
		"apiVersion": "v1", "kind": "Event", "metadata": map[string]any{"name": "hello"},
		"involvedObject": map[string]any{"kind": "Pod", "name": "web-1", "namespace": ns},
		"reason":         "Hello", "message": "written by the test", "type": "Normal",
	}, nil); err != nil {
		t.Fatal(err)
	}
	served := func() error {
		req, err := http.NewRequestWithContext(t.Context(), http.MethodGet, "http://"+in.serveAddr+"/events/"+ns, nil)
		if err != nil {
			return err
		}
		req.Header.Set("Authorization", "Bearer "+tr.Status.Token)
		resp, err := http.DefaultClient.Do(req)
		if err != nil {
			return err
		}
		defer resp.Body.Close()
		b, _ := io.ReadAll(resp.Body)
		if resp.StatusCode != http.StatusOK || !strings.Contains(string(b), `"name":"hello"`) || !strings.Contains(string(b), `"reason":"Hello"`) {
			return fmt.Errorf("GET /events/%s = %s %s", ns, resp.Status, b)
		}
		return nil
	}
	e2e.Eventually(t, 30*time.Second, served)
	if err := c.Delete(t.Context(), event, client.DeleteOptions{}); err != nil {
		t.Fatal(err)
	}
	e2e.Never(t, 2*time.Second, served)
	noPermissionErrors(t, out)
}
