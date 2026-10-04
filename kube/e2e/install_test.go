package e2e_test

import (
	"context"
	"encoding/json"
	"fmt"
	"strings"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
	"github.com/imjasonh/playground/kube/internal/image/imagetest"
)

type installedConfigMap struct {
	Metadata struct {
		Labels map[string]string `json:"labels"`
	} `json:"metadata"`
	Data map[string]string `json:"data"`
}

// TestInstall installs a ConfigMap with kube.Install, and installs it again
// when the program restarts, keeping what others added to it.
func TestInstall(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	manifest := fmt.Sprintf("apiVersion: v1\nkind: ConfigMap\nmetadata:\n  name: settings\n  namespace: %s\ndata:\n  color: blue\n", ns)
	install := kube.Install(func() []byte { return []byte(manifest) })
	path := client.Path("v1", "configmaps", ns, "settings")
	stop := release(t, &kube.Manager{Name: "installer"}, install)
	var cm installedConfigMap
	e2e.Eventually(t, 30*time.Second, func() error { return e2e.Get(t.Context(), c, path, &cm) })
	if cm.Metadata.Labels["kube.imjasonh.github.io/managed-by"] != "installer" || cm.Data["color"] != "blue" {
		t.Errorf("installed ConfigMap = %+v", cm)
	}
	if err := stop(); err != nil {
		t.Fatal(err)
	}

	if err := c.Patch(t.Context(), path, "application/merge-patch+json", nil, []byte(`{"data":{"color":"red","size":"large"}}`), nil); err != nil {
		t.Fatal(err)
	}
	release(t, &kube.Manager{Name: "installer"}, install)
	e2e.Eventually(t, 30*time.Second, func() error {
		if err := e2e.Get(t.Context(), c, path, &cm); err != nil {
			return err
		}
		if cm.Data["color"] != "blue" || cm.Data["size"] != "large" {
			return fmt.Errorf("data = %v, want the manifest's color and the size that someone else added", cm.Data)
		}
		return nil
	})

	manifest = "apiVersion: v1\nkind: ConfigMap\nmetadata:\n  name: settings\n"
	if err := failedRelease(t, &kube.Manager{Name: "installer"}, install); !strings.Contains(err.Error(), "ConfigMap settings is namespaced, so it needs metadata.namespace") {
		t.Errorf("installing a ConfigMap without a namespace: %v", err)
	}
}

// TestGenerateInstall installs a program that installs an admission policy
// with parameters, from what its generate command wrote, and runs it with
// the generated RBAC rules. The API server lets only someone who can read a
// policy's parameters create the policy and its binding, so a missing rule
// fails the test.
func TestGenerateInstall(t *testing.T) {
	c := e2e.Client(t)
	reg := imagetest.Registry(t)
	imagetest.Base(t, reg+"/chainguard/static:latest", "linux/amd64")
	// The policy's parameter is in this namespace, so the YAML has a Role
	// there. envtest has no namespace controller to delete it, so an earlier
	// run may have created it.
	if err := c.Create(t.Context(), "/api/v1/namespaces", map[string]any{
		"apiVersion": "v1", "kind": "Namespace", "metadata": map[string]any{"name": "installer-params"},
	}, nil); err != nil && !client.IsAlreadyExists(err) {
		t.Fatal(err)
	}
	rules := func(in installation) map[string]string {
		out := map[string]string{}
		for _, obj := range in.objects {
			if obj["kind"] == "ClusterRole" || obj["kind"] == "Role" {
				ns, _ := obj["metadata"].(map[string]any)["namespace"].(string)
				b, _ := json.Marshal(obj["rules"])
				out[obj["kind"].(string)+" "+ns] = string(b)
			}
		}
		return out
	}
	in := generateExample(t, reg, "e2e/testdata/installer", "installer", "-replicas=1")
	got := rules(in)
	for role, want := range map[string][]string{
		"ClusterRole ": {
			`{"apiGroups":[""],"resourceNames":["*"],"resources":["configmaps"],"verbs":["get"]}`,
			`{"apiGroups":["admissionregistration.k8s.io"],"resourceNames":["installer-colors"],"resources":["validatingadmissionpolicies","validatingadmissionpolicybindings"],"verbs":["create","patch"]}`,
		},
		"Role installer-params": {
			`{"apiGroups":[""],"resourceNames":["installer-colors"],"resources":["configmaps"],"verbs":["create","get","patch"]}`,
		},
	} {
		for _, w := range want {
			if !strings.Contains(got[role], w) {
				t.Errorf("%s rules = %s, want %s", role, got[role], w)
			}
		}
	}
	t.Cleanup(func() {
		ctx := context.WithoutCancel(t.Context())
		for _, r := range []string{"validatingadmissionpolicybindings", "validatingadmissionpolicies"} {
			_ = c.Delete(ctx, client.Path("admissionregistration.k8s.io/v1", r, "", "installer-colors"), client.DeleteOptions{})
		}
	})
	in.apply(t, c)
	exe := in.executable(t, "installer")
	out := in.runInstalled(t, exe, serviceAccountKubeconfig(t, c, "installer", "installer"))

	e2e.Eventually(t, 30*time.Second, func() error {
		return e2e.Get(t.Context(), c, client.Path("admissionregistration.k8s.io/v1", "validatingadmissionpolicybindings", "", "installer-colors"), &map[string]any{})
	})
	params := client.Path("v1", "configmaps", "installer-params", "installer-colors")
	if err := c.Patch(t.Context(), params, "application/merge-patch+json", nil, []byte(`{"data":{"forbidden":"red"}}`), nil); err != nil {
		t.Fatal(err)
	}
	ns := e2e.Namespace(t, c)
	configMap := func(name, color string) map[string]any {
		return map[string]any{
			"apiVersion": "v1", "kind": "ConfigMap",
			"metadata": map[string]any{"name": name, "labels": map[string]any{"installer-test": "true"}},
			"data":     map[string]any{"color": color},
		}
	}
	tries := 0
	e2e.Eventually(t, 30*time.Second, func() error {
		tries++
		err := c.Create(t.Context(), client.Path("v1", "configmaps", ns, ""), configMap(fmt.Sprintf("red-%d", tries), "red"), nil)
		switch {
		case err == nil:
			return fmt.Errorf("created a red ConfigMap")
		case !strings.Contains(err.Error(), "the color red is forbidden"):
			return err
		}
		return nil
	})
	if err := c.Create(t.Context(), client.Path("v1", "configmaps", ns, ""), configMap("blue", "blue"), nil); err != nil {
		t.Errorf("creating a blue ConfigMap: %v", err)
	}
	noPermissionErrors(t, out)

	got = rules(generateExample(t, reg, "e2e/testdata/installer", "installer", "-replicas=1", "--", "-install=false"))
	if _, ok := got["Role installer-params"]; ok {
		t.Error("with -install=false, the YAML has a Role in installer-params")
	}
	for role, r := range got {
		if strings.Contains(r, "configmaps") || strings.Contains(r, "validatingadmissionpolic") {
			t.Errorf("with -install=false, %s rules = %s", role, r)
		}
	}
}
