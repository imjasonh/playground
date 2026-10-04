package e2e_test

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net"
	"net/http"
	"slices"
	"strings"
	"syscall"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
	"github.com/imjasonh/playground/kube/internal/image/imagetest"
)

type idleConfigMaps struct{}

func (idleConfigMaps) Reconcile(context.Context, *ConfigMapMeta) error { return nil }

// TestServeListenFailure runs a manager, without leader election, whose
// kube.Serve address is in use. Run must return the error instead of
// stopping as if its context had ended.
func TestServeListenFailure(t *testing.T) {
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer ln.Close()
	m := &kube.Manager{Name: "serve-listen-e2e", Kubeconfig: e2e.Env(t).Kubeconfig, Logger: e2e.Logger(t), ServeAddr: ln.Addr().String()}
	ctx, cancel := context.WithTimeout(t.Context(), 30*time.Second)
	defer cancel()
	err = m.Run(ctx, kube.For[ConfigMapMeta](idleConfigMaps{}, kube.Named("serve-listen")), kube.Serve(http.NotFoundHandler()))
	if !errors.Is(err, syscall.EADDRINUSE) {
		t.Errorf("Run = %v, want an error that the address is in use", err)
	}
	if ctx.Err() != nil {
		t.Errorf("Run returned only once its context ended: %v", ctx.Err())
	}
}

// TestGenerateProbe installs the probe example, which requests tokens for
// its own service account, reviews its callers' tokens, and triggers
// reconciles from its kube.Serve handler. It runs two replicas of the
// image's program with the generated RBAC rules, and the API server issues
// and reviews the tokens.
func TestGenerateProbe(t *testing.T) {
	c := e2e.Client(t)
	reg := imagetest.Registry(t)
	imagetest.Base(t, reg+"/chainguard/static:latest", "linux/amd64")
	in := generateExample(t, reg, "probe", "probe")
	byKind := map[string]string{}
	for _, obj := range in.objects {
		b, _ := json.Marshal(obj)
		byKind[obj["kind"].(string)] = string(b)
	}
	for kind, want := range map[string]string{
		"ClusterRole": `{"apiGroups":["authentication.k8s.io"],"resources":["tokenreviews"],"verbs":["create"]}`,
		"Role":        `{"apiGroups":[""],"resourceNames":["probe"],"resources":["serviceaccounts/token"],"verbs":["create"]}`,
		"Service":     `{"name":"serve","port":80,"targetPort":"serve"}`,
	} {
		if !strings.Contains(byKind[kind], want) {
			t.Errorf("%s = %s, want %s", kind, byKind[kind], want)
		}
	}
	if strings.Contains(byKind["ClusterRole"], "serviceaccounts") {
		t.Errorf("the ClusterRole lets the program request tokens for other service accounts: %s", byKind["ClusterRole"])
	}
	if !slices.Contains(in.args, "-serve-addr=:8081") || !slices.Contains(in.args, "-leader-elect") {
		t.Errorf("args = %q", in.args)
	}
	in.apply(t, c)
	exe := in.executable(t, "probe")
	kubeconfig := serviceAccountKubeconfig(t, c, "probe", "probe")
	var addrs []string
	var outs []*syncBuffer
	for range 2 {
		r := in
		r.serveAddr = freeAddr(t)
		outs = append(outs, r.runInstalled(t, exe, kubeconfig))
		addrs = append(addrs, r.serveAddr)
	}

	ns := e2e.Namespace(t, c)
	if err := c.Create(t.Context(), client.Path("v1", "serviceaccounts", ns, ""), map[string]any{
		"apiVersion": "v1", "kind": "ServiceAccount", "metadata": map[string]any{"name": "ci"},
	}, nil); err != nil {
		t.Fatal(err)
	}
	token := func(audiences ...string) string {
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
		if err := c.Create(t.Context(), client.Path("v1", "serviceaccounts", ns, "ci", "token"), map[string]any{
			"apiVersion": "authentication.k8s.io/v1", "kind": "TokenRequest", "spec": spec,
		}, &tr); err != nil {
			t.Fatal(err)
		}
		return tr.Status.Token
	}
	type response struct {
		code  int
		body  string
		close bool
	}
	call := func(method, addr, path, token string) response {
		t.Helper()
		req, err := http.NewRequestWithContext(t.Context(), method, "http://"+addr+path, nil)
		if err != nil {
			t.Fatal(err)
		}
		req.Header.Set("Authorization", "Bearer "+token)
		resp, err := http.DefaultClient.Do(req)
		if err != nil {
			t.Fatal(err)
		}
		defer resp.Body.Close()
		b, _ := io.ReadAll(resp.Body)
		return response{resp.StatusCode, string(b), resp.Close}
	}

	t.Log("Every replica serves, and accepts only tokens for its audience.")
	ci := token("probe")
	for _, addr := range addrs {
		if r := call(http.MethodGet, addr, "/whoami", ci); r.code != http.StatusOK || r.body != "system:serviceaccount:"+ns+":ci\n" {
			t.Errorf("GET /whoami on %s = %+v", addr, r)
		}
	}
	for name, tok := range map[string]string{"another audience": token("other"), "the API server's audience": token()} {
		if r := call(http.MethodGet, addrs[0], "/whoami", tok); r.code != http.StatusUnauthorized {
			t.Errorf("GET /whoami with a token for %s = %+v, want 401", name, r)
		}
	}

	t.Log("A probe of the program's own API sends a token that the program requested.")
	probe := client.Path("examples.kube.imjasonh.github.io/v1", "probes", ns, "self")
	e2e.Eventually(t, time.Minute, func() error {
		// The replica that holds the lease creates the CRD.
		return c.Create(t.Context(), client.Path("examples.kube.imjasonh.github.io/v1", "probes", ns, ""), map[string]any{
			"apiVersion": "examples.kube.imjasonh.github.io/v1", "kind": "Probe",
			"metadata": map[string]any{"name": "self"},
			"spec":     map[string]any{"url": "http://" + addrs[0] + "/whoami", "audience": "probe"},
		}, nil)
	})
	var p struct {
		Status struct {
			Code      int       `json:"code"`
			Message   string    `json:"message"`
			CheckedAt time.Time `json:"checkedAt"`
		} `json:"status"`
	}
	e2e.Eventually(t, 30*time.Second, func() error {
		if err := e2e.Get(t.Context(), c, probe, &p); err != nil {
			return err
		}
		if p.Status.Code != http.StatusOK || p.Status.Message != "system:serviceaccount:probe:probe" {
			return fmt.Errorf("status = %+v", p.Status)
		}
		return nil
	})
	checked := p.Status.CheckedAt
	e2e.Never(t, 2*time.Second, func() error {
		if err := e2e.Get(t.Context(), c, probe, &p); err != nil {
			return err
		}
		if !p.Status.CheckedAt.Equal(checked) {
			return fmt.Errorf("the probe ran again at %v without a trigger", p.Status.CheckedAt)
		}
		return nil
	})

	t.Log("The replica that holds the lease triggers a check, and the other refuses.")
	var leader string
	e2e.Eventually(t, 30*time.Second, func() error {
		leader = ""
		var got []response
		for _, addr := range addrs {
			r := call(http.MethodPost, addr, "/probes/"+ns+"/self", ci)
			got = append(got, r)
			switch {
			case r.code == http.StatusAccepted && leader == "":
				leader = addr
			case r.code != http.StatusServiceUnavailable || !r.close:
				return fmt.Errorf("responses = %+v, want 202 from one replica and 503 with Connection: close from the other", got)
			}
		}
		if leader == "" {
			return fmt.Errorf("responses = %+v, want 202 from one replica", got)
		}
		return nil
	})
	e2e.Eventually(t, 30*time.Second, func() error {
		if err := e2e.Get(t.Context(), c, probe, &p); err != nil {
			return err
		}
		if !p.Status.CheckedAt.After(checked) {
			return fmt.Errorf("checkedAt = %v, want a check after %v", p.Status.CheckedAt, checked)
		}
		return nil
	})
	for _, addr := range addrs {
		if r := call(http.MethodPost, addr, "/probes/"+ns+"/missing", ci); r.code != http.StatusNotFound {
			t.Errorf("POST for a missing probe on %s = %+v, want 404", addr, r)
		}
	}
	if r := call(http.MethodPost, leader, "/probes/default/self", ci); r.code != http.StatusForbidden {
		t.Errorf("POST for a probe in another namespace = %+v, want 403", r)
	}
	for _, out := range outs {
		noPermissionErrors(t, out)
	}
}
