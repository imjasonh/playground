package kube

import (
	"encoding/json"
	"io"
	"maps"
	"net/http"
	"net/http/httptest"
	"path"
	"regexp"
	"slices"
	"strings"
	"sync"
	"testing"

	"github.com/imjasonh/playground/kube/internal/client"
)

func TestObjectName(t *testing.T) {
	for in, want := range map[string]string{"website": "website", "My_Controller": "my-controller", "__": "controller", "a.b": "a-b"} {
		if got := objectName(in); got != want {
			t.Errorf("objectName(%q) = %q, want %q", in, got, want)
		}
	}
}

// subdomain matches the names that the API server accepts for most kinds,
// including Leases, Secrets, and webhook configurations.
var subdomain = regexp.MustCompile(`^[a-z0-9]([-a-z0-9]*[a-z0-9])?(\.[a-z0-9]([-a-z0-9]*[a-z0-9])?)*$`)

// namesAPI keeps the objects written to it by path, and rejects names that
// the API server rejects.
type namesAPI struct {
	mu   sync.Mutex
	objs map[string][]byte
}

func (a *namesAPI) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	a.mu.Lock()
	defer a.mu.Unlock()
	body, err := io.ReadAll(r.Body)
	if err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	p := r.URL.Path
	switch r.Method {
	case http.MethodGet:
		if strings.HasSuffix(p, "/leases") {
			items := []json.RawMessage{}
			for k, obj := range a.objs {
				if path.Dir(k) == p {
					items = append(items, obj)
				}
			}
			_ = json.NewEncoder(w).Encode(map[string]any{"items": items})
			return
		}
		obj, ok := a.objs[p]
		if !ok {
			http.NotFound(w, r)
			return
		}
		_, _ = w.Write(obj)
		return
	case http.MethodPost:
		var o struct {
			Metadata ObjectMeta `json:"metadata"`
		}
		if err := json.Unmarshal(body, &o); err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		p += "/" + o.Metadata.Name
	case http.MethodPut, http.MethodPatch:
	default:
		http.Error(w, "unexpected request", http.StatusMethodNotAllowed)
		return
	}
	if name := path.Base(p); len(name) > 253 || !subdomain.MatchString(name) {
		w.WriteHeader(http.StatusUnprocessableEntity)
		_ = json.NewEncoder(w).Encode(map[string]any{"kind": "Status", "reason": "Invalid", "message": "invalid name " + name})
		return
	}
	a.objs[p] = body
	_, _ = w.Write(body)
}

func (a *namesAPI) paths() []string {
	a.mu.Lock()
	defer a.mu.Unlock()
	return slices.Sorted(maps.Keys(a.objs))
}

func TestInstallName(t *testing.T) {
	for _, tc := range []struct{ name, namespace, want string }{
		{"website", "website", "website"},
		{"website", "team-a", "website.team-a"},
	} {
		if got := installName(tc.name, tc.namespace); got != tc.want {
			t.Errorf("installName(%q, %q) = %q, want %q", tc.name, tc.namespace, got, tc.want)
		}
	}
}

// TestObjectNamesForAnyProgramName runs a manager named like a program built
// from cmd/Web_Site. The Leases, the webhook certificate Secret, and the
// webhook configuration that it writes need lowercase names, or the API
// server rejects them. The webhook configuration is cluster-scoped, so its
// name includes the manager's namespace.
func TestObjectNamesForAnyProgramName(t *testing.T) {
	api := &namesAPI{objs: map[string][]byte{}}
	srv := httptest.NewServer(api)
	t.Cleanup(srv.Close)
	cl, err := client.New(&client.Config{Host: srv.URL}, "test")
	if err != nil {
		t.Fatal(err)
	}
	m := testManager()
	m.client, m.Name, m.LeaseNamespace, m.Shards = cl, "Web_Site", "shop", 2
	m.WebhookService, m.WebhookAddr = "web-site", "127.0.0.1:0"

	s := newSharder(m)
	s.sync(t.Context())
	for _, sh := range s.shards {
		if !sh.held {
			t.Errorf("the replica didn't take shard %s", sh.name)
		}
	}
	ws := m.webhooks()
	if err := ws.addAdmission(false, "configmaps", "/validate", map[string]any{"name": "configmaps.core.kube.imjasonh.github.io"}); err != nil {
		t.Fatal(err)
	}
	if err := ws.start(t.Context()); err != nil {
		t.Fatal(err)
	}
	ws.stop()

	want := []string{
		"/api/v1/namespaces/shop/secrets/web-site-webhook-tls",
		"/apis/admissionregistration.k8s.io/v1/validatingwebhookconfigurations/web-site.shop",
		"/apis/coordination.k8s.io/v1/namespaces/shop/leases/" + s.memberName(),
		"/apis/coordination.k8s.io/v1/namespaces/shop/leases/web-site-shard-0",
		"/apis/coordination.k8s.io/v1/namespaces/shop/leases/web-site-shard-1",
	}
	if got := api.paths(); !slices.Equal(got, want) {
		t.Errorf("objects =\n%s\nwant\n%s", strings.Join(got, "\n"), strings.Join(want, "\n"))
	}
	if !strings.HasPrefix(s.memberName(), "web-site-member-") {
		t.Errorf("membership Lease %s doesn't start with web-site-member-", s.memberName())
	}
}
