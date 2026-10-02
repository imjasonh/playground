package kube

import (
	"bytes"
	"context"
	"crypto/tls"
	"errors"
	"fmt"
	"maps"
	"net"
	"net/http"
	"net/url"
	"slices"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/imjasonh/playground/kube/internal/certs"
	"github.com/imjasonh/playground/kube/internal/client"
)

// certRefresh is how often each replica rereads the webhook certificate
// Secret, to renew the certificate and to pick up another replica's renewal.
var certRefresh = time.Minute

// webhookServer serves admission and conversion webhooks over HTTPS. Every
// replica runs one, whether or not it holds a lease, because the API server
// sends webhook requests to any replica behind the Service.
type webhookServer struct {
	m      *Manager
	mux    *http.ServeMux
	cert   atomic.Pointer[tls.Certificate]
	ready  atomic.Bool
	srv    *http.Server
	hosts  []string
	secret Key
	// Exactly one of url and service is set.
	url     string
	service struct {
		namespace, name string
		port            int
	}

	mu         sync.Mutex
	bundle     []byte
	validating map[string]registered // by webhook name
	mutating   map[string]registered
	onBundle   []func(context.Context) error
	builtinNS  []string
}

// registered is a webhook definition without its clientConfig, and the path
// that serves it.
type registered struct {
	hook map[string]any
	path string
}

func (m *Manager) webhooks() *webhookServer {
	m.mu.Lock()
	defer m.mu.Unlock()
	if m.hooks == nil {
		m.hooks = &webhookServer{
			m:          m,
			mux:        http.NewServeMux(),
			validating: map[string]registered{},
			mutating:   map[string]registered{},
		}
	}
	return m.hooks
}

func (m *Manager) needsWebhooks() bool {
	m.mu.Lock()
	defer m.mu.Unlock()
	return m.hooks != nil
}

// ownNamespace is the namespace of the manager's own objects: its leases and
// its webhook certificate.
func (m *Manager) ownNamespace() string {
	switch {
	case m.LeaseNamespace != "":
		return m.LeaseNamespace
	case m.client.Namespace != "":
		return m.client.Namespace
	default:
		return "default"
	}
}

// handle registers an HTTP handler on the webhook server.
func (ws *webhookServer) handle(path string, h http.HandlerFunc) {
	ws.mux.HandleFunc(path, func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "use POST", http.StatusMethodNotAllowed)
			return
		}
		h(w, r)
	})
}

// addAdmission registers a validating or mutating webhook for a resource.
// The framework fills in its clientConfig when it applies the configuration.
func (ws *webhookServer) addAdmission(mutating bool, name, path string, hook map[string]any) error {
	ws.mu.Lock()
	defer ws.mu.Unlock()
	set, kind := ws.validating, "validating"
	if mutating {
		set, kind = ws.mutating, "mutating"
	}
	if _, ok := set[name]; ok {
		return fmt.Errorf("kube: two controllers register %s webhooks for %s", kind, name)
	}
	set[name] = registered{hook: hook, path: path}
	return nil
}

// clientConfig is how the API server reaches path on this server.
func (ws *webhookServer) clientConfig(path string) map[string]any {
	ws.mu.Lock()
	defer ws.mu.Unlock()
	cc := map[string]any{"caBundle": slices.Clone(ws.bundle)}
	if ws.url != "" {
		cc["url"] = ws.url + path
	} else {
		cc["service"] = map[string]any{"namespace": ws.service.namespace, "name": ws.service.name, "path": path, "port": ws.service.port}
	}
	return cc
}

// whenBundleChanges runs fn now and again whenever the CA bundle changes,
// for objects that embed it, such as CustomResourceDefinitions with a
// conversion webhook.
func (ws *webhookServer) whenBundleChanges(fn func(context.Context) error) {
	ws.mu.Lock()
	defer ws.mu.Unlock()
	ws.onBundle = append(ws.onBundle, fn)
}

// start obtains a serving certificate, starts serving, and registers the
// webhook configurations with the API server.
func (ws *webhookServer) start(ctx context.Context) error {
	m := ws.m
	switch {
	case m.WebhookURL != "":
		u, err := url.Parse(m.WebhookURL)
		if err != nil || u.Scheme != "https" || u.Hostname() == "" {
			return fmt.Errorf("kube: WebhookURL %q must be an https URL", m.WebhookURL)
		}
		ws.url = strings.TrimSuffix(u.String(), "/")
		ws.hosts = []string{u.Hostname()}
	case m.WebhookService != "":
		ns, name, ok := strings.Cut(m.WebhookService, "/")
		if !ok {
			ns, name = m.ownNamespace(), m.WebhookService
		}
		ws.service.namespace, ws.service.name, ws.service.port = ns, name, 443
		ws.hosts = []string{name + "." + ns + ".svc", name + "." + ns + ".svc.cluster.local", name + "." + ns, name}
	default:
		return errors.New("kube: a controller has webhooks, so the API server needs a way to reach this program: " +
			"set Manager.WebhookService (-webhook-service) to a Service that routes port 443 to the webhook port, " +
			"or Manager.WebhookURL (-webhook-url) when running outside the cluster")
	}
	ws.builtinNS = []string{"kube-system"}
	if own := ws.service.namespace; own != "" && own != "kube-system" {
		ws.builtinNS = append(ws.builtinNS, own)
	}
	ws.secret = Key{Namespace: m.ownNamespace(), Name: labelValue(m.Name) + "-webhook-tls"}
	if err := ws.refresh(ctx); err != nil {
		return err
	}
	addr := m.WebhookAddr
	if addr == "" {
		addr = ":9443"
	}
	ln, err := net.Listen("tcp", addr)
	if err != nil {
		return err
	}
	ws.srv = &http.Server{
		Handler:           ws.mux,
		ReadHeaderTimeout: 10 * time.Second,
		TLSConfig: &tls.Config{
			MinVersion:     tls.VersionTLS12,
			GetCertificate: func(*tls.ClientHelloInfo) (*tls.Certificate, error) { return ws.cert.Load(), nil },
		},
	}
	go func() {
		if err := ws.srv.ServeTLS(ln, "", ""); err != nil && !errors.Is(err, http.ErrServerClosed) {
			m.log.Error("webhook server failed", "err", err)
		}
	}()
	m.log.Info("serving webhooks", "addr", ln.Addr().String(), "hosts", ws.hosts)
	if err := ws.applyConfigurations(ctx); err != nil {
		ws.srv.Close()
		return err
	}
	ws.ready.Store(true)
	go ws.refreshLoop(ctx)
	return nil
}

func (ws *webhookServer) stop() {
	if ws.srv != nil {
		ws.srv.Close()
	}
}

func (ws *webhookServer) refreshLoop(ctx context.Context) {
	t := time.NewTicker(certRefresh)
	defer t.Stop()
	for {
		select {
		case <-ctx.Done():
			return
		case <-t.C:
		}
		ws.mu.Lock()
		old := slices.Clone(ws.bundle)
		ws.mu.Unlock()
		if err := ws.refresh(ctx); err != nil {
			ws.m.log.Warn("refreshing the webhook certificate failed", "err", err)
			continue
		}
		ws.mu.Lock()
		changed := !bytes.Equal(old, ws.bundle)
		ws.mu.Unlock()
		if !changed {
			continue
		}
		ws.m.log.Info("the webhook CA bundle changed; updating webhook configurations")
		if err := ws.applyConfigurations(ctx); err != nil {
			ws.m.log.Warn("updating webhook configurations failed", "err", err)
		}
	}
}

// tlsSecret is the Secret that holds the webhook certificates, shared by
// every replica.
type tlsSecret struct {
	TypeMeta
	Metadata ObjectMeta        `json:"metadata"`
	Type     string            `json:"type,omitempty"`
	Data     map[string][]byte `json:"data"`
}

// refresh reads the certificate Secret, creating or renewing certificates
// in it when needed, and serves the result. Replicas that race to create or
// renew it settle on whichever write the API server accepts first.
func (ws *webhookServer) refresh(ctx context.Context) error {
	c := ws.m.client
	path := client.Path("v1", "secrets", ws.secret.Namespace, ws.secret.Name)
	for range 5 {
		now := time.Now()
		var s tlsSecret
		err := c.Get(ctx, path, &s)
		if client.IsNotFound(err) {
			ca, err := certs.NewCA(ws.secret.Name+"-ca", now)
			if err != nil {
				return err
			}
			serving, err := certs.NewServing(ca, ws.hosts, now)
			if err != nil {
				return err
			}
			s = tlsSecret{
				TypeMeta: TypeMeta{APIVersion: "v1", Kind: "Secret"},
				Metadata: ObjectMeta{
					Name: ws.secret.Name, Namespace: ws.secret.Namespace,
					Labels: map[string]string{newLabelKeys(ws.m.Domain).managedBy: labelValue(ws.m.Name)},
				},
				Type: "Opaque",
				Data: map[string][]byte{"ca.crt": ca.Cert, "ca.key": ca.Key, "tls.crt": serving.Cert, "tls.key": serving.Key},
			}
			err = c.Create(ctx, client.Path("v1", "secrets", ws.secret.Namespace, ""), s, nil)
			if client.IsAlreadyExists(err) {
				continue
			}
			if err != nil {
				return fmt.Errorf("creating webhook certificate Secret %s: %w", ws.secret, err)
			}
			return ws.use(serving, ca.Cert)
		}
		if err != nil {
			return fmt.Errorf("reading webhook certificate Secret %s: %w", ws.secret, err)
		}
		if s.Data == nil {
			s.Data = map[string][]byte{}
		}
		ca := certs.Pair{Cert: s.Data["ca.crt"], Key: s.Data["ca.key"]}
		serving := certs.Pair{Cert: s.Data["tls.crt"], Key: s.Data["tls.key"]}
		changed := false
		if certs.ExpiresSoon(ca, now) {
			next, err := certs.NewCA(ws.secret.Name+"-ca", now)
			if err != nil {
				return err
			}
			if len(ca.Cert) > 0 {
				s.Data["ca-previous.crt"] = ca.Cert
			}
			ca, changed = next, true
		}
		if changed || !certs.Usable(ca, serving, ws.hosts, now) {
			if serving, err = certs.NewServing(ca, ws.hosts, now); err != nil {
				return err
			}
			changed = true
		}
		if changed {
			maps.Copy(s.Data, map[string][]byte{"ca.crt": ca.Cert, "ca.key": ca.Key, "tls.crt": serving.Cert, "tls.key": serving.Key})
			err := c.Update(ctx, path, s, nil)
			if client.IsConflict(err) {
				continue
			}
			if err != nil {
				return fmt.Errorf("renewing the webhook certificate in Secret %s: %w", ws.secret, err)
			}
			ws.m.log.Info("renewed the webhook certificate", "secret", ws.secret.String())
		}
		// Until the previous CA expires, the API server also trusts it, so a
		// replica still serving a certificate it signed keeps working.
		bundle := slices.Clone(ca.Cert)
		if prev := s.Data["ca-previous.crt"]; certs.ValidAt(prev, now) {
			bundle = append(bundle, prev...)
		}
		return ws.use(serving, bundle)
	}
	return fmt.Errorf("the webhook certificate Secret %s kept changing; giving up for now", ws.secret)
}

func (ws *webhookServer) use(serving certs.Pair, bundle []byte) error {
	cert, err := tls.X509KeyPair(serving.Cert, serving.Key)
	if err != nil {
		return fmt.Errorf("loading the webhook certificate: %w", err)
	}
	ws.cert.Store(&cert)
	ws.mu.Lock()
	ws.bundle = bundle
	ws.mu.Unlock()
	return nil
}

// configurationName names the manager's webhook configurations.
func (ws *webhookServer) configurationName() string { return labelValue(ws.m.Name) }

// applyConfigurations registers the validating and mutating webhooks, and
// updates objects that embed the CA bundle. When the manager has no webhooks
// of a kind, it deletes the configuration of that kind that an earlier
// version of the program left behind: its webhooks would fail every request.
func (ws *webhookServer) applyConfigurations(ctx context.Context) error {
	c := ws.m.client
	keys := newLabelKeys(ws.m.Domain)
	ws.mu.Lock()
	kinds := []struct {
		kind, resource string
		hooks          map[string]registered
	}{
		{"ValidatingWebhookConfiguration", "validatingwebhookconfigurations", maps.Clone(ws.validating)},
		{"MutatingWebhookConfiguration", "mutatingwebhookconfigurations", maps.Clone(ws.mutating)},
	}
	onBundle := slices.Clone(ws.onBundle)
	ws.mu.Unlock()
	for _, k := range kinds {
		path := client.Path("admissionregistration.k8s.io/v1", k.resource, "", ws.configurationName())
		if len(k.hooks) == 0 {
			var existing struct {
				Metadata ObjectMeta `json:"metadata"`
			}
			err := c.Get(ctx, path, &existing)
			switch {
			case err == nil && existing.Metadata.Labels[keys.managedBy] != "":
				if err := c.Delete(ctx, path, client.DeleteOptions{UID: existing.Metadata.UID}); err != nil && !client.IsNotFound(err) && !client.IsConflict(err) {
					return fmt.Errorf("deleting stale %s %s: %w", k.kind, ws.configurationName(), err)
				}
				ws.m.log.Info("deleted a webhook configuration that this program no longer needs", "kind", k.kind, "name", ws.configurationName())
			case err != nil && !client.IsNotFound(err) && !client.IsForbidden(err):
				return fmt.Errorf("reading %s %s: %w", k.kind, ws.configurationName(), err)
			}
			continue
		}
		var hooks []any
		for _, name := range slices.Sorted(maps.Keys(k.hooks)) {
			h := maps.Clone(k.hooks[name].hook)
			h["clientConfig"] = ws.clientConfig(k.hooks[name].path)
			hooks = append(hooks, h)
		}
		body := map[string]any{
			"apiVersion": "admissionregistration.k8s.io/v1",
			"kind":       k.kind,
			"metadata": map[string]any{
				"name":   ws.configurationName(),
				"labels": map[string]string{keys.managedBy: labelValue(ws.m.Name)},
			},
			"webhooks": hooks,
		}
		if err := c.Apply(ctx, path, ws.m.Name, true, body, nil); err != nil {
			return fmt.Errorf("registering %s %s: %w", k.kind, ws.configurationName(), err)
		}
	}
	for _, fn := range onBundle {
		if err := fn(ctx); err != nil {
			return err
		}
	}
	return nil
}

// webhookName is a webhook's name in a configuration: a domain-like name
// with at least three parts.
func (ws *webhookServer) webhookName(ti *typeInfo, plural string) string {
	g := ti.group
	if g == "" {
		g = "core"
	}
	name := plural + "." + g
	if strings.Count(name, ".") < 2 {
		name += "." + ws.m.Domain
	}
	return name
}

// admissionRule is the webhook definition for a resource, except clientConfig.
func (ws *webhookServer) admissionRule(ti *typeInfo, res resolved, builtin bool) map[string]any {
	scope := "Cluster"
	if res.namespaced {
		scope = "Namespaced"
	}
	hook := map[string]any{
		"name": ws.webhookName(ti, res.plural),
		"rules": []any{map[string]any{
			"operations":  []string{"CREATE", "UPDATE"},
			"apiGroups":   []string{ti.group},
			"apiVersions": []string{ti.version},
			"resources":   []string{res.plural},
			"scope":       scope,
		}},
		"admissionReviewVersions": []string{"v1"},
		"sideEffects":             "None",
		"failurePolicy":           "Fail",
		"matchPolicy":             "Equivalent",
		"timeoutSeconds":          10,
	}
	switch {
	case res.namespaced && ws.m.Namespace != "":
		hook["namespaceSelector"] = map[string]any{"matchExpressions": []any{map[string]any{
			"key": "kubernetes.io/metadata.name", "operator": "In", "values": []string{ws.m.Namespace},
		}}}
	case res.namespaced && builtin:
		// A webhook for a built-in type that the controller's own pods
		// depend on, such as Pods, could stop those pods from being created
		// while the webhook is down. Skip the namespaces where the
		// controller and the cluster's system components run.
		hook["namespaceSelector"] = map[string]any{"matchExpressions": []any{map[string]any{
			"key": "kubernetes.io/metadata.name", "operator": "NotIn", "values": slices.Clone(ws.builtinNS),
		}}}
	}
	return hook
}

func groupOrCore(g string) string {
	if g == "" {
		return "core"
	}
	return g
}

func admissionPath(kind string, ti *typeInfo, plural string) string {
	return "/" + kind + "/" + groupOrCore(ti.group) + "/" + ti.version + "/" + plural
}

func (ws *webhookServer) serving() bool { return ws == nil || ws.ready.Load() }
