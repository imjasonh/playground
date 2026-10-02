package kube

import (
	"context"
	"errors"
	"flag"
	"fmt"
	"log/slog"
	"net"
	"net/http"
	"os"
	"os/signal"
	"path/filepath"
	"reflect"
	"slices"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"

	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/queue"
	"github.com/imjasonh/playground/kube/internal/schema"
)

// Manager runs controllers against one cluster. The zero value is ready to
// use; every field is optional.
type Manager struct {
	// Name identifies the program. It names the leader election lease and
	// appears in the User-Agent and on CustomResourceDefinitions the manager
	// installs. It defaults to the executable's name.
	Name string
	// Kubeconfig is the path of a kubeconfig file. When empty, the manager
	// uses $KUBECONFIG, then the pod's service account, then
	// $HOME/.kube/config.
	Kubeconfig string
	// Namespace limits every cache of a namespaced type to one namespace,
	// and admission webhooks for namespaced types to objects in it. Empty
	// means all namespaces.
	Namespace string
	// Domain prefixes the labels, annotations, and finalizers that the
	// framework adds to objects. It defaults to "kube.imjasonh.github.io".
	Domain string
	// LeaderElection makes replicas take turns: only the replica that holds
	// a Lease reconciles. Caches start only after the replica first holds
	// it, so standby replicas use almost no memory. A replica that loses the
	// Lease stops reconciling and tries to take it back; it keeps serving
	// webhooks.
	LeaderElection bool
	// Shards splits the objects that controllers reconcile into this many
	// groups, each held by one replica at a time through its own Lease, so
	// replicas share the work and a failed replica's groups move to the
	// others. Each object is reconciled by one replica at a time. Setting it
	// above 1 turns on LeaderElection. Every replica caches every object, so
	// shards divide reconcile work, not memory.
	Shards int
	// LeaseNamespace is where the Leases live, and the webhook certificate
	// Secret. It defaults to the configuration's namespace, or "default".
	LeaseNamespace string
	// Addr, when set, serves /healthz, /readyz, and Prometheus /metrics at
	// this address, for example ":8080".
	Addr string
	// Logger receives the framework's logs. It defaults to slog.Default().
	Logger *slog.Logger
	// DisableStreamingLists makes caches use paginated lists instead of
	// trying streaming lists (watches with sendInitialEvents) first.
	DisableStreamingLists bool
	// DisableInterning stops caches from sharing one copy of strings that
	// repeat across objects, such as label keys and namespaces.
	DisableInterning bool
	// Compression asks the API server to gzip responses. It cuts the bytes
	// of a streaming list of Pods about tenfold, but the API server spends
	// CPU compressing every one. Leave it off for controllers that run in
	// the cluster; turn it on over slow links.
	Compression bool

	// WebhookAddr is where the manager serves admission and conversion
	// webhooks over HTTPS, when a controller has them. It defaults to
	// ":9443". Every replica serves webhooks, whether or not it holds a
	// lease.
	WebhookAddr string
	// WebhookService is the Service through which the API server reaches
	// the webhooks, as "name" in the manager's namespace or
	// "namespace/name". It must select the controller's pods and route port
	// 443 to WebhookAddr. The manager makes and renews the certificate,
	// keeps it in a Secret that replicas share, and registers the webhooks
	// with the API server.
	WebhookService string
	// WebhookURL is the base URL through which the API server reaches the
	// webhooks of a manager that runs outside the cluster, for example
	// "https://192.0.2.10:9443". It takes precedence over WebhookService.
	WebhookURL string

	client  *client.Client
	log     *slog.Logger
	metrics *metrics
	tracker *tracker
	ids     atomic.Int64
	runCtx  context.Context
	started atomic.Bool
	sharder *sharder

	mu          sync.Mutex
	caches      map[cacheKey]cache
	cacheDone   []chan struct{}
	resolved    map[*typeInfo]resolved
	controllers []Controller
	hooks       *webhookServer
}

type cacheKey struct {
	ti        *typeInfo
	namespace string
	selector  string
}

// Run runs controllers with a zero Manager until ctx is done.
func Run(ctx context.Context, controllers ...Controller) error {
	return (&Manager{}).Run(ctx, controllers...)
}

// Main is a main function for a controller program. It reads flags,
// stops on SIGINT or SIGTERM, runs controllers, and exits with status 1 if
// they fail. Flags: -kubeconfig, -namespace, -leader-elect, -shards, -addr,
// -webhook-addr, -webhook-service, -webhook-url, and -v for debug logs.
func Main(controllers ...Controller) {
	m := &Manager{}
	flag.StringVar(&m.Kubeconfig, "kubeconfig", "", "path to a kubeconfig file")
	flag.StringVar(&m.Namespace, "namespace", "", "watch only this namespace")
	flag.BoolVar(&m.LeaderElection, "leader-elect", false, "reconcile only while holding a Lease")
	flag.IntVar(&m.Shards, "shards", 1, "split reconciles across replicas in this many shards, each held through a Lease")
	flag.StringVar(&m.Addr, "addr", "", "address for /healthz, /readyz, and /metrics, for example :8080")
	flag.StringVar(&m.WebhookAddr, "webhook-addr", "", "address for HTTPS webhooks (default :9443)")
	flag.StringVar(&m.WebhookService, "webhook-service", "", "Service, as name or namespace/name, through which the API server reaches the webhooks")
	flag.StringVar(&m.WebhookURL, "webhook-url", "", "base https URL through which the API server reaches the webhooks, outside the cluster")
	verbose := flag.Bool("v", false, "log debug messages")
	flag.Parse()
	level := slog.LevelInfo
	if *verbose {
		level = slog.LevelDebug
	}
	m.Logger = slog.New(slog.NewTextHandler(os.Stderr, &slog.HandlerOptions{Level: level}))
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	if err := m.Run(ctx, controllers...); err != nil {
		m.Logger.Error("exiting", "err", err)
		stop()
		os.Exit(1)
	}
}

func (m *Manager) init() error {
	if m.Name == "" {
		m.Name = filepath.Base(os.Args[0])
	}
	if m.Domain == "" {
		m.Domain = "kube.imjasonh.github.io"
	}
	m.log = m.Logger
	if m.log == nil {
		m.log = slog.Default()
	}
	if m.client == nil {
		cfg, err := client.Load(m.Kubeconfig)
		if err != nil {
			return err
		}
		cfg.Compression = m.Compression
		if m.client, err = client.New(cfg, m.Name+" (kube; github.com/imjasonh/playground/kube)"); err != nil {
			return err
		}
		m.log.Info("connecting", "host", cfg.Host, "config", cfg.Source)
	}
	m.metrics = newMetrics()
	m.tracker = newTracker()
	m.caches = map[cacheKey]cache{}
	m.resolved = map[*typeInfo]resolved{}
	m.metrics.gauge("kube_cache_objects", "Objects held in each cache.", func() []sample {
		m.mu.Lock()
		defer m.mu.Unlock()
		var out []sample
		for k, c := range m.caches {
			out = append(out, sample{labels: []string{"type", k.ti.String(), "namespace", k.namespace, "selector", k.selector}, value: float64(c.size())})
		}
		return out
	})
	m.metrics.gauge("kube_tracked_dependencies", "Objects and queries that reconciles read.", func() []sample {
		return []sample{{value: float64(m.tracker.size())}}
	})
	return nil
}

// Run connects to the cluster and runs controllers until ctx is done. It
// returns nil when ctx is canceled, or an error if setup fails.
func (m *Manager) Run(ctx context.Context, controllers ...Controller) error {
	if err := m.init(); err != nil {
		return err
	}
	ctx, cancel := context.WithCancelCause(ctx)
	m.runCtx = ctx
	m.controllers = controllers
	// stops run in reverse order once ctx is canceled, so each part stops
	// after the parts that use it.
	var stops []func()
	defer func() {
		cancel(nil)
		for i := len(stops) - 1; i >= 0; i-- {
			stops[i]()
		}
	}()
	if m.Addr != "" {
		srv, err := m.serve()
		if err != nil {
			return err
		}
		stops = append(stops, func() { srv.Close() })
	}
	stops = append(stops, m.waitForCaches)
	for _, c := range controllers {
		if err := c.prepare(ctx, m); err != nil {
			return err
		}
	}
	if m.needsWebhooks() {
		if err := m.hooks.start(ctx); err != nil {
			return err
		}
		stops = append(stops, m.hooks.stop)
	}
	var reconcilers []Controller
	for _, c := range controllers {
		if c.reconciles() {
			reconcilers = append(reconcilers, c)
		}
	}
	if len(reconcilers) > 0 && (m.LeaderElection || m.Shards > 1) {
		m.sharder = newSharder(m)
		done := make(chan struct{})
		go func() {
			defer close(done)
			m.sharder.run(ctx)
		}()
		// Release the shards after reconciles stop, so the replica that
		// takes a shard over never overlaps a reconcile still running here.
		stops = append(stops, func() {
			<-done
			m.sharder.releaseAll()
		})
		select {
		case <-m.sharder.first:
		case <-ctx.Done():
		}
	}
	var wg sync.WaitGroup
	stops = append(stops, wg.Wait)
	if ctx.Err() == nil {
		for _, c := range reconcilers {
			if err := c.setup(ctx, m); err != nil {
				return err
			}
		}
		m.started.Store(true)
		for _, c := range reconcilers {
			wg.Go(func() {
				if err := c.run(ctx); err != nil {
					cancel(fmt.Errorf("controller %s: %w", c.controllerName(), err))
				}
			})
		}
	}
	<-ctx.Done()
	if cause := context.Cause(ctx); cause != nil && !errors.Is(cause, context.Canceled) {
		return cause
	}
	return nil
}

// waitForCaches waits for every cache's goroutine to return.
func (m *Manager) waitForCaches() {
	m.mu.Lock()
	done := slices.Clone(m.cacheDone)
	m.mu.Unlock()
	for _, d := range done {
		<-d
	}
}

func (m *Manager) serve() (*http.Server, error) {
	mux := http.NewServeMux()
	mux.HandleFunc("/healthz", func(w http.ResponseWriter, r *http.Request) { fmt.Fprintln(w, "ok") })
	// A standby replica is ready once its webhooks serve: the Service must
	// send webhook requests to it, though it doesn't reconcile.
	mux.HandleFunc("/readyz", func(w http.ResponseWriter, r *http.Request) {
		m.mu.Lock()
		hooks := m.hooks
		m.mu.Unlock()
		if !hooks.serving() {
			http.Error(w, "webhooks are not serving", http.StatusServiceUnavailable)
			return
		}
		if m.started.Load() {
			for _, c := range m.controllers {
				if c.reconciles() && !c.synced() {
					http.Error(w, "controller "+c.controllerName()+" is not synced", http.StatusServiceUnavailable)
					return
				}
			}
		}
		fmt.Fprintln(w, "ok")
	})
	mux.HandleFunc("/metrics", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "text/plain; version=0.0.4")
		m.metrics.write(w)
	})
	ln, err := net.Listen("tcp", m.Addr)
	if err != nil {
		return nil, err
	}
	srv := &http.Server{Handler: mux, ReadHeaderTimeout: 10 * time.Second}
	go func() {
		if err := srv.Serve(ln); err != nil && !errors.Is(err, http.ErrServerClosed) {
			m.log.Error("health server failed", "err", err)
		}
	}()
	m.log.Info("serving health and metrics", "addr", ln.Addr().String())
	return srv, nil
}

func (m *Manager) newID() int { return int(m.ids.Add(1)) }

func (m *Manager) informerConfig(res resolved, namespace, selector, ownerKey string) informerConfig {
	if !res.namespaced {
		namespace = ""
	}
	return informerConfig{
		namespace: namespace,
		selector:  selector,
		ownerKey:  ownerKey,
		streaming: !m.DisableStreamingLists,
		intern:    !m.DisableInterning,
	}
}

// resolve finds how the server serves ti, using discovery unless the type's
// tag already says.
func (m *Manager) resolve(ctx context.Context, ti *typeInfo) (resolved, error) {
	m.mu.Lock()
	r, ok := m.resolved[ti]
	m.mu.Unlock()
	if ok {
		return r, nil
	}
	if ti.plural != "" && ti.scope != "" {
		r = resolved{apiVersion: ti.apiVersion, plural: ti.plural, namespaced: ti.scope == "Namespaced"}
	} else {
		ar, err := m.client.Resource(ctx, ti.apiVersion, ti.kind)
		if err != nil {
			return resolved{}, err
		}
		r = resolved{apiVersion: ti.apiVersion, plural: ar.Name, namespaced: ar.Namespaced}
	}
	m.mu.Lock()
	m.resolved[ti] = r
	m.mu.Unlock()
	return r, nil
}

// ensureType makes sure the cluster serves a controller's primary type,
// installing a CustomResourceDefinition for types the program defines.
func (m *Manager) ensureType(ctx context.Context, crd crdSpec) (resolved, error) {
	if crd.ti.custom {
		if err := m.installCRD(ctx, crd); err != nil {
			return resolved{}, err
		}
	}
	return m.resolve(ctx, crd.ti)
}

// crdSpec describes a CustomResourceDefinition: the stored version, other
// served versions, and how to convert between them.
type crdSpec struct {
	ti         *typeInfo
	versions   []*typeInfo
	conversion map[string]any
}

func (m *Manager) installCRD(ctx context.Context, spec crdSpec) error {
	ti := spec.ti
	keys := newLabelKeys(m.Domain)
	name := ti.plural + "." + ti.group
	path := "/apis/apiextensions.k8s.io/v1/customresourcedefinitions/" + name
	var existing struct {
		Metadata ObjectMeta `json:"metadata"`
	}
	err := m.client.Get(ctx, path, &existing)
	switch {
	case err == nil && existing.Metadata.Labels[keys.managedBy] == "":
		m.log.Info("using CustomResourceDefinition that something else installed", "crd", name)
		return nil
	case err != nil && !client.IsNotFound(err):
		return fmt.Errorf("reading CustomResourceDefinition %s: %w", name, err)
	}
	cs := schema.CRDSpec{
		Group: ti.group, Version: ti.version, Kind: ti.kind, Plural: ti.plural, Singular: ti.singular,
		ShortNames: ti.shortNames, Categories: ti.categories, Namespaced: ti.scope == "Namespaced",
		Labels:     map[string]string{keys.managedBy: labelValue(m.Name)},
		Deprecated: ti.deprecated, Conversion: spec.conversion,
	}
	for _, v := range spec.versions {
		cs.Versions = append(cs.Versions, schema.VersionSpec{Name: v.version, Type: v.goType, Deprecated: v.deprecated})
	}
	crd, err := schema.CRD(ti.goType, cs)
	if err != nil {
		return err
	}
	if err := m.client.Apply(ctx, path, m.Name, true, crd, nil); err != nil {
		return fmt.Errorf("installing CustomResourceDefinition %s: %w", name, err)
	}
	deadline := time.Now().Add(time.Minute)
	for {
		var got struct {
			Status struct {
				Conditions []Condition `json:"conditions"`
			} `json:"status"`
		}
		if err := m.client.Get(ctx, path, &got); err != nil {
			return err
		}
		if c := FindCondition(got.Status.Conditions, "Established"); c != nil && c.Status == True {
			break
		}
		if time.Now().After(deadline) {
			return fmt.Errorf("CustomResourceDefinition %s was not established after a minute", name)
		}
		select {
		case <-ctx.Done():
			return ctx.Err()
		case <-time.After(100 * time.Millisecond):
		}
	}
	m.log.Info("installed CustomResourceDefinition", "crd", name)
	return nil
}

// labelValue makes s a valid label value.
func labelValue(s string) string {
	s = strings.Map(func(r rune) rune {
		if r >= 'a' && r <= 'z' || r >= 'A' && r <= 'Z' || r >= '0' && r <= '9' || r == '-' || r == '_' || r == '.' {
			return r
		}
		return '-'
	}, s)
	if len(s) > 63 {
		s = s[:63]
	}
	return strings.Trim(s, "-_.")
}

// cache returns the cache for key, creating and starting it if needed.
func (m *Manager) cacheFor(key cacheKey, res resolved, ownerKey string, onCreate func(cache)) cache {
	m.mu.Lock()
	defer m.mu.Unlock()
	if c, ok := m.caches[key]; ok {
		return c
	}
	id := m.newID()
	c := key.ti.newCache(id, res, m.client, m.informerConfig(res, key.namespace, key.selector, ownerKey), m.log, m.metrics)
	c.onChange(func(old, new *ObjectMeta, initial bool) {
		if !initial {
			m.tracker.changed(id, old, new)
		}
	})
	if onCreate != nil {
		onCreate(c)
	}
	m.caches[key] = c
	done := make(chan struct{})
	m.cacheDone = append(m.cacheDone, done)
	go func() {
		defer close(done)
		c.run(m.runCtx)
	}()
	return c
}

// adopt registers a controller's primary informer as the shared cache for
// its type when it watches the same objects that Get and List would.
func (m *Manager) adopt(ti *typeInfo, res resolved, cfg informerConfig, inf cache) {
	key := cacheKey{ti: ti, namespace: m.informerConfig(res, m.Namespace, "", "").namespace}
	if cfg.namespace != key.namespace || cfg.selector != "" {
		return
	}
	m.mu.Lock()
	defer m.mu.Unlock()
	if _, ok := m.caches[key]; ok {
		return
	}
	id := inf.id()
	inf.onChange(func(old, new *ObjectMeta, initial bool) {
		if !initial {
			m.tracker.changed(id, old, new)
		}
	})
	m.caches[key] = inf
}

func (m *Manager) source(ctx context.Context, ti *typeInfo) (source, error) {
	res, err := m.resolve(ctx, ti)
	if err != nil {
		return nil, err
	}
	c := m.cacheFor(cacheKey{ti: ti, namespace: m.informerConfig(res, m.Namespace, "", "").namespace}, res, "", nil)
	return c, c.waitSynced(ctx)
}

func (m *Manager) existing(ti *typeInfo) source {
	m.mu.Lock()
	defer m.mu.Unlock()
	res, ok := m.resolved[ti]
	if !ok {
		return nil
	}
	if c, ok := m.caches[cacheKey{ti: ti, namespace: m.informerConfig(res, m.Namespace, "", "").namespace}]; ok {
		return c
	}
	return nil
}

func (m *Manager) children(ctx context.Context, c *core, ti *typeInfo) (source, error) {
	return m.childSource(ctx, c, ti, true)
}

// childSource returns the cache of ti objects that controller c owns. It
// selects them by the controller label, so it holds only those objects.
func (m *Manager) childSource(ctx context.Context, c *core, ti *typeInfo, wait bool) (source, error) {
	res, err := m.resolve(ctx, ti)
	if err != nil {
		return nil, err
	}
	key := cacheKey{ti: ti, namespace: m.informerConfig(res, m.Namespace, "", "").namespace, selector: c.labels.controller + "=" + c.name}
	src := m.cacheFor(key, res, c.labels.owner, func(cc cache) {
		cc.onChange(func(old, new *ObjectMeta, initial bool) {
			p := priorityFor(initial)
			for _, om := range []*ObjectMeta{old, new} {
				if om == nil {
					continue
				}
				if owner, ok := om.Annotations[c.labels.owner]; ok {
					c.enqueue(parseKey(owner), p)
				}
			}
		})
	})
	c.mu.Lock()
	if c.children == nil {
		c.children = map[*typeInfo]source{}
	}
	c.children[ti] = src
	c.mu.Unlock()
	if !wait {
		return src, nil
	}
	return src, src.waitSynced(ctx)
}

func (m *Manager) fetch(ctx context.Context, ti *typeInfo, k Key) (any, error) {
	res, err := m.resolve(ctx, ti)
	if err != nil {
		return nil, err
	}
	obj := reflect.New(ti.goType).Interface()
	if err := m.client.Get(ctx, res.path(k.Namespace, k.Name), obj); err != nil {
		if client.IsNotFound(err) {
			return nil, nil
		}
		return nil, err
	}
	o := obj.(interface{ object() *Object }).object()
	o.APIVersion, o.Kind = ti.apiVersion, ti.kind
	return obj, nil
}

func (m *Manager) deps() *tracker { return m.tracker }

func priorityFor(initial bool) queue.Priority {
	if initial {
		return queue.Low
	}
	return queue.High
}

func parseKey(s string) Key {
	if ns, name, ok := strings.Cut(s, "/"); ok {
		return Key{Namespace: ns, Name: name}
	}
	return Key{Name: s}
}
