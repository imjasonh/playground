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
	// webhooks and the handler passed to Serve.
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
	// DisableProtobuf makes caches read built-in types as JSON. By default
	// they read protobuf, which the API server encodes faster, when every
	// field the Go type declares is in the framework's schema of built-in
	// types; other types, and every custom type, are read as JSON.
	DisableProtobuf bool
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
	// ServeAddr is where the manager serves the handler passed to Serve,
	// over plain HTTP. It defaults to ":8081".
	ServeAddr string
	// TokenDir is a directory of service account tokens for RequestToken,
	// each in a file named by the hex SHA-256 hash of its audience. The
	// generate command mounts the program's tokens there from a projected
	// volume, whose tokens the kubelet renews.
	TokenDir string

	client  *client.Client
	log     *slog.Logger
	metrics *metrics
	events  *eventWriter
	tracker *tracker
	ids     atomic.Int64
	runCtx  context.Context
	started atomic.Bool
	sharder *sharder
	// self is the user that the program authenticates as, once known.
	self atomic.Pointer[UserInfo]

	mu          sync.Mutex
	caches      map[cacheKey]cache
	unshared    []cache // primary informers that aren't in caches
	cacheDone   []chan struct{}
	resolved    map[*typeInfo]resolved
	crdCalls    map[*typeInfo]*crdCall
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
// -webhook-addr, -webhook-service, -webhook-url, -serve-addr, -token-dir,
// and -v for debug logs.
//
// Run as "PROGRAM generate -registry=REGISTRY", from the program's module,
// Main instead builds the program into an image on Chainguard's static
// base image, pushes it to REGISTRY, and writes YAML for kubectl apply that
// installs it: a namespace, a service account, RBAC rules for the types and
// APIs the program uses, a Deployment, and a Service for its webhooks and
// its Serve handler.
func Main(controllers ...Controller) {
	if len(os.Args) > 1 && os.Args[1] == "generate" {
		ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
		err := generate(ctx, os.Args[2:], controllers, os.Stdout, os.Stderr)
		stop()
		switch {
		case errors.Is(err, flag.ErrHelp):
		case err != nil:
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
		return
	}
	m := &Manager{}
	flag.Usage = func() {
		name := filepath.Base(os.Args[0])
		fmt.Fprintf(flag.CommandLine.Output(), "Usage: %s [flags]\n       %s generate -registry=REGISTRY [flags] | kubectl apply -f -\n\nFlags:\n", name, name)
		flag.PrintDefaults()
	}
	verbose := m.flags(flag.CommandLine)
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

// flags defines Main's flags on fs, and returns the value of -v.
func (m *Manager) flags(fs *flag.FlagSet) *bool {
	fs.StringVar(&m.Kubeconfig, "kubeconfig", "", "path to a kubeconfig file")
	fs.StringVar(&m.Namespace, "namespace", "", "watch only this namespace")
	fs.BoolVar(&m.LeaderElection, "leader-elect", false, "reconcile only while holding a Lease")
	fs.IntVar(&m.Shards, "shards", 1, "split reconciles across replicas in this many shards, each held through a Lease")
	fs.StringVar(&m.Addr, "addr", "", "address for /healthz, /readyz, and /metrics, for example :8080")
	fs.StringVar(&m.WebhookAddr, "webhook-addr", "", "address for HTTPS webhooks (default :9443)")
	fs.StringVar(&m.WebhookService, "webhook-service", "", "Service, as name or namespace/name, through which the API server reaches the webhooks")
	fs.StringVar(&m.WebhookURL, "webhook-url", "", "base https URL through which the API server reaches the webhooks, outside the cluster")
	fs.StringVar(&m.ServeAddr, "serve-addr", "", "address for the HTTP handler passed to kube.Serve (default :8081)")
	fs.StringVar(&m.TokenDir, "token-dir", "", "directory of service account tokens for kube.RequestToken, by audience")
	return fs.Bool("v", false, "log debug messages")
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
	m.events = newEventWriter(m.client, m.log, m.metrics)
	m.tracker = newTracker()
	m.caches = map[cacheKey]cache{}
	m.resolved = map[*typeInfo]resolved{}
	m.crdCalls = map[*typeInfo]*crdCall{}
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
	parent := ctx
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
	// startFailed reports a failure to start. If the caller stopped the
	// manager meanwhile, it stops cleanly. If a server failed, which
	// canceled ctx and so made this step fail, it reports the server's
	// error.
	startFailed := func(err error) error {
		switch {
		case parent.Err() != nil:
			return nil
		case ctx.Err() != nil:
			return context.Cause(ctx)
		}
		return err
	}
	if m.Addr != "" {
		srv, err := m.serve()
		if err != nil {
			return err
		}
		stops = append(stops, func() { srv.Close() })
	}
	stops = append(stops, m.waitForCaches, m.events.start())
	for _, c := range controllers {
		if err := c.prepare(ctx, m); err != nil {
			return startFailed(err)
		}
	}
	if m.needsWebhooks() {
		if err := m.hooks.start(ctx); err != nil {
			return startFailed(err)
		}
		stops = append(stops, m.hooks.stop)
	} else if err := (&webhookServer{m: m}).applyConfigurations(ctx); err != nil {
		// An earlier version of the program may have left webhook
		// configurations whose webhooks no longer answer.
		m.log.Warn("removing stale webhook configurations failed", "err", err)
	}
	var reconcilers, others []Controller
	for _, c := range controllers {
		if c.reconciles() {
			reconcilers = append(reconcilers, c)
		} else {
			others = append(others, c)
		}
	}
	var servers sync.WaitGroup
	stops = append(stops, servers.Wait)
	for _, c := range others {
		servers.Go(func() {
			if err := c.run(ctx); err != nil {
				cancel(fmt.Errorf("%s: %w", c.controllerName(), err))
			}
		})
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
		// Reconcilers install their CustomResourceDefinitions in setup, and
		// the objects that Install applies may need them.
		for _, c := range slices.Concat(reconcilers, others) {
			if err := c.setup(ctx, m); err != nil {
				return startFailed(err)
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
	if parent.Err() != nil {
		// The caller stopped the manager, perhaps with a cause, such as the
		// signal that signal.NotifyContext received.
		return nil
	}
	return context.Cause(ctx)
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
	// A standby replica is ready once its webhooks and Serve handler serve:
	// the Service must send their requests to it, though it doesn't
	// reconcile.
	mux.HandleFunc("/readyz", func(w http.ResponseWriter, r *http.Request) {
		m.mu.Lock()
		hooks := m.hooks
		m.mu.Unlock()
		if !hooks.serving() {
			http.Error(w, "webhooks are not serving", http.StatusServiceUnavailable)
			return
		}
		for _, c := range m.controllers {
			if !c.reconciles() && !c.synced() {
				http.Error(w, c.controllerName()+" is not serving", http.StatusServiceUnavailable)
				return
			}
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
		protobuf:  !m.DisableProtobuf,
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

// crdCall is one run of ensureCRD for a type. The caller that runs it sets
// err and ctxErr, and then closes done.
type crdCall struct {
	done   chan struct{}
	err    error
	ctxErr error // the error of the caller's context, if the call failed
}

// ensureCRD creates the CustomResourceDefinition of a type that the program
// defines and owns but doesn't reconcile, if it's missing. Concurrent callers
// for a type wait for the first one and share its result. If the first one
// fails after its context ends, a waiter whose context is live takes its
// place. ensureCRD doesn't keep a failure, so the next caller tries again.
func (m *Manager) ensureCRD(ctx context.Context, ti *typeInfo) error {
	if !ti.custom {
		return nil
	}
	for {
		m.mu.Lock()
		call, ok := m.crdCalls[ti]
		if !ok {
			call = &crdCall{done: make(chan struct{})}
			m.crdCalls[ti] = call
		}
		m.mu.Unlock()
		if !ok {
			return m.runCRDCall(ctx, ti, call)
		}
		select {
		case <-call.done:
		case <-ctx.Done():
			return ctx.Err()
		}
		if call.ctxErr == nil || ctx.Err() != nil {
			return call.err
		}
	}
}

// runCRDCall runs call, the entry for ti in m.crdCalls. If the call fails or
// panics, runCRDCall removes the entry before it closes call.done, so that a
// waiter that tries again never finds the finished call.
func (m *Manager) runCRDCall(ctx context.Context, ti *typeInfo, call *crdCall) error {
	finished := false
	defer func() {
		if !finished {
			call.err = fmt.Errorf("creating CustomResourceDefinition %s panicked", crdSpec{ti: ti}.name())
		}
		if call.err != nil {
			call.ctxErr = ctx.Err()
			m.mu.Lock()
			delete(m.crdCalls, ti)
			m.mu.Unlock()
		}
		close(call.done)
	}()
	if !m.reconciled(ti) {
		call.err = m.createCRD(ctx, ti)
	}
	finished = true
	return call.err
}

// reconciled reports whether a controller in the program reconciles ti's
// type, and so installs the type's CustomResourceDefinition.
func (m *Manager) reconciled(ti *typeInfo) bool {
	return slices.ContainsFunc(m.controllers, func(c Controller) bool {
		d, err := c.describe()
		return err == nil && d.reconciles && d.ti.custom && d.ti.group == ti.group && d.ti.plural == ti.plural
	})
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

// adopt returns the cache that a controller with the primary informer inf
// reads. If inf watches the same objects that Get and List would, that's the
// shared cache for its type: the one that already exists, or else inf, which
// adopt registers as that cache. Otherwise adopt registers inf as an unshared
// cache, so that the process's writes show in it.
func (m *Manager) adopt(ti *typeInfo, res resolved, cfg informerConfig, inf cache) cache {
	key := cacheKey{ti: ti, namespace: m.informerConfig(res, m.Namespace, "", "").namespace}
	m.mu.Lock()
	defer m.mu.Unlock()
	if cfg.namespace != key.namespace || cfg.selector != "" {
		m.unshared = append(m.unshared, inf)
		return inf
	}
	if c, ok := m.caches[key]; ok {
		return c
	}
	id := inf.id()
	inf.onChange(func(old, new *ObjectMeta, initial bool) {
		if !initial {
			m.tracker.changed(id, old, new)
		}
	})
	m.caches[key] = inf
	return inf
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
	if err := m.ensureCRD(ctx, ti); err != nil {
		return nil, err
	}
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
