package kube

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"hash/fnv"
	"log/slog"
	"maps"
	"math/rand/v2"
	"net/url"
	"reflect"
	"regexp"
	"runtime/debug"
	"slices"
	"strconv"
	"strings"
	"sync"
	"time"

	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/clone"
	"github.com/imjasonh/playground/kube/internal/queue"
	"github.com/imjasonh/playground/kube/internal/subset"
)

// Reconciler is the one interface a controller implements. Reconcile looks
// at obj, the desired state, and at the real state through Get, List, and
// Fetch, then declares what should exist with Own and Apply. It can also act
// on systems outside Kubernetes directly.
//
// The framework calls Reconcile whenever obj or anything Reconcile read
// changes, and retries with backoff when it returns an error. Calls for the
// same object never overlap. Changes that Reconcile makes to obj's status are
// written back to the cluster; other changes to obj are ignored.
type Reconciler[T any] interface {
	Reconcile(ctx context.Context, obj *T) error
}

// Finalizer is implemented by reconcilers that must clean up outside
// Kubernetes before an object goes away, for example deleting a cloud
// resource. When a reconciler implements it, the framework adds a finalizer to
// each object before the first Reconcile, calls Finalize when the object is
// deleted, and removes the finalizer once Finalize returns nil. Objects that
// the deleted object owns are cleaned up without it. After you remove
// Finalize from a reconciler, pass RemovesFinalizer to For until no object
// carries the finalizer.
type Finalizer[T any] interface {
	Finalize(ctx context.Context, obj *T) error
}

// Controller is a reconciler configured to run in a Manager. Create one
// with For, with Webhooks for admission webhooks alone, with Install for
// objects to install, or with Volume for a persistent volume.
type Controller interface {
	// prepare runs on every replica before leader election. It checks the
	// controller and registers its webhooks.
	prepare(ctx context.Context, m *Manager) error
	// setup and run start the reconcile loop, on a replica that holds the
	// lease. Install's controller applies its objects in setup. For a
	// controller that doesn't reconcile, the manager also calls run on every
	// replica, before it waits for the lease.
	setup(ctx context.Context, m *Manager) error
	run(ctx context.Context) error
	reconciles() bool
	controllerName() string
	synced() bool
	// describe reports what the controller declares, without a cluster.
	describe() (declared, error)
}

// declared is what a controller says about the API it uses before it
// runs. The generate command turns it into RBAC rules.
type declared struct {
	ti         *typeInfo
	reconciles bool
	// finalizes is set when the reconciler has a Finalize method, or when
	// objects can carry a finalizer that an earlier version of the program
	// added.
	finalizes bool
	// webhooks is set when the controller serves admission or conversion
	// webhooks.
	webhooks bool
	// versioned is set when the type has more than one version, so the
	// framework migrates stored objects in every namespace.
	versioned bool
	owns      []*typeInfo
	// serves is set when the controller serves HTTP for Serve.
	serves bool
	// installs are the objects that the controller applies when the
	// program starts.
	installs []installObject
	// volume is the directory of the persistent volume that Volume
	// declares.
	volume string
}

func (c *controller[T, P]) describe() (declared, error) {
	ti, err := typeInfoFor[T, P]()
	if err != nil {
		return declared{}, err
	}
	d := declared{ti: ti, reconciles: true}
	d.finalizes = c.fin != nil || c.opts.finalizes
	_, validates := c.r.(Validator[T])
	_, defaults := c.r.(Defaulter[T])
	d.webhooks = validates || defaults
	d.versioned = len(c.opts.versions) > 0
	for _, vo := range c.opts.versions {
		if _, ok := vo.newObj().(converter[T]); ok {
			d.webhooks = true
		}
	}
	for _, own := range c.opts.owns {
		oti, err := own()
		if err != nil {
			return declared{}, err
		}
		d.owns = append(d.owns, oti)
	}
	for _, t := range append([]*typeInfo{ti}, d.owns...) {
		if t.local {
			return declared{}, fmt.Errorf("kube: %v is local, so a controller can't reconcile or own it", t)
		}
	}
	return d, nil
}

// Option configures a controller.
type Option func(*options)

type options struct {
	name      string
	workers   int
	namespace string
	selector  string
	resync    time.Duration
	owns      []func() (*typeInfo, error)
	finalizes bool
	versions  []versionOption
}

// Named sets the controller's name. The name is the value of ControllerLabel
// on the objects that the controller owns, the end of its finalizer (see
// FinalizerName), and its field manager for server-side apply. It also
// appears in logs, metrics, and events. Two controllers that reconcile or own
// the same type in a cluster need different names, or they remove each
// other's finalizers and delete each other's objects. Run fails when two
// controllers in one program have the same name.
//
// The name defaults to the program's name (Manager.Name) and the lowercase
// kind, joined by '-', such as "shop-website" for a program named shop that
// reconciles Websites. When the program has the kind's name, the default is
// only the kind, such as "website". A default longer than 50 characters is
// shortened and ends in a hash. Objects in clusters carry the name, so set
// one to keep it when you rename the program. A name has at most 50
// lowercase letters, digits, '-', and '.', and starts and ends with a letter
// or digit. Run fails with any other name.
func Named(name string) Option { return func(o *options) { o.name = name } }

// Workers sets how many objects the controller reconciles at once. The
// default is 4. The framework never reconciles one object concurrently.
func Workers(n int) Option { return func(o *options) { o.workers = n } }

// WatchNamespace limits the controller to objects in one namespace.
func WatchNamespace(namespace string) Option { return func(o *options) { o.namespace = namespace } }

// WatchSelector limits the controller to objects that match a label
// selector. The API server applies the selector, so other objects are never
// sent or cached. Don't combine it with a Finalizer: an object whose labels
// stop matching looks deleted, and its finalizer is never removed.
func WatchSelector(selector string) Option { return func(o *options) { o.selector = selector } }

// Resync reconciles every object again at this interval, at low priority,
// even if nothing changed. The default is 10 hours. Zero disables it.
func Resync(d time.Duration) Option { return func(o *options) { o.resync = d } }

// Owns declares up front that the controller owns objects of type T. The
// framework learns owned types from calls to Own, so this is only needed to
// delete owned objects of a type that no reconcile declares anymore, for
// example after a code change, and to start that cache before the first
// reconcile. If the program defines T but doesn't reconcile it, starting the
// cache also creates T's CustomResourceDefinition if it's missing, so use
// Owns when a reconcile calls Get or List for T before it first owns an
// object of type T. If creating the CustomResourceDefinition fails at
// startup, the program logs the error and starts anyway, and the next Own of
// T tries again.
func Owns[T any, P Resource[T]]() Option {
	return func(o *options) { o.owns = append(o.owns, typeInfoFor[T, P]) }
}

// RemovesFinalizer declares that objects can carry the controller's
// finalizer from an earlier version of the program, for example one whose
// reconciler had a Finalize method. The framework removes a finalizer that
// the controller no longer needs, which takes permission to patch the
// object, so the generate command grants patch on the reconciled type for
// this option. When no object carries the finalizer anymore, remove the
// option.
func RemovesFinalizer() Option { return func(o *options) { o.finalizes = true } }

// For returns a controller that reconciles objects of type T with r.
func For[T any, P Resource[T]](r Reconciler[T], opts ...Option) Controller {
	c := &controller[T, P]{r: r, opts: options{workers: 4, resync: 10 * time.Hour}}
	if f, ok := r.(Finalizer[T]); ok {
		c.fin = f
	}
	for _, o := range opts {
		o(&c.opts)
	}
	return c
}

// core is the part of a controller that doesn't depend on its type.
type core struct {
	name      string
	ti        *typeInfo
	res       resolved
	q         *queue.Queue[Key]
	finalizer string
	labels    labelKeys
	log       *slog.Logger
	// sh decides which keys this replica reconciles, or is nil when it
	// reconciles every key.
	sh *sharder

	mu       sync.Mutex
	children map[*typeInfo]source
	// applied holds, for each reconciled object, hashes of the documents
	// that its last successful reconcile applied.
	applied map[Key]map[appliedKey]uint64
	// statuses holds a hash of each object's status as this controller last
	// wrote or confirmed it, to tell its own status writes from others'.
	statuses map[Key]uint64
	// statusApplies holds a hash of the status that this controller last
	// applied to each object.
	statusApplies map[Key]uint64
	// caughtUp holds, for each object, the tenure of its shard in which a
	// write to the object that required the cached resource version succeeded.
	caughtUp map[Key]uint64
	// errs holds the error that each object's last reconcile failed with.
	errs map[Key]error
}

type appliedKey struct {
	ti     *typeInfo
	key    Key
	status bool
}

// labelKeys are the label and annotation keys the framework uses.
type labelKeys struct {
	controller string // label: controller name, on owned objects
	ownerUID   string // label: owner UID, on owned objects
	owner      string // annotation: owner namespace/name, on owned objects
	applied    string // annotation: hash of the last applied body, on owned objects
	cleanup    string // annotation: owned kinds to delete on finalize, on owners
	managedBy  string // label: on objects the framework installs for itself
	leaseGroup string // label: the manager whose shard and membership Leases these are
	leaseRole  string // label: shard or member
}

func newLabelKeys() labelKeys {
	return labelKeys{
		controller: ControllerLabel,
		ownerUID:   OwnerUIDLabel,
		owner:      OwnerAnnotation,
		applied:    Domain + "/applied",
		cleanup:    Domain + "/cleanup",
		managedBy:  Domain + "/managed-by",
		leaseGroup: Domain + "/lease-group",
		leaseRole:  Domain + "/lease-role",
	}
}

// enqueue adds k to the queue if this replica reconciles it. A replica that
// acquires a shard later enqueues its keys then.
func (c *core) enqueue(k Key, p queue.Priority) {
	if c.q != nil && c.sh.owns(k) {
		c.q.Add(k, p)
	}
}

func (c *core) childSources() map[*typeInfo]source {
	c.mu.Lock()
	defer c.mu.Unlock()
	return maps.Clone(c.children)
}

func (c *core) lastApplied(parent Key, k appliedKey) (uint64, bool) {
	c.mu.Lock()
	defer c.mu.Unlock()
	h, ok := c.applied[parent][k]
	return h, ok
}

func (c *core) setApplied(parent Key, m map[appliedKey]uint64) {
	c.mu.Lock()
	defer c.mu.Unlock()
	if c.applied == nil {
		c.applied = map[Key]map[appliedKey]uint64{}
	}
	if len(m) == 0 {
		delete(c.applied, parent)
		return
	}
	c.applied[parent] = m
}

func (c *core) lastStatus(k Key) (uint64, bool) {
	c.mu.Lock()
	defer c.mu.Unlock()
	h, ok := c.statuses[k]
	return h, ok
}

// setStatus records h as the hash of k's status. If ok is false, it forgets
// k's status, the status that this controller last applied to k, and
// whether k's cache caught up.
func (c *core) setStatus(k Key, h uint64, ok bool) {
	c.mu.Lock()
	defer c.mu.Unlock()
	if !ok {
		delete(c.statuses, k)
		delete(c.statusApplies, k)
		delete(c.caughtUp, k)
		return
	}
	if c.statuses == nil {
		c.statuses = map[Key]uint64{}
	}
	c.statuses[k] = h
}

func (c *core) lastStatusApply(k Key) (uint64, bool) {
	c.mu.Lock()
	defer c.mu.Unlock()
	h, ok := c.statusApplies[k]
	return h, ok
}

func (c *core) setStatusApply(k Key, h uint64) {
	c.mu.Lock()
	defer c.mu.Unlock()
	if c.statusApplies == nil {
		c.statusApplies = map[Key]uint64{}
	}
	c.statusApplies[k] = h
}

// hasCaughtUp reports whether a write to k that required the cached resource
// version succeeded during tenure.
func (c *core) hasCaughtUp(k Key, tenure uint64) bool {
	c.mu.Lock()
	defer c.mu.Unlock()
	t, ok := c.caughtUp[k]
	return ok && t == tenure
}

func (c *core) setCaughtUp(k Key, tenure uint64) {
	c.mu.Lock()
	defer c.mu.Unlock()
	if c.caughtUp == nil {
		c.caughtUp = map[Key]uint64{}
	}
	c.caughtUp[k] = tenure
}

func (c *core) lastError(k Key) error {
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.errs[k]
}

// forgetErrors forgets the last reconcile error of each key that in matches,
// including keys whose objects were deleted after the reconcile failed.
func (c *core) forgetErrors(in func(Key) bool) {
	c.mu.Lock()
	defer c.mu.Unlock()
	for k := range c.errs {
		if in(k) {
			delete(c.errs, k)
		}
	}
}

func (c *core) setLastError(k Key, err error) {
	c.mu.Lock()
	defer c.mu.Unlock()
	if err == nil {
		delete(c.errs, k)
		return
	}
	if c.errs == nil {
		c.errs = map[Key]error{}
	}
	c.errs[k] = err
}

type controller[T any, P Resource[T]] struct {
	core
	r       Reconciler[T]
	fin     Finalizer[T]
	opts    options
	m       *Manager
	primary *informer[T, P]
	// borrowed is set when primary is a cache that something else started
	// and runs, such as the cache that Get reads.
	borrowed bool
	// versions are the type's other served versions. conversion is set
	// when any of them converts itself, through a webhook.
	versions   []servedVersion
	conversion bool
}

var nameRE = regexp.MustCompile(`^[a-z0-9]([-a-z0-9.]{0,48}[a-z0-9])?$`)

// defaultName is the name of a controller without the Named option: the
// program's name and the kind, lowercase and joined by '-', or only the kind
// when the program has the kind's name. To fit nameRE, a longer name keeps
// its first 41 characters and adds '-' and a hash of the whole name.
func defaultName(program, kind string) string {
	kind = strings.ToLower(kind)
	p := strings.Trim(strings.Map(func(r rune) rune {
		switch {
		case r >= 'a' && r <= 'z', r >= '0' && r <= '9', r == '-', r == '.':
			return r
		case r >= 'A' && r <= 'Z':
			return r - 'A' + 'a'
		}
		return '-'
	}, program), "-.")
	if p == "" || p == kind {
		return kind
	}
	name := p + "-" + kind
	if len(name) <= 50 {
		return name
	}
	h := fnv.New32a()
	h.Write([]byte(name))
	return fmt.Sprintf("%s-%08x", strings.TrimRight(name[:41], "-."), h.Sum32())
}

func (c *controller[T, P]) controllerName() string { return c.name }

func (c *controller[T, P]) synced() bool { return c.primary != nil && c.primary.hasSynced.Load() }

func (c *controller[T, P]) reconciles() bool { return true }

func (c *controller[T, P]) prepare(ctx context.Context, m *Manager) error {
	ti, err := typeInfoFor[T, P]()
	if err != nil {
		return err
	}
	c.ti, c.m = ti, m
	c.name = c.opts.name
	if c.name == "" {
		c.name = defaultName(m.Name, ti.kind)
	}
	if !nameRE.MatchString(c.name) {
		return fmt.Errorf("kube: controller name %q must be at most 50 lowercase letters, digits, '-', or '.', and start and end with a letter or digit", c.name)
	}
	for _, o := range m.controllers {
		if o == Controller(c) {
			break
		}
		if o.reconciles() && o.controllerName() == c.name {
			return fmt.Errorf("kube: two controllers are named %q; give the one for %v another name with kube.Named", c.name, ti)
		}
	}
	c.labels = newLabelKeys()
	c.finalizer = FinalizerName(c.name)
	c.log = m.log.With("controller", c.name)
	if err := c.prepareVersions(m); err != nil {
		return err
	}
	v, _ := c.r.(Validator[T])
	d, _ := c.r.(Defaulter[T])
	return registerAdmission[T, P](ctx, m, ti, v, d)
}

func (c *controller[T, P]) setup(ctx context.Context, m *Manager) error {
	ti := c.ti
	var err error
	if c.res, err = m.ensureType(ctx, c.crd()); err != nil {
		return fmt.Errorf("controller %s: %w", c.name, err)
	}
	ns := m.Namespace
	if c.opts.namespace != "" {
		ns = c.opts.namespace
	}
	c.q = queue.New[Key](queue.Options{})
	c.sh = m.sharder
	cfg := m.informerConfig(c.res, ns, c.opts.selector, "")
	c.primary = newInformer[T, P](m.newID(), ti, c.res, m.client, cfg, m.log, m.metrics)
	// A handler or webhook that read the type before the controller
	// started, or another controller of the type, may have started a cache
	// of the same objects. Two caches of them see each write at different
	// times, so the controller reads that one.
	if shared, ok := m.adopt(ti, c.res, cfg, c.primary).(*informer[T, P]); ok && shared != c.primary {
		c.primary, c.borrowed = shared, true
	}
	// Another replica may have reconciled a shard's keys since this one
	// last held it, so forget what this replica last wrote for them, and
	// how its last reconciles of them failed.
	c.sh.onAcquire(func(i int) {
		c.forgetErrors(func(k Key) bool { return c.sh.shardOf(k) == i })
		c.primary.store.each("", func(o *T) bool {
			if k := metaOf[T, P](o).Key(); c.sh.shardOf(k) == i {
				c.setApplied(k, nil)
				c.setStatus(k, 0, false)
				c.q.Add(k, queue.Low)
			}
			return true
		})
	})
	c.primary.addHandler(c.onPrimary)
	if c.borrowed {
		// A cache that has synced doesn't notify a new handler of the
		// objects it already holds.
		c.primary.store.each("", func(o *T) bool {
			c.enqueue(metaOf[T, P](o).Key(), queue.Low)
			return true
		})
	}
	for _, own := range c.opts.owns {
		oti, err := own()
		if err != nil {
			return err
		}
		if err := m.ensureCRD(ctx, oti); err != nil {
			c.log.Warn("creating the CustomResourceDefinition of an owned type failed; Own tries again", "type", oti.String(), "err", err)
		}
		if _, err := m.childSource(ctx, &c.core, oti, false); err != nil {
			return fmt.Errorf("controller %s: %w", c.name, err)
		}
	}
	m.metrics.gauge("kube_queue_depth", "Keys waiting to be reconciled.", func() []sample {
		high, low := c.q.Len()
		return []sample{
			{labels: []string{"controller", c.name, "priority", "high"}, value: float64(high)},
			{labels: []string{"controller", c.name, "priority", "low"}, value: float64(low)},
			{labels: []string{"controller", c.name, "priority", "scheduled"}, value: float64(c.q.Waiting())},
		}
	})
	return nil
}

func (c *controller[T, P]) run(ctx context.Context) error {
	if !c.borrowed {
		informed := make(chan struct{})
		go func() {
			defer close(informed)
			c.primary.run(ctx)
		}()
		defer func() { <-informed }()
	}
	select {
	case <-c.primary.synced:
	case <-ctx.Done():
		c.q.ShutDown()
		return nil
	}
	c.log.Info("started", "type", c.ti.String(), "objects", c.primary.store.len(), "workers", c.opts.workers)
	var wg sync.WaitGroup
	for range c.opts.workers {
		wg.Go(func() {
			for {
				key, ok := c.q.Get()
				if !ok {
					return
				}
				if i, mine := c.sh.begin(key); mine {
					c.process(ctx, key)
					c.sh.end(i)
				} else {
					c.q.Forget(key)
				}
				c.q.Done(key)
			}
		})
	}
	if c.opts.resync > 0 {
		wg.Go(func() { c.resyncLoop(ctx) })
	}
	if c.ti.custom {
		wg.Go(func() { c.maintainCRD(ctx) })
	}
	<-ctx.Done()
	c.q.ShutDown()
	wg.Wait()
	return nil
}

func (c *controller[T, P]) resyncLoop(ctx context.Context) {
	for {
		t := time.NewTimer(c.opts.resync + time.Duration(float64(c.opts.resync)*0.1*rand.Float64())) // #nosec G404 -- jitter needs no cryptographic randomness.
		select {
		case <-ctx.Done():
			t.Stop()
			return
		case <-t.C:
		}
		c.primary.store.each("", func(o *T) bool {
			c.enqueue(metaOf[T, P](o).Key(), queue.Low)
			return true
		})
	}
}

// onPrimary enqueues changed objects. It ignores changes to only the resource
// version, and status changes that this controller made.
func (c *controller[T, P]) onPrimary(old, new *T, initial bool) {
	p := queue.High
	if initial {
		p = queue.Low
	}
	switch {
	case new == nil:
		// Reconciling a deleted object forgets what this replica recorded
		// for it, but this replica doesn't reconcile objects in shards that
		// it doesn't hold.
		k := metaOf[T, P](old).Key()
		c.m.tracker.forget(ref{c: &c.core, key: k})
		c.setApplied(k, nil)
		c.setStatus(k, 0, false)
		c.enqueue(k, queue.High)
	case old == nil || c.specChanged(old, new) || c.statusChanged(old, new):
		c.enqueue(metaOf[T, P](new).Key(), p)
	}
}

// statusChanged reports whether something other than this controller changed
// the status, for example a person who cleared it. Reconciling then writes the
// status back.
func (c *controller[T, P]) statusChanged(old, new *T) bool {
	if c.ti.status == nil {
		return false
	}
	ns := reflect.ValueOf(new).Elem().FieldByIndex(c.ti.status).Interface()
	if reflect.DeepEqual(reflect.ValueOf(old).Elem().FieldByIndex(c.ti.status).Interface(), ns) {
		return false
	}
	b, err := json.Marshal(ns)
	if err != nil {
		return true
	}
	h, ok := c.lastStatus(metaOf[T, P](new).Key())
	return !ok || h != hashJSON(b)
}

// specChanged reports whether a field that the type declares changed,
// ignoring status and resourceVersion. A metadata-only type can't see the
// fields that matter (often its reconciler fetches them), so for those types
// every new resource version counts.
func (c *controller[T, P]) specChanged(old, new *T) bool {
	if c.ti.metadataOnly {
		return metaOf[T, P](old).ResourceVersion != metaOf[T, P](new).ResourceVersion
	}
	a, b := *old, *new
	ma, mb := metaOf[T, P](&a), metaOf[T, P](&b)
	ma.ResourceVersion, mb.ResourceVersion = "", ""
	if c.ti.status != nil {
		for _, v := range []reflect.Value{reflect.ValueOf(&a), reflect.ValueOf(&b)} {
			f := v.Elem().FieldByIndex(c.ti.status)
			f.SetZero()
		}
	}
	return !reflect.DeepEqual(a, b)
}

func (c *controller[T, P]) process(ctx context.Context, key Key) {
	start := time.Now()
	requeue, err := c.reconcileKey(ctx, key)
	// The retry of a stale reconcile redoes it from a newer copy of the
	// object, so LastError keeps returning the error from before it.
	if !errors.Is(err, errStale) {
		c.setLastError(key, err)
	}
	elapsed := time.Since(start)
	result := "success"
	log := c.log.With("key", key.String(), "duration", elapsed.Round(time.Microsecond))
	switch {
	case err == nil:
		c.q.Forget(key)
		if requeue > 0 {
			c.q.AddAfter(key, queue.Low, requeue)
		}
		log.Debug("reconciled", "requeueAfter", requeue)
	case ctx.Err() != nil:
		return
	case IsPermanent(err):
		c.q.Forget(key)
		result = "permanent_error"
		log.Warn("reconcile failed; waiting for the object to change", "err", err)
	case errors.Is(err, errStale):
		d := c.q.Retry(key, queue.High)
		result = "stale"
		// A cache catches up within a few retries. More can mean that
		// something else, such as a webhook, refuses the writes with 409
		// Conflict, which no retry fixes.
		level, failures := slog.LevelInfo, c.q.Failures(key)
		if failures > 5 {
			level = slog.LevelWarn
		}
		log.Log(ctx, level, "reconcile worked from an out-of-date object; retrying", "err", err, "retry", d.Round(time.Millisecond), "failures", failures)
	default:
		d := c.q.Retry(key, queue.High)
		result = "error"
		log.Warn("reconcile failed; retrying", "err", err, "retry", d.Round(time.Millisecond), "failures", c.q.Failures(key))
	}
	c.m.metrics.inc("kube_reconcile_total", "controller", c.name, "result", result)
	c.m.metrics.observe("kube_reconcile_duration_seconds", elapsed.Seconds(), "controller", c.name)
}

func (c *controller[T, P]) reconcileKey(ctx context.Context, key Key) (time.Duration, error) {
	cached := c.primary.store.get(key)
	if cached == nil {
		c.m.tracker.forget(ref{c: &c.core, key: key})
		c.setApplied(key, nil)
		c.setStatus(key, 0, false)
		return 0, nil
	}
	obj := clone.Of(cached)
	m := metaOf[T, P](obj)
	pre := c.precondition(key, cached)
	// A write to the object that required the cached resource version and
	// succeeded shows that the cache had caught up, as a status write would,
	// and the status may need no write.
	defer func(orig string) {
		if pre.rv != orig && !pre.diverged {
			c.setCaughtUp(key, pre.tenure)
		}
	}(pre.rv)
	if m.Deleting() {
		if !slices.Contains(m.Finalizers, c.finalizer) {
			return 0, nil
		}
		return c.finalize(ctx, key, cached, obj, pre)
	}
	if c.fin != nil && !slices.Contains(m.Finalizers, c.finalizer) {
		if err := c.setFinalizer(ctx, obj, true, m.Annotations[c.labels.cleanup], &pre.rv); err != nil {
			return 0, fmt.Errorf("adding finalizer: %w", err)
		}
	}
	rctx, s := newScope(ctx, c.m, &c.core, key)
	defer s.cancel(nil)
	defer c.m.events.send(&c.core, metaOf[T, P](cached), "Reconcile", s)
	err := c.call(rctx, func(ctx context.Context) error { return c.r.Reconcile(ctx, obj) })
	if s.err != nil {
		err = s.err
	}
	if err == nil {
		// execute may have applied some documents before it failed, and the
		// records don't show them, so the next reconcile sends every one.
		if err = c.execute(ctx, key, obj, s, &pre.rv); err != nil {
			c.setApplied(key, nil)
		}
	}
	c.m.tracker.retain(ref{c: &c.core, key: key}, s.deps)
	if serr := c.writeStatus(ctx, cached, obj, err, pre); serr != nil {
		switch {
		case err == nil:
			err = fmt.Errorf("writing status: %w", serr)
		case !errors.Is(serr, errStale):
			c.log.Warn("writing status failed", "key", key.String(), "err", serr)
		}
	}
	return s.requeue, err
}

// call runs fn and turns a panic into an error, so one bad object can't
// crash the controller.
func (c *controller[T, P]) call(ctx context.Context, fn func(context.Context) error) (err error) {
	defer func() {
		if r := recover(); r != nil {
			c.log.Error("reconcile panicked", "panic", r, "stack", string(debug.Stack()))
			err = fmt.Errorf("panic: %v", r)
		}
	}()
	return fn(ctx)
}

// execute carries out a successful reconcile's intents, then deletes owned
// objects that the reconcile no longer declared. Writes to parent carry the
// resource version that rv points to, as setFinalizer describes.
func (c *controller[T, P]) execute(ctx context.Context, key Key, parent *T, s *scope, rv *string) error {
	pm := metaOf[T, P](parent)
	var cleanup []string
	for _, in := range s.intents {
		if in.kind == intentOwn && !c.canReference(in, pm) {
			if k := in.ti.apiVersion + "/" + in.ti.kind; !slices.Contains(cleanup, k) {
				cleanup = append(cleanup, k)
			}
		}
	}
	if len(cleanup) > 0 {
		have := splitList(pm.Annotations[c.labels.cleanup])
		want := slices.Sorted(maps.Keys(setOf(append(have, cleanup...))))
		if !slices.Contains(pm.Finalizers, c.finalizer) || !slices.Equal(have, want) {
			if err := c.setFinalizer(ctx, parent, true, strings.Join(want, ","), rv); err != nil {
				return fmt.Errorf("adding finalizer before creating objects that garbage collection can't delete: %w", err)
			}
		}
	}

	applied := map[appliedKey]uint64{}
	declared := map[*typeInfo]map[Key]bool{}
	for _, in := range s.intents {
		m := metaOfAny(in.obj)
		switch in.kind {
		case intentOwn, intentApply:
			body, err := c.body(in, parent)
			if err != nil {
				return err
			}
			manager := c.name
			if in.kind == intentApply {
				manager = c.applyManager(key)
			}
			ak := appliedKey{ti: in.ti, key: m.Key()}
			h := hashOf(body, manager)
			if in.kind == intentOwn {
				if declared[in.ti] == nil {
					declared[in.ti] = map[Key]bool{}
				}
				declared[in.ti][m.Key()] = true
			}
			// An observed object that has every field of body needs no write,
			// unless the last apply set fields that body drops: those must
			// be removed. An owned object's body carries the hash of the rest
			// of it in an annotation, so matching it means the last apply
			// sent this same body, even if this process didn't send it.
			// Apply doesn't annotate objects that it doesn't own, and relies
			// on what the last successful reconcile in this process applied.
			if in.observed != nil && matches(in.observed, body) {
				if last, ok := c.lastApplied(key, ak); in.kind == intentOwn || ok && last == h {
					applied[ak] = h
					c.m.metrics.inc("kube_apply_total", "controller", c.name, "result", "skipped")
					if err := c.applyStatus(ctx, key, in, manager, nil, applied); err != nil {
						return err
					}
					continue
				}
			}
			var resp fieldManagers
			var out any
			if in.status {
				out = &resp
			}
			if err := c.m.apply(ctx, in.ti, m.Key(), in.res.path(m.Namespace, m.Name), manager, body, out); err != nil {
				return fmt.Errorf("applying %v %s: %w", in.ti, m.Key(), err)
			}
			applied[ak] = h
			c.m.metrics.inc("kube_apply_total", "controller", c.name, "result", "applied")
			c.log.Debug("applied", "key", key.String(), "object", in.ti.String()+" "+m.Key().String())
			owns := resp.ownsStatus(manager)
			if err := c.applyStatus(ctx, key, in, manager, &owns, applied); err != nil {
				return err
			}
		case intentDelete:
			if err := c.delete(ctx, in.ti, in.res, m); err != nil {
				return err
			}
		}
	}
	c.setApplied(key, applied)

	for ti, src := range c.childSources() {
		for _, o := range src.owned(key.String()) {
			om := metaOfAny(o)
			// The owner annotation names only a namespace and name, so a
			// child with another owner UID belongs to an earlier owner with
			// this name, or to an owner of another type.
			if declared[ti][om.Key()] || om.Deleting() || om.Labels[c.labels.ownerUID] != pm.UID {
				continue
			}
			res, err := c.m.resolve(ctx, ti)
			if err != nil {
				return err
			}
			if err := c.delete(ctx, ti, res, om); err != nil {
				return err
			}
			c.log.Debug("pruned", "key", key.String(), "object", ti.String()+" "+om.Key().String())
		}
	}

	// The finalizer was only for owned objects that garbage collection
	// can't delete. Once none are declared, delete any that remain and
	// remove the finalizer, so the owner can be deleted without this
	// controller running.
	if len(cleanup) == 0 && c.fin == nil && slices.Contains(pm.Finalizers, c.finalizer) {
		keep := map[string]bool{}
		for ti, keys := range declared {
			for k := range keys {
				keep[ti.apiVersion+"/"+ti.kind+" "+k.String()] = true
			}
		}
		if err := c.cleanupOwned(ctx, parent, keep); err != nil {
			return err
		}
		if err := c.removeFinalizer(ctx, parent, rv); err != nil {
			return err
		}
	}
	return nil
}

func (c *controller[T, P]) delete(ctx context.Context, ti *typeInfo, res resolved, m *ObjectMeta) error {
	err := c.m.delete(ctx, ti, m.Key(), res.path(m.Namespace, m.Name), client.DeleteOptions{UID: m.UID, Propagation: "Background"})
	if err != nil && !client.IsNotFound(err) && !client.IsConflict(err) {
		return fmt.Errorf("deleting %v %s: %w", ti, m.Key(), err)
	}
	c.m.metrics.inc("kube_delete_total", "controller", c.name)
	return nil
}

// canReference reports whether an owned object can carry an owner reference
// to its owner, so garbage collection deletes it with the owner.
func (c *controller[T, P]) canReference(in intent, owner *ObjectMeta) bool {
	if !c.res.namespaced {
		return true
	}
	return in.res.namespaced && metaOfAny(in.obj).Namespace == owner.Namespace
}

// applyManager is the field manager for Apply intents. Each reconciled
// object gets its own, so two objects that apply fields to the same target
// don't remove each other's fields.
func (c *controller[T, P]) applyManager(key Key) string {
	m := c.name + "/" + key.String()
	if len(m) <= 128 {
		return m
	}
	h := fnv.New64a()
	h.Write([]byte(key.String()))
	return fmt.Sprintf("%s/%x", c.name, h.Sum64())
}

// body builds the server-side apply document for an Own or Apply intent.
func (c *controller[T, P]) body(in intent, parent *T) (map[string]any, error) {
	doc, err := toMap(in.obj)
	if err != nil {
		return nil, err
	}
	doc["apiVersion"], doc["kind"] = in.ti.apiVersion, in.ti.kind
	if in.ti.status != nil {
		delete(doc, "status")
	}
	meta, _ := doc["metadata"].(map[string]any)
	if meta == nil {
		meta = map[string]any{}
		doc["metadata"] = meta
	}
	for _, k := range []string{"uid", "resourceVersion", "generation", "creationTimestamp", "deletionTimestamp", "managedFields"} {
		delete(meta, k)
	}
	if in.kind != intentOwn {
		// Apply changes an existing object. With its UID, the apply fails
		// rather than creating the object if it's gone.
		uid := metaOfAny(in.obj).UID
		if uid == "" && in.observed != nil {
			uid = metaOfAny(in.observed).UID
		}
		if uid != "" {
			meta["uid"] = uid
		}
		return doc, nil
	}
	pm := metaOf[T, P](parent)
	labels, _ := meta["labels"].(map[string]any)
	if labels == nil {
		labels = map[string]any{}
	}
	labels[c.labels.controller] = c.name
	labels[c.labels.ownerUID] = pm.UID
	meta["labels"] = labels
	anns, _ := meta["annotations"].(map[string]any)
	if anns == nil {
		anns = map[string]any{}
	}
	anns[c.labels.owner] = pm.Key().String()
	meta["annotations"] = anns
	if c.canReference(in, pm) {
		refs, _ := meta["ownerReferences"].([]any)
		refs = append(refs, map[string]any{
			"apiVersion":         c.ti.apiVersion,
			"kind":               c.ti.kind,
			"name":               pm.Name,
			"uid":                pm.UID,
			"controller":         true,
			"blockOwnerDeletion": true,
		})
		meta["ownerReferences"] = refs
	}
	anns[c.labels.applied] = strconv.FormatUint(hashOf(doc, c.name), 16)
	return doc, nil
}

// setFinalizer adds or removes this controller's finalizer with a dedicated
// field manager, so it never conflicts with other managers' finalizers.
// cleanup, when not empty, records the owned kinds to delete on finalize.
//
// Server-side apply creates objects that don't exist. The UID in the body
// makes the apply fail instead, so a reconcile working from a stale cache
// can't recreate an object that was just deleted.
//
// If rv points to a resource version, each write requires it and replaces
// it with the version that the write leaves, so that the reconcile's status
// write can still carry its precondition.
func (c *controller[T, P]) setFinalizer(ctx context.Context, obj *T, present bool, cleanup string, rv *string) error {
	m := metaOf[T, P](obj)
	meta := map[string]any{"name": m.Name, "uid": m.UID}
	if m.Namespace != "" {
		meta["namespace"] = m.Namespace
	}
	conditional := rv != nil && *rv != ""
	if conditional {
		meta["resourceVersion"] = *rv
	}
	if present {
		meta["finalizers"] = []string{c.finalizer}
		if cleanup != "" {
			meta["annotations"] = map[string]string{c.labels.cleanup: cleanup}
		}
	}
	body := map[string]any{"apiVersion": c.ti.apiVersion, "kind": c.ti.kind, "metadata": meta}
	var out struct {
		Metadata ObjectMeta `json:"metadata"`
	}
	path := c.res.path(m.Namespace, m.Name)
	if err := c.m.apply(ctx, c.ti, m.Key(), path, c.name+"-finalizer", body, &out); err != nil {
		if conditional && client.IsConflict(err) {
			return fmt.Errorf("%w: %w", errStale, err)
		}
		if !present && replaced(err) {
			return nil
		}
		return err
	}
	if conditional {
		*rv = out.Metadata.ResourceVersion
	}
	if present {
		m.Finalizers = out.Metadata.Finalizers
		m.Annotations = out.Metadata.Annotations
		return nil
	}
	// Another field manager may also have listed this finalizer. Remove it
	// by position, guarded by a test so a concurrent change fails instead of
	// removing the wrong entry.
	if i := slices.Index(out.Metadata.Finalizers, c.finalizer); i >= 0 {
		ops := []map[string]any{
			{"op": "test", "path": fmt.Sprintf("/metadata/finalizers/%d", i), "value": c.finalizer},
			{"op": "remove", "path": fmt.Sprintf("/metadata/finalizers/%d", i)},
		}
		if conditional {
			// A patched resource version that isn't the stored one fails
			// with a conflict, as the apply does. A failed test would fail
			// as invalid instead.
			ops = append(ops, map[string]any{"op": "replace", "path": "/metadata/resourceVersion", "value": *rv})
		}
		patch, _ := json.Marshal(ops)
		if err := c.m.patch(ctx, c.ti, m.Key(), path, client.JSONPatch, patch, &out); err != nil {
			switch {
			case conditional && client.IsConflict(err):
				return fmt.Errorf("%w: %w", errStale, err)
			case client.IsNotFound(err):
				return nil
			}
			return err
		}
		if conditional {
			*rv = out.Metadata.ResourceVersion
		}
	}
	return nil
}

// removeFinalizer removes the controller's finalizer from obj, and treats rv
// as setFinalizer does. The generate command grants the permission that this
// takes only to controllers that need it, so a denial names the option that
// grants it.
func (c *controller[T, P]) removeFinalizer(ctx context.Context, obj *T, rv *string) error {
	err := c.setFinalizer(ctx, obj, false, "", rv)
	switch {
	case err == nil:
		return nil
	case client.IsForbidden(err) && c.fin == nil && !c.opts.finalizes:
		return fmt.Errorf("removing finalizer %s: %w; if an earlier version of the program added it, pass kube.RemovesFinalizer() to kube.For and run generate again", c.finalizer, err)
	default:
		return fmt.Errorf("removing finalizer: %w", err)
	}
}

// finalize runs the Finalizer, deletes owned objects that garbage
// collection can't, and removes the finalizer.
func (c *controller[T, P]) finalize(ctx context.Context, key Key, cached, obj *T, pre precondition) (time.Duration, error) {
	rctx, s := newScope(ctx, c.m, &c.core, key)
	defer s.cancel(nil)
	defer c.m.events.send(&c.core, metaOf[T, P](cached), "Finalize", s)
	var err error
	if c.fin != nil {
		err = c.call(rctx, func(ctx context.Context) error { return c.fin.Finalize(ctx, obj) })
		if s.err != nil {
			err = s.err
		}
	}
	if err == nil {
		err = c.cleanupOwned(ctx, obj, nil)
	}
	if err == nil {
		// A status write follows the removal only if it fails, so the
		// removal needn't carry the precondition.
		err = c.removeFinalizer(ctx, obj, nil)
	}
	c.m.tracker.forget(ref{c: &c.core, key: key})
	if err != nil {
		if serr := c.writeStatus(ctx, cached, obj, err, pre); serr != nil && !client.IsNotFound(serr) && !errors.Is(serr, errStale) {
			c.log.Warn("writing status failed", "key", key.String(), "err", serr)
		}
		return s.requeue, err
	}
	c.setApplied(key, nil)
	c.log.Debug("finalized", "key", key.String())
	return 0, nil
}

// cleanupOwned deletes the owned objects of the kinds recorded in obj's
// cleanup annotation, except those in keep, which holds "apiVersion/kind
// namespace/name" strings.
func (c *controller[T, P]) cleanupOwned(ctx context.Context, obj *T, keep map[string]bool) error {
	m := metaOf[T, P](obj)
	for _, kind := range splitList(m.Annotations[c.labels.cleanup]) {
		i := strings.LastIndex(kind, "/")
		if i < 0 {
			continue
		}
		r, err := c.m.client.Resource(ctx, kind[:i], kind[i+1:])
		if err != nil {
			return err
		}
		res := resolved{apiVersion: kind[:i], plural: r.Name, namespaced: r.Namespaced}
		var owned []ObjectMeta
		q := url.Values{"labelSelector": {c.labels.ownerUID + "=" + m.UID + "," + c.labels.controller + "=" + c.name}}
		_, err = c.m.client.ListAll(ctx, res.path("", ""), q, listAccept, 500, func(dec *json.Decoder) error {
			var item struct {
				Metadata ObjectMeta `json:"metadata"`
			}
			if err := dec.Decode(&item); err != nil {
				return err
			}
			owned = append(owned, item.Metadata)
			return nil
		})
		if err != nil {
			return fmt.Errorf("listing owned %s: %w", kind, err)
		}
		ti := &typeInfo{apiVersion: kind[:i], kind: kind[i+1:]}
		for _, om := range owned {
			if keep[kind+" "+om.Key().String()] || om.Deleting() {
				continue
			}
			if err := c.delete(ctx, ti, res, &om); err != nil {
				return err
			}
		}
	}
	return nil
}

// replaced reports whether a forced apply with a UID failed because the
// object no longer exists (409) or was recreated with a new UID (422).
// Forced applies never fail with field manager conflicts.
func replaced(err error) bool {
	if client.IsConflict(err) || client.IsNotFound(err) {
		return true
	}
	return client.IsInvalid(err) && strings.Contains(err.Error(), "metadata.uid")
}

func toMap(obj any) (map[string]any, error) {
	b, err := json.Marshal(obj)
	if err != nil {
		return nil, err
	}
	dec := json.NewDecoder(bytes.NewReader(b))
	dec.UseNumber()
	var m map[string]any
	if err := dec.Decode(&m); err != nil {
		return nil, err
	}
	return m, nil
}

// matches reports whether the observed object already has every field in
// the apply document.
func matches(observed any, body map[string]any) bool {
	have, err := toMap(observed)
	if err != nil {
		return false
	}
	return subset.Contains(have, body)
}

func hashOf(body map[string]any, manager string) uint64 {
	b, _ := json.Marshal(body)
	h := fnv.New64a()
	h.Write([]byte(manager))
	h.Write(b)
	return h.Sum64()
}

func hashJSON(b []byte) uint64 {
	h := fnv.New64a()
	h.Write(b)
	return h.Sum64()
}

func splitList(s string) []string {
	if s == "" {
		return nil
	}
	out := strings.Split(s, ",")
	slices.Sort(out)
	return out
}

func setOf(xs []string) map[string]struct{} {
	m := make(map[string]struct{}, len(xs))
	for _, x := range xs {
		m[x] = struct{}{}
	}
	return m
}
