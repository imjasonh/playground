package kube

import (
	"bytes"
	"context"
	"encoding/json"
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
// the deleted object owns are cleaned up without it.
type Finalizer[T any] interface {
	Finalize(ctx context.Context, obj *T) error
}

// Controller is a reconciler configured to run in a Manager. Create one
// with For.
type Controller interface {
	setup(ctx context.Context, m *Manager) error
	run(ctx context.Context) error
	controllerName() string
	synced() bool
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
}

// Named sets the controller's name. The name appears in logs and metrics,
// is the field manager for server-side apply, and labels owned objects. It
// defaults to the lowercase kind, for example "website".
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
// reconcile.
func Owns[T any, P Resource[T]]() Option {
	return func(o *options) { o.owns = append(o.owns, typeInfoFor[T, P]) }
}

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

	mu       sync.Mutex
	children map[*typeInfo]source
	applied  map[Key]map[appliedKey]uint64
	// statuses holds a hash of each object's status as this controller last
	// wrote or confirmed it, to tell its own status writes from others'.
	statuses map[Key]uint64
}

type appliedKey struct {
	ti  *typeInfo
	key Key
}

// labelKeys are the label and annotation keys the framework uses, under a
// configurable domain.
type labelKeys struct {
	controller string // label: controller name, on owned objects
	ownerUID   string // label: owner UID, on owned objects
	owner      string // annotation: owner namespace/name, on owned objects
	applied    string // annotation: hash of the last applied body, on owned objects
	cleanup    string // annotation: owned kinds to delete on finalize, on owners
	managedBy  string // label: on CustomResourceDefinitions the framework installs
}

func newLabelKeys(domain string) labelKeys {
	return labelKeys{
		controller: domain + "/controller",
		ownerUID:   domain + "/owner-uid",
		owner:      domain + "/owner",
		applied:    domain + "/applied",
		cleanup:    domain + "/cleanup",
		managedBy:  domain + "/managed-by",
	}
}

func (c *core) enqueue(k Key, p queue.Priority) {
	if c.q != nil {
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

// setStatus records h as the hash of k's status, or forgets k's if ok is
// false.
func (c *core) setStatus(k Key, h uint64, ok bool) {
	c.mu.Lock()
	defer c.mu.Unlock()
	if !ok {
		delete(c.statuses, k)
		return
	}
	if c.statuses == nil {
		c.statuses = map[Key]uint64{}
	}
	c.statuses[k] = h
}

type controller[T any, P Resource[T]] struct {
	core
	r       Reconciler[T]
	fin     Finalizer[T]
	opts    options
	m       *Manager
	primary *informer[T, P]
}

var nameRE = regexp.MustCompile(`^[a-z0-9]([-a-z0-9.]{0,48}[a-z0-9])?$`)

func (c *controller[T, P]) controllerName() string { return c.name }

func (c *controller[T, P]) synced() bool { return c.primary != nil && c.primary.hasSynced.Load() }

func (c *controller[T, P]) setup(ctx context.Context, m *Manager) error {
	ti, err := typeInfoFor[T, P]()
	if err != nil {
		return err
	}
	c.ti, c.m = ti, m
	c.name = c.opts.name
	if c.name == "" {
		c.name = strings.ToLower(ti.kind)
	}
	if !nameRE.MatchString(c.name) {
		return fmt.Errorf("kube: controller name %q must be at most 50 lowercase letters, digits, '-', or '.'", c.name)
	}
	c.labels = newLabelKeys(m.Domain)
	c.finalizer = m.Domain + "/" + c.name
	c.log = m.log.With("controller", c.name)
	if c.res, err = m.ensureType(ctx, ti); err != nil {
		return fmt.Errorf("controller %s: %w", c.name, err)
	}
	ns := m.Namespace
	if c.opts.namespace != "" {
		ns = c.opts.namespace
	}
	c.q = queue.New[Key](queue.Options{})
	cfg := m.informerConfig(c.res, ns, c.opts.selector, "")
	c.primary = newInformer[T, P](m.newID(), ti, c.res, m.client, cfg, m.log, m.metrics)
	c.primary.addHandler(c.onPrimary)
	m.adopt(ti, c.res, cfg, c.primary)
	for _, own := range c.opts.owns {
		oti, err := own()
		if err != nil {
			return err
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
	go c.primary.run(ctx)
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
				c.process(ctx, key)
				c.q.Done(key)
			}
		})
	}
	if c.opts.resync > 0 {
		wg.Go(func() { c.resyncLoop(ctx) })
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
			c.q.Add(metaOf[T, P](o).Key(), queue.Low)
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
		c.q.Add(metaOf[T, P](old).Key(), queue.High)
	case old == nil || c.specChanged(old, new) || c.statusChanged(old, new):
		c.q.Add(metaOf[T, P](new).Key(), p)
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
	if m.Deleting() {
		if !slices.Contains(m.Finalizers, c.finalizer) {
			return 0, nil
		}
		return c.finalize(ctx, key, cached, obj)
	}
	if c.fin != nil && !slices.Contains(m.Finalizers, c.finalizer) {
		if err := c.setFinalizer(ctx, obj, true, m.Annotations[c.labels.cleanup]); err != nil {
			return 0, fmt.Errorf("adding finalizer: %w", err)
		}
	}
	rctx, s := newScope(ctx, c.m, &c.core, key)
	defer s.cancel(nil)
	err := c.call(rctx, func(ctx context.Context) error { return c.r.Reconcile(ctx, obj) })
	if s.err != nil {
		err = s.err
	}
	if err == nil {
		err = c.execute(ctx, key, obj, s)
	}
	c.m.tracker.retain(ref{c: &c.core, key: key}, s.deps)
	if serr := c.writeStatus(ctx, cached, obj, err); serr != nil {
		if err == nil {
			err = fmt.Errorf("writing status: %w", serr)
		} else {
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
// objects that the reconcile no longer declared.
func (c *controller[T, P]) execute(ctx context.Context, key Key, parent *T, s *scope) error {
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
			if err := c.setFinalizer(ctx, parent, true, strings.Join(want, ",")); err != nil {
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
			// on what this process last applied.
			if in.observed != nil && matches(in.observed, body) {
				if last, ok := c.lastApplied(key, ak); in.kind == intentOwn || ok && last == h {
					applied[ak] = h
					c.m.metrics.inc("kube_apply_total", "controller", c.name, "result", "skipped")
					continue
				}
			}
			if err := c.m.client.Apply(ctx, in.res.path(m.Namespace, m.Name), manager, true, body, nil); err != nil {
				return fmt.Errorf("applying %v %s: %w", in.ti, m.Key(), err)
			}
			applied[ak] = h
			c.m.metrics.inc("kube_apply_total", "controller", c.name, "result", "applied")
			c.log.Debug("applied", "key", key.String(), "object", in.ti.String()+" "+m.Key().String())
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
			if declared[ti][om.Key()] || om.Deleting() {
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
		if err := c.setFinalizer(ctx, parent, false, ""); err != nil {
			return fmt.Errorf("removing finalizer: %w", err)
		}
	}
	return nil
}

func (c *controller[T, P]) delete(ctx context.Context, ti *typeInfo, res resolved, m *ObjectMeta) error {
	err := c.m.client.Delete(ctx, res.path(m.Namespace, m.Name), client.DeleteOptions{UID: m.UID, Propagation: "Background"})
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
func (c *controller[T, P]) setFinalizer(ctx context.Context, obj *T, present bool, cleanup string) error {
	m := metaOf[T, P](obj)
	meta := map[string]any{"name": m.Name, "uid": m.UID}
	if m.Namespace != "" {
		meta["namespace"] = m.Namespace
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
	if err := c.m.client.Apply(ctx, path, c.name+"-finalizer", true, body, &out); err != nil {
		if !present && replaced(err) {
			return nil
		}
		return err
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
		patch, _ := json.Marshal([]map[string]any{
			{"op": "test", "path": fmt.Sprintf("/metadata/finalizers/%d", i), "value": c.finalizer},
			{"op": "remove", "path": fmt.Sprintf("/metadata/finalizers/%d", i)},
		})
		if err := c.m.client.Patch(ctx, path, client.JSONPatch, nil, patch, nil); err != nil && !client.IsNotFound(err) {
			return err
		}
	}
	return nil
}

// finalize runs the Finalizer, deletes owned objects that garbage
// collection can't, and removes the finalizer.
func (c *controller[T, P]) finalize(ctx context.Context, key Key, cached, obj *T) (time.Duration, error) {
	rctx, s := newScope(ctx, c.m, &c.core, key)
	defer s.cancel(nil)
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
		err = c.setFinalizer(ctx, obj, false, "")
	}
	c.m.tracker.forget(ref{c: &c.core, key: key})
	if err != nil {
		if serr := c.writeStatus(ctx, cached, obj, err); serr != nil && !client.IsNotFound(serr) {
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
		q := url.Values{"labelSelector": {c.labels.ownerUID + "=" + m.UID}}
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
