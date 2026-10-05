package kube

import (
	"cmp"
	"context"
	"errors"
	"fmt"
	"slices"
	"time"

	"github.com/imjasonh/playground/kube/internal/clone"
)

// world is where a reconcile reads from: the manager's caches in production,
// or in-memory objects in tests.
type world interface {
	// source returns the cache that Get and List use for ti, starting it
	// and waiting for it to sync if needed.
	source(ctx context.Context, ti *typeInfo) (source, error)
	// existing returns the cache for ti if it's already running, or nil.
	existing(ti *typeInfo) source
	// children returns the cache of ti objects that controller c owns.
	children(ctx context.Context, c *core, ti *typeInfo) (source, error)
	// fetch reads one object from the API server. It returns nil, nil if
	// the object doesn't exist.
	fetch(ctx context.Context, ti *typeInfo, k Key) (any, error)
	resolve(ctx context.Context, ti *typeInfo) (resolved, error)
	deps() *tracker
	services
}

type scopeKey struct{}

type intentKind int

const (
	intentOwn intentKind = iota
	intentApply
	intentDelete
)

// intent is a change that a reconcile asked for. The framework carries out
// intents after Reconcile returns successfully, in the order they were made.
type intent struct {
	kind     intentKind
	ti       *typeInfo
	res      resolved
	obj      any // desired object, or the object to delete
	observed any // the cached object, shared; nil if unknown
	// status is set when the framework also applies obj's status to the
	// status subresource.
	status bool
}

// scope is the state of one reconcile. Reconcile's context carries it.
type scope struct {
	w        world
	c        *core
	key      Key
	parentNS bool
	deps     map[dep]struct{}
	intents  []intent
	events   []eventIntent
	requeue  time.Duration
	err      error
	lastErr  error
	cancel   context.CancelCauseFunc
	// webhook scopes can read, but don't track reads or accept intents.
	webhook bool
}

func newScope(ctx context.Context, w world, c *core, key Key) (context.Context, *scope) {
	s := &scope{w: w, c: c, key: key, parentNS: c.res.namespaced, deps: map[dep]struct{}{}, lastErr: c.lastError(key)}
	ctx, s.cancel = context.WithCancelCause(context.WithValue(ctx, scopeKey{}, s))
	return ctx, s
}

// newWebhookScope returns a context in which Get, List, and Fetch read from
// the manager, for admission and conversion webhooks and Serve handlers.
func newWebhookScope(ctx context.Context, w world) (context.Context, *scope) {
	s := &scope{w: w, webhook: true}
	ctx, s.cancel = context.WithCancelCause(context.WithValue(ctx, scopeKey{}, s))
	return ctx, s
}

// readOnly fails a webhook scope that's asked to change something.
func (s *scope) readOnly(verb string) bool {
	if s.webhook {
		s.fail(fmt.Errorf("kube.%s can't be called in a webhook or a kube.Serve handler, which can only read", verb))
	}
	return s.webhook
}

func scopeFrom(ctx context.Context, verb string) *scope {
	s, _ := ctx.Value(scopeKey{}).(*scope)
	if s == nil {
		panic(fmt.Sprintf("kube.%s called outside a reconcile, webhook, or kube.Serve handler: pass it the context that Reconcile, Finalize, Validate, or Default received, the context of a kube.Serve request, or a context from kube.Fake or kube.FakeRequest in a test", verb))
	}
	return s
}

// fail records the first error that keeps the reconcile from seeing the
// world correctly and cancels the reconcile's context. The framework then
// skips the reconcile's writes and retries it.
func (s *scope) fail(err error) {
	if s.err == nil {
		s.err = err
		s.cancel(err)
	}
}

func (s *scope) self() ref { return ref{c: s.c, key: s.key} }

func (s *scope) track(d dep, sel selector) {
	if s.webhook {
		return
	}
	s.deps[d] = struct{}{}
	s.w.deps().add(s.self(), d, sel)
}

func typeFor[T any, P Resource[T]](s *scope) *typeInfo {
	ti, err := typeInfoFor[T, P]()
	if err != nil {
		s.fail(err)
		return nil
	}
	return ti
}

func (s *scope) sourceFor(ctx context.Context, ti *typeInfo) (source, resolved, bool) {
	if ti == nil || s.err != nil {
		return nil, resolved{}, false
	}
	res, err := s.w.resolve(ctx, ti)
	if err != nil {
		s.fail(err)
		return nil, resolved{}, false
	}
	src, err := s.w.source(ctx, ti)
	if err != nil {
		s.fail(fmt.Errorf("reading %v: %w", ti, err))
		return nil, resolved{}, false
	}
	return src, res, true
}

// Get returns the object of type T with the given namespace and name, or
// nil if it doesn't exist. Leave namespace empty for cluster-scoped types.
//
// Get reads from an in-memory cache that the framework keeps current with
// a watch, starting it the first time a reconcile reads type T. The returned
// object is a copy that you can change. When the object later changes, the
// reconcile that read it runs again.
func Get[T any, P Resource[T]](ctx context.Context, namespace, name string) *T {
	s := scopeFrom(ctx, "Get")
	src, res, ok := s.sourceFor(ctx, typeFor[T, P](s))
	if !ok {
		return nil
	}
	if !res.namespaced {
		namespace = ""
	}
	s.track(dep{src: src.id(), ns: namespace, name: name}, nil)
	if o := src.get(Key{Namespace: namespace, Name: name}); o != nil {
		return o.(*T)
	}
	return nil
}

// ListOption narrows List.
type ListOption func(*listOptions)

type listOptions struct {
	namespace string
	labels    map[string]string
	selector  string
}

// InNamespace limits List to one namespace.
func InNamespace(namespace string) ListOption {
	return func(o *listOptions) { o.namespace = namespace }
}

// MatchingLabels limits List to objects whose labels include all of these.
func MatchingLabels(labels map[string]string) ListOption {
	return func(o *listOptions) { o.labels = labels }
}

// MatchingSelector limits List to objects that match a label selector in
// the Kubernetes syntax, for example "tier in (web,api),!canary".
func MatchingSelector(selector string) ListOption {
	return func(o *listOptions) { o.selector = selector }
}

// List returns the objects of type T, sorted by namespace and name. Like
// Get, it reads from a cache, returns copies, and runs the reconcile again
// when the set of matching objects or any of them changes.
func List[T any, P Resource[T]](ctx context.Context, opts ...ListOption) []*T {
	s := scopeFrom(ctx, "List")
	var lo listOptions
	for _, o := range opts {
		o(&lo)
	}
	sel := selectorFromMap(lo.labels)
	if lo.selector != "" {
		parsed, err := parseSelector(lo.selector)
		if err != nil {
			s.fail(Permanent(err))
			return nil
		}
		sel = append(sel, parsed...)
	}
	src, res, ok := s.sourceFor(ctx, typeFor[T, P](s))
	if !ok {
		return nil
	}
	ns := lo.namespace
	if !res.namespaced {
		ns = ""
	}
	s.track(dep{src: src.id(), ns: ns, sel: sel.String(), list: true}, sel)
	objs := src.list(ns, sel)
	out := make([]*T, len(objs))
	for i, o := range objs {
		out[i] = o.(*T)
	}
	slices.SortFunc(out, func(a, b *T) int {
		ma, mb := metaOf[T, P](a), metaOf[T, P](b)
		return cmp.Or(cmp.Compare(ma.Namespace, mb.Namespace), cmp.Compare(ma.Name, mb.Name))
	})
	return out
}

// Fetch reads one object directly from the API server, bypassing caches. It
// returns nil and no error if the object doesn't exist. Use it for large
// objects that you need rarely, such as the data of one Secret, so the
// framework doesn't have to cache every object of that type. Fetch doesn't
// run the reconcile again when the object changes.
func Fetch[T any, P Resource[T]](ctx context.Context, namespace, name string) (*T, error) {
	s := scopeFrom(ctx, "Fetch")
	ti := typeFor[T, P](s)
	if ti == nil {
		return nil, s.err
	}
	o, err := s.w.fetch(ctx, ti, Key{Namespace: namespace, Name: name})
	if err != nil || o == nil {
		return nil, err
	}
	return o.(*T), nil
}

func (s *scope) prepare(ctx context.Context, verb string, ti *typeInfo, m *ObjectMeta) (resolved, bool) {
	if ti == nil || s.err != nil {
		return resolved{}, false
	}
	res, err := s.w.resolve(ctx, ti)
	if err != nil {
		s.fail(err)
		return resolved{}, false
	}
	switch {
	case !res.namespaced:
		m.Namespace = ""
	case m.Namespace == "" && s.parentNS:
		m.Namespace = s.key.Namespace
	case m.Namespace == "":
		s.fail(fmt.Errorf("kube.%s: %v %q needs a namespace because the object being reconciled is cluster-scoped", verb, ti, m.Name))
		return resolved{}, false
	}
	if m.Name == "" {
		s.fail(fmt.Errorf("kube.%s: %v needs a name", verb, ti))
		return resolved{}, false
	}
	for _, in := range s.intents {
		if in.kind == intentDelete || !in.ti.sameKind(ti) || metaOfAny(in.obj).Key() != m.Key() {
			continue
		}
		first := "Apply"
		if in.kind == intentOwn {
			first = "Own"
		}
		msg := fmt.Sprintf("kube.%s: %v %s was declared twice in one reconcile", verb, ti, m.Key())
		switch {
		case first != verb:
			msg += fmt.Sprintf(", with %s and %s; Own doesn't apply a status, and Apply is for objects that the reconciled object doesn't own", first, verb)
		case in.ti != ti:
			msg += fmt.Sprintf(", as %v and %v; declare it with one type", in.ti.goType, ti.goType)
		}
		s.fail(errors.New(msg))
		return resolved{}, false
	}
	return res, true
}

// Own declares that the object being reconciled should own an object with
// exactly the fields set in desired, and returns the owned object as last
// observed, or nil if it doesn't exist yet.
//
// After Reconcile returns nil, the framework creates or updates every owned
// object with server-side apply and deletes objects it created for this owner
// in an earlier reconcile that weren't declared this time. It skips the write
// when the observed object already matches. Owned objects are deleted when
// their owner is. The framework doesn't apply desired's status, but changes
// to an owned object, including its status, run the owner's reconcile again.
//
// The namespace of desired defaults to the owner's. An owned object may be in
// another namespace, or cluster-scoped; the framework then adds a finalizer
// to the owner so it can delete the owned object itself.
//
// Set only the fields you care about: server-side apply makes your
// controller the manager of exactly those fields and leaves the rest alone.
// Use pointers or omitempty for optional fields, so a zero value isn't sent.
func Own[T any, P Resource[T]](ctx context.Context, desired P) P {
	s := scopeFrom(ctx, "Own")
	if s.readOnly("Own") {
		return nil
	}
	ti := typeFor[T, P](s)
	m := &desired.object().ObjectMeta
	res, ok := s.prepare(ctx, "Own", ti, m)
	if !ok {
		return nil
	}
	src, err := s.w.children(ctx, s.c, ti)
	if err != nil {
		s.fail(fmt.Errorf("watching owned %v: %w", ti, err))
		return nil
	}
	observed := src.peek(m.Key())
	s.intents = append(s.intents, intent{kind: intentOwn, ti: ti, res: res, obj: desired, observed: observed})
	if observed == nil {
		return nil
	}
	return clone.Of(observed.(*T))
}

// Apply declares that the fields set in desired should have these values on
// an object that the reconciled object doesn't own, for example an
// annotation on a Deployment that someone else manages. After Reconcile
// returns nil, the framework applies the fields with server-side apply. The
// object isn't deleted with the reconciled object, and fields that a later
// reconcile stops applying are removed.
//
// If desired's type has a status, the framework then applies the status to
// the object's status subresource, in a second request with the same field
// manager, so the status fields that a later reconcile stops applying are
// removed too, unless another manager also set them. The framework applies
// the status with force, so the controller takes over every field in it. Set
// only your own fields, and build a fresh object rather than editing one that
// Get returned. The framework sends an empty status only to remove status
// fields that an earlier reconcile applied, even one that failed or that ran
// in an earlier run of the program. If the cluster doesn't serve a status
// subresource for the type, a status that isn't empty fails the reconcile.
//
// When the reconciled type has a status, the framework writes the status of
// the object being reconciled from the object that Reconcile received. So
// when desired is that object, Apply ignores an empty status and fails the
// reconcile for any other.
func Apply[T any, P Resource[T]](ctx context.Context, desired P) {
	s := scopeFrom(ctx, "Apply")
	if s.readOnly("Apply") {
		return
	}
	ti := typeFor[T, P](s)
	m := &desired.object().ObjectMeta
	res, ok := s.prepare(ctx, "Apply", ti, m)
	if !ok {
		return
	}
	status := ti.status != nil
	if status && s.writesStatus(ti, m.Key()) {
		st, err := statusOf(desired)
		if err != nil {
			s.fail(err)
			return
		}
		if st != nil {
			s.fail(fmt.Errorf("kube.Apply: %v %s is the object being reconciled, so the framework writes its status; set the status on the object that Reconcile received", ti, m.Key()))
			return
		}
		status = false
	}
	var observed any
	if src := s.w.existing(ti); src != nil {
		observed = src.peek(m.Key())
	}
	s.intents = append(s.intents, intent{kind: intentApply, ti: ti, res: res, obj: desired, observed: observed, status: status})
}

// writesStatus reports whether the framework writes the status of the object
// of type ti with key k after the reconcile, because it's the object being
// reconciled.
func (s *scope) writesStatus(ti *typeInfo, k Key) bool {
	if s.c == nil || s.c.ti == nil || s.c.ti.status == nil {
		return false
	}
	return ti.sameKind(s.c.ti) && k == s.key
}

// Delete declares that obj should be deleted. After Reconcile returns nil,
// the framework deletes it, if it still has the same UID.
func Delete[T any, P Resource[T]](ctx context.Context, obj P) {
	s := scopeFrom(ctx, "Delete")
	if s.readOnly("Delete") {
		return
	}
	ti := typeFor[T, P](s)
	if ti == nil {
		return
	}
	res, err := s.w.resolve(ctx, ti)
	if err != nil {
		s.fail(err)
		return
	}
	s.intents = append(s.intents, intent{kind: intentDelete, ti: ti, res: res, obj: obj})
}

// RequeueAfter asks for another reconcile after d, even if nothing changes.
// Use it when the desired state depends on time, such as an expiry, or on a
// system outside Kubernetes that can't be watched. If you call it more than
// once, the shortest duration wins.
func RequeueAfter(ctx context.Context, d time.Duration) {
	s := scopeFrom(ctx, "RequeueAfter")
	if s.readOnly("RequeueAfter") {
		return
	}
	if d > 0 && (s.requeue == 0 || d < s.requeue) {
		s.requeue = d
	}
}

// LastError returns the error that the previous reconcile of the object
// failed with, or nil if it succeeded or there wasn't one. The framework
// carries out a reconcile's declarations after Reconcile returns, so only the
// next reconcile can see that one failed, for example because an admission
// policy rejected an apply. The framework writes the status even when a
// declaration fails, so that reconcile can report the error in the status.
// When a write fails because the cache was behind, the framework retries the
// reconcile, and LastError in the retry returns the error from before it.
//
// Each process keeps the errors in memory, so LastError returns nil in the
// first reconcile after the process starts or acquires the object's shard.
// It keeps them by namespace and name, so when an object is deleted and
// recreated before the process reconciles the deletion, the new object's
// first reconcile can get the old object's error. An error from the API
// server can quote the values that it rejected, so if those values are
// secret, don't copy the error into a status.
func LastError(ctx context.Context) error {
	return scopeFrom(ctx, "LastError").lastErr
}

// Permanent marks err as one that retrying won't fix, such as an invalid
// spec. The framework reports it in the object's status and waits for the
// object to change instead of retrying.
func Permanent(err error) error {
	if err == nil {
		return nil
	}
	return &permanentError{err}
}

type permanentError struct{ err error }

func (e *permanentError) Error() string { return e.err.Error() }
func (e *permanentError) Unwrap() error { return e.err }

// IsPermanent reports whether err, or an error it wraps, came from Permanent.
func IsPermanent(err error) bool {
	var p *permanentError
	return errors.As(err, &p)
}

// metaOfAny returns the metadata of a *T held in an interface.
func metaOfAny(o any) *ObjectMeta {
	return &o.(interface{ object() *Object }).object().ObjectMeta
}
