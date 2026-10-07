package kube

import (
	"context"
	"encoding/json"
	"errors"
	"io"
	"log/slog"
	"math/rand/v2"
	"net/url"
	"reflect"
	"slices"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/clone"
	"github.com/imjasonh/playground/kube/internal/protobuf"
)

// resolved is how the API server serves a type.
type resolved struct {
	apiVersion string
	plural     string
	namespaced bool
}

func (r resolved) path(namespace, name string, subresource ...string) string {
	if !r.namespaced {
		namespace = ""
	}
	return client.Path(r.apiVersion, r.plural, namespace, name, subresource...)
}

// source is a cache of one type, as reconcilers and the framework see it.
// Objects from get and list are copies the caller may change; objects from
// peek and owned are shared and must not be changed.
type source interface {
	id() int
	typeInfo() *typeInfo
	waitSynced(ctx context.Context) error
	get(k Key) any
	list(namespace string, sel selector) []any
	peek(k Key) any
	owned(owner string) []any
}

type informerConfig struct {
	// namespace limits a namespaced type to one namespace.
	namespace string
	// selector is a label selector the API server applies.
	selector string
	// ownerKey is the annotation by which to index children.
	ownerKey string
	// streaming enables streaming lists (watches with sendInitialEvents).
	streaming bool
	pageSize  int
	intern    bool
	// protobuf reads built-in types as protobuf, when the type's fields are
	// all in the schema.
	protobuf bool
}

const (
	listAccept  = "application/json;as=PartialObjectMetadataList;g=meta.k8s.io;v=v1,application/json"
	watchAccept = "application/json;as=PartialObjectMetadata;g=meta.k8s.io;v=v1,application/json"
	// The protobuf forms list JSON last, for servers that can't send
	// protobuf, such as some aggregated API servers.
	protoAccept      = "application/vnd.kubernetes.protobuf,application/json"
	protoListAccept  = "application/vnd.kubernetes.protobuf;as=PartialObjectMetadataList;g=meta.k8s.io;v=v1," + listAccept
	protoWatchAccept = "application/vnd.kubernetes.protobuf;as=PartialObjectMetadata;g=meta.k8s.io;v=v1," + watchAccept
	// firstEventTimeout bounds how long a streaming list may go without its
	// first event before the informer decides the server doesn't support
	// streaming lists. Servers that do send at least the end bookmark at once.
	firstEventTimeout = 15 * time.Second
)

var errStreamingUnsupported = errors.New("streaming lists are not supported")

// informer keeps a store in sync with the API server by listing and then
// watching, and calls handlers for every change.
type informer[T any, P Resource[T]] struct {
	idn int
	ti  *typeInfo
	res resolved
	cfg informerConfig
	c   *client.Client
	log *slog.Logger
	m   *metrics

	store store[T, P]
	// sel is cfg.selector, parsed. ownWrites is false when the cache can't
	// evaluate it, and then doesn't show this process's writes.
	sel       selector
	ownWrites bool
	// pb decodes protobuf responses; nil means read JSON.
	pb *protobuf.Plan

	hmu      sync.RWMutex
	handlers []func(old, new *T, initial bool)

	attempted   chan struct{}
	attemptOnce sync.Once
	synced      chan struct{}
	syncOnce    sync.Once
	errMu       sync.Mutex
	lastErr     error
	hasSynced   atomic.Bool
	streaming   atomic.Bool
}

// decodeError is the error for an object that doesn't decode as the
// informer's type. meta names the object.
type decodeError struct {
	meta ObjectMeta
	err  error
}

func (e *decodeError) Error() string { return e.err.Error() }

// same reports whether o is about the same object as e, with the same error.
func (e *decodeError) same(o *decodeError) bool {
	return o != nil && o.meta.UID == e.meta.UID && o.err.Error() == e.err.Error()
}

func newInformer[T any, P Resource[T]](id int, ti *typeInfo, res resolved, c *client.Client, cfg informerConfig, log *slog.Logger, m *metrics) *informer[T, P] {
	inf := &informer[T, P]{
		idn:       id,
		ti:        ti,
		res:       res,
		cfg:       cfg,
		c:         c,
		log:       log.With("type", ti.String()),
		m:         m,
		attempted: make(chan struct{}),
		synced:    make(chan struct{}),
	}
	inf.store.ownerKey = cfg.ownerKey
	inf.streaming.Store(cfg.streaming)
	if cfg.pageSize == 0 {
		inf.cfg.pageSize = 500
	}
	if cfg.selector != "" {
		inf.log = inf.log.With("selector", cfg.selector)
	}
	// parseSelector doesn't parse the > and < operators, and a selector
	// with them would seem to match no object.
	if sel, err := parseSelector(cfg.selector); err == nil && !strings.ContainsAny(cfg.selector, "<>") {
		inf.sel, inf.ownWrites = sel, true
	}
	if cfg.protobuf {
		inf.pb = protoPlan(ti, inf.log)
	}
	return inf
}

func (inf *informer[T, P]) id() int             { return inf.idn }
func (inf *informer[T, P]) typeInfo() *typeInfo { return inf.ti }

func (inf *informer[T, P]) addHandler(h func(old, new *T, initial bool)) {
	inf.hmu.Lock()
	inf.handlers = append(slices.Clip(inf.handlers), h)
	inf.hmu.Unlock()
}

func (inf *informer[T, P]) notify(old, new *T, initial bool) {
	inf.hmu.RLock()
	hs := inf.handlers
	inf.hmu.RUnlock()
	for _, h := range hs {
		h(old, new, initial)
	}
}

func (inf *informer[T, P]) get(k Key) any {
	o := inf.store.get(k)
	if o == nil {
		return nil
	}
	return clone.Of(o)
}

func (inf *informer[T, P]) peek(k Key) any {
	o := inf.store.get(k)
	if o == nil {
		return nil
	}
	return o
}

func (inf *informer[T, P]) list(namespace string, sel selector) []any {
	var out []any
	inf.store.each(namespace, func(o *T) bool {
		if sel.matches(metaOf[T, P](o).Labels) {
			out = append(out, clone.Of(o))
		}
		return true
	})
	return out
}

func (inf *informer[T, P]) owned(owner string) []any {
	objs := inf.store.byOwner(owner)
	out := make([]any, len(objs))
	for i, o := range objs {
		out[i] = o
	}
	return out
}

// begin prepares the cache for a write by this process to the object at k.
// It returns the function to call with what the write stored, or nil if
// the cache doesn't hold the object.
func (inf *informer[T, P]) begin(k Key) func(*written) {
	if !inf.res.namespaced {
		k.Namespace = ""
	}
	if !inf.ownWrites || inf.cfg.namespace != "" && k.Namespace != inf.cfg.namespace {
		return nil
	}
	f := inf.store.begin(k)
	return func(w *written) { inf.store.end(f, inf.own(w)) }
}

// own decodes what a write stored as this cache holds it. It returns nil if
// the write's result is unknown, and an ownWrite without an object if the
// object is gone or doesn't match the cache's selector.
func (inf *informer[T, P]) own(w *written) *ownWrite[T] {
	switch {
	case w == nil:
		return nil
	case w.gone:
		return &ownWrite[T]{uid: w.uid}
	}
	obj := new(T)
	if err := json.Unmarshal(w.obj, obj); err != nil {
		return nil
	}
	inf.normalize(obj)
	m := metaOf[T, P](obj)
	ow := &ownWrite[T]{obj: obj, rv: m.ResourceVersion, uid: m.UID}
	if !inf.sel.matches(m.Labels) {
		ow.obj = nil
	}
	return ow
}

// waitSynced blocks until the first list completes. If the first attempt
// fails, it returns that error at once; the informer keeps retrying.
func (inf *informer[T, P]) waitSynced(ctx context.Context) error {
	select {
	case <-inf.synced:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	case <-inf.attempted:
		select {
		case <-inf.synced:
			return nil
		default:
		}
		inf.errMu.Lock()
		defer inf.errMu.Unlock()
		return inf.lastErr
	}
}

func (inf *informer[T, P]) attemptFailed(err error) {
	inf.errMu.Lock()
	inf.lastErr = err
	inf.errMu.Unlock()
	inf.attemptOnce.Do(func() { close(inf.attempted) })
}

func (inf *informer[T, P]) replaceAll(items map[Key]*T, bad map[Key]*decodeError) {
	initial := !inf.hasSynced.Load()
	changes, fresh := inf.store.replace(items, bad)
	for _, e := range fresh {
		inf.warnSkipped(e)
	}
	inf.hasSynced.Store(true)
	inf.syncOnce.Do(func() { close(inf.synced) })
	inf.attemptOnce.Do(func() { close(inf.attempted) })
	inf.log.Debug("cache synced", "objects", len(items), "changes", len(changes))
	for _, c := range changes {
		if inf.changed(c.old, c.new) {
			inf.notify(c.old, c.new, initial)
		}
	}
}

// changed reports whether a change to an object is one that T can see. Every
// change has a new resource version, and one that changes only that, or only
// fields that T doesn't declare, can't change what a reconcile reads. A
// metadata-only type can't see the fields that matter (often its reconciler
// fetches them), so for those types every new resource version counts.
func (inf *informer[T, P]) changed(old, new *T) bool {
	if old == nil || new == nil || inf.ti.metadataOnly {
		return true
	}
	a, b := *old, *new
	ma, mb := metaOf[T, P](&a), metaOf[T, P](&b)
	ma.ResourceVersion, mb.ResourceVersion = "", ""
	return !reflect.DeepEqual(a, b)
}

func (inf *informer[T, P]) run(ctx context.Context) {
	b := backoff{min: 800 * time.Millisecond, max: 30 * time.Second}
	b.reset()
	rv, needSync := "", true
	for ctx.Err() == nil {
		var err error
		if needSync {
			inf.store.beginList()
		}
		switch {
		case needSync && inf.streaming.Load():
			var synced bool
			rv, synced, err = inf.stream(ctx, "", true)
			if errors.Is(err, errStreamingUnsupported) {
				inf.log.Info("API server doesn't support streaming lists; using paginated lists")
				inf.streaming.Store(false)
				continue
			}
			if synced {
				needSync = false
			}
		case needSync:
			if rv, err = inf.relist(ctx); err == nil {
				needSync = false
			}
		default:
			rv, _, err = inf.stream(ctx, rv, false)
		}
		if err == nil {
			b.reset()
			continue
		}
		if ctx.Err() != nil {
			return
		}
		if client.IsGone(err) {
			inf.m.inc("kube_cache_relists_total", "type", inf.ti.String())
			inf.log.Debug("resource version expired; relisting", "err", err)
			needSync = true
			continue
		}
		if !inf.hasSynced.Load() {
			inf.attemptFailed(err)
		}
		inf.m.inc("kube_watch_errors_total", "type", inf.ti.String())
		inf.log.Warn("list or watch failed; retrying", "err", err, "retry", b.d)
		b.sleep(ctx)
	}
}

func (inf *informer[T, P]) query() url.Values {
	q := url.Values{}
	if inf.cfg.selector != "" {
		q.Set("labelSelector", inf.cfg.selector)
	}
	return q
}

func (inf *informer[T, P]) accept(list bool) string {
	switch {
	case inf.pb != nil && inf.ti.metadataOnly && list:
		return protoListAccept
	case inf.pb != nil && inf.ti.metadataOnly:
		return protoWatchAccept
	case inf.pb != nil:
		return protoAccept
	case inf.ti.metadataOnly && list:
		return listAccept
	case inf.ti.metadataOnly:
		return watchAccept
	}
	return ""
}

// protoPlan returns the plan to decode ti from protobuf, or nil if the
// schema doesn't have the kind or a field that ti declares.
func protoPlan(ti *typeInfo, log *slog.Logger) *protobuf.Plan {
	apiVersion, kind := ti.apiVersion, ti.kind
	if ti.metadataOnly {
		apiVersion, kind = "meta.k8s.io/v1", "PartialObjectMetadata"
	} else if ti.custom {
		return nil
	}
	p, err := protobuf.For(ti.goType, apiVersion, kind)
	if err != nil {
		log.Debug("reading as JSON", "reason", err)
		return nil
	}
	return p
}

func (inf *informer[T, P]) path() string {
	return inf.res.path(inf.cfg.namespace, "")
}

// relist does a paginated list and replaces the store's contents.
func (inf *informer[T, P]) relist(ctx context.Context) (string, error) {
	items, bad := map[Key]*T{}, map[Key]*decodeError{}
	add := func(obj *T, err error) error {
		var de *decodeError
		switch {
		case errors.As(err, &de):
			bad[de.meta.Key()] = de
		case err != nil:
			return err
		default:
			items[metaOf[T, P](obj).Key()] = obj
		}
		return nil
	}
	// Decoding each item straight into T is fastest, but the decoder keeps
	// no copy of an item that doesn't decode, whose metadata may not have
	// decoded either. So after such an item, relist lists again, reading
	// each item's bytes first, to name the items that it skips.
	var raw, failed bool
	decode := client.Items{
		JSON: func(dec *json.Decoder) error {
			if raw {
				var b json.RawMessage
				if err := dec.Decode(&b); err != nil {
					return err
				}
				return add(inf.decodeJSON(b))
			}
			obj := new(T)
			if err := dec.Decode(obj); err != nil {
				failed = true
				return err
			}
			inf.normalize(obj)
			return add(obj, nil)
		},
		Proto: func(b []byte) error { return add(inf.decodeProto(b)) },
	}
	list := func() (string, error) {
		clear(items)
		clear(bad)
		rv, err := inf.c.ListItems(ctx, inf.path(), inf.query(), inf.accept(true), inf.cfg.pageSize, decode)
		if client.IsGone(err) {
			// The continue token expired between pages. List everything at once.
			clear(items)
			clear(bad)
			rv, err = inf.c.ListItems(ctx, inf.path(), inf.query(), inf.accept(true), 0, decode)
		}
		return rv, err
	}
	rv, err := list()
	if failed {
		raw = true
		rv, err = list()
	}
	if err != nil {
		return "", err
	}
	inf.replaceAll(items, bad)
	return rv, nil
}

type bookmark struct {
	Metadata struct {
		ResourceVersion string            `json:"resourceVersion"`
		Annotations     map[string]string `json:"annotations"`
	} `json:"metadata"`
}

// stream consumes one watch. With initial set, it asks the server to send
// the current state first (a streaming list) and replaces the store's
// contents when the initial state ends. It returns the last resource version
// seen and whether the store is synced.
func (inf *informer[T, P]) stream(ctx context.Context, rv string, initial bool) (string, bool, error) {
	q := inf.query()
	q.Set("allowWatchBookmarks", "true")
	q.Set("timeoutSeconds", strconv.Itoa(300+rand.IntN(300))) // #nosec G404 -- spreading reconnects needs no cryptographic randomness.
	if initial {
		q.Set("sendInitialEvents", "true")
		q.Set("resourceVersionMatch", "NotOlderThan")
	} else {
		q.Set("resourceVersion", rv)
	}
	w, err := inf.c.Watch(ctx, inf.path(), q, inf.accept(false))
	if err != nil {
		if initial && (client.IsBadRequest(err) || client.IsInvalid(err)) {
			return "", false, errStreamingUnsupported
		}
		return rv, false, err
	}
	defer w.Close()

	var items map[Key]*T
	var bad map[Key]*decodeError
	var first *time.Timer
	var timedOut atomic.Bool
	if initial {
		items, bad = map[Key]*T{}, map[Key]*decodeError{}
		first = time.AfterFunc(firstEventTimeout, func() {
			timedOut.Store(true)
			w.Close()
		})
		defer first.Stop()
	}
	synced := !initial
	for {
		typ, frame, err := w.NextFrame()
		if first != nil {
			first.Stop()
			if err == nil {
				first = nil
			}
		}
		if err != nil {
			switch {
			case first != nil && timedOut.Load():
				return "", false, errStreamingUnsupported
			case errors.Is(err, io.EOF):
				return rv, synced, nil
			case ctx.Err() != nil:
				return rv, synced, ctx.Err()
			default:
				return rv, synced, err
			}
		}
		inf.m.inc("kube_watch_events_total", "type", inf.ti.String())
		switch typ {
		case client.Added, client.Modified, client.Deleted:
			obj, err := inf.decodeEvent(frame, w.Proto)
			var de *decodeError
			var m *ObjectMeta
			switch {
			case err == nil:
				m = metaOf[T, P](obj)
			case errors.As(err, &de):
				m = &de.meta
			default:
				return rv, synced, err
			}
			rv = m.ResourceVersion
			k := m.Key()
			if items != nil {
				delete(items, k)
				delete(bad, k)
				switch {
				case typ == client.Deleted:
				case de != nil:
					bad[k] = de
				default:
					items[k] = obj
				}
				continue
			}
			switch {
			case typ == client.Deleted:
				if old := inf.store.remove(m); old != nil {
					obj = old
				}
				if obj != nil {
					inf.notify(obj, nil, false)
				}
			case de != nil:
				old, fresh := inf.store.skip(de)
				if fresh {
					inf.warnSkipped(de)
				}
				if old != nil {
					inf.notify(old, nil, false)
				}
			default:
				if old := inf.store.put(obj); inf.changed(old, obj) {
					inf.notify(old, obj, false)
				}
			}
		case client.Bookmark:
			var annotations map[string]string
			if w.Proto {
				_, _, raw, err := protobuf.Unwrap(frame)
				if err != nil {
					return rv, synced, err
				}
				om, err := protobuf.Meta(raw)
				if err != nil {
					return rv, synced, err
				}
				rv, annotations = om.ResourceVersion, om.Annotations
			} else {
				var b struct {
					Object bookmark `json:"object"`
				}
				if err := json.Unmarshal(frame, &b); err != nil {
					return rv, synced, err
				}
				rv, annotations = b.Object.Metadata.ResourceVersion, b.Object.Metadata.Annotations
			}
			if items != nil && annotations[client.InitialEventsEndAnnotation] == "true" {
				inf.replaceAll(items, bad)
				items, bad, synced = nil, nil, true
			}
		case client.Error:
			apiErr := client.FrameError(frame)
			if initial && !synced && (client.IsBadRequest(apiErr) || client.IsInvalid(apiErr)) {
				return "", false, errStreamingUnsupported
			}
			return rv, synced, apiErr
		}
	}
}

// decodeEvent decodes the object in a watch event frame straight into T, in
// one pass. Decoding the event into json.RawMessage first and then the
// object nearly doubles the cost. If the object doesn't decode, decodeEvent
// returns what decodeJSON or decodeProto does.
func (inf *informer[T, P]) decodeEvent(frame []byte, proto bool) (*T, error) {
	if proto {
		_, _, raw, err := protobuf.Unwrap(frame)
		if err != nil {
			return nil, err
		}
		return inf.decodeProto(raw)
	}
	e := struct {
		Object *T `json:"object"`
	}{Object: new(T)}
	if err := json.Unmarshal(frame, &e); err != nil {
		var raw struct {
			Object json.RawMessage `json:"object"`
		}
		if json.Unmarshal(frame, &raw) != nil {
			return nil, err
		}
		return inf.decodeJSON(raw.Object)
	}
	inf.normalize(e.Object)
	return e.Object, nil
}

// decodeJSON decodes an object. Any error leaves the object incomplete:
// encoding/json stops at an error from a type's UnmarshalJSON, and returns
// the same kind of error as for a field that it skips. If the object
// doesn't decode but its metadata does, decodeJSON returns a *decodeError.
func (inf *informer[T, P]) decodeJSON(b []byte) (*T, error) {
	obj := new(T)
	if err := json.Unmarshal(b, obj); err != nil {
		var o struct {
			Metadata ObjectMeta `json:"metadata"`
		}
		if json.Unmarshal(b, &o) != nil || o.Metadata.Name == "" {
			return nil, err
		}
		return nil, &decodeError{meta: o.Metadata, err: err}
	}
	inf.normalize(obj)
	return obj, nil
}

// decodeProto is decodeJSON for protobuf.
func (inf *informer[T, P]) decodeProto(b []byte) (*T, error) {
	if inf.pb == nil {
		return nil, errors.New("the server sent protobuf without being asked")
	}
	obj := new(T)
	if err := inf.pb.Unmarshal(b, obj); err != nil {
		m, merr := protobuf.Meta(b)
		if merr != nil || m.Name == "" {
			return nil, err
		}
		return nil, &decodeError{meta: ObjectMeta{Name: m.Name, Namespace: m.Namespace, UID: m.UID, ResourceVersion: m.ResourceVersion}, err: err}
	}
	inf.normalize(obj)
	return obj, nil
}

func (inf *informer[T, P]) warnSkipped(e *decodeError) {
	inf.log.Warn("object doesn't decode; skipping it", "key", e.meta.Key().String(), "resourceVersion", e.meta.ResourceVersion, "err", e.err)
}

func (inf *informer[T, P]) normalize(obj *T) {
	o := P(obj).object()
	o.APIVersion, o.Kind = inf.ti.apiVersion, inf.ti.kind
	if inf.cfg.intern {
		intern(&o.ObjectMeta)
	}
}

type backoff struct {
	d, min, max time.Duration
}

func (b *backoff) reset() { b.d = b.min }

func (b *backoff) sleep(ctx context.Context) {
	d := b.d + time.Duration(rand.Int64N(int64(b.d/5)+1)) // #nosec G404 -- jitter needs no cryptographic randomness.
	t := time.NewTimer(d)
	defer t.Stop()
	select {
	case <-t.C:
	case <-ctx.Done():
	}
	b.d = min(b.d*2, b.max)
}
