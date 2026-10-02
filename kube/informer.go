package kube

import (
	"context"
	"encoding/json"
	"errors"
	"io"
	"log/slog"
	"math/rand/v2"
	"net/url"
	"slices"
	"strconv"
	"sync"
	"sync/atomic"
	"time"

	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/clone"
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
}

const (
	listAccept  = "application/json;as=PartialObjectMetadataList;g=meta.k8s.io;v=v1,application/json"
	watchAccept = "application/json;as=PartialObjectMetadata;g=meta.k8s.io;v=v1,application/json"
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
	warned      atomic.Bool
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

func (inf *informer[T, P]) replaceAll(items map[Key]*T) {
	initial := !inf.hasSynced.Load()
	changes := inf.store.replace(items)
	inf.hasSynced.Store(true)
	inf.syncOnce.Do(func() { close(inf.synced) })
	inf.attemptOnce.Do(func() { close(inf.attempted) })
	inf.log.Debug("cache synced", "objects", len(items), "changes", len(changes))
	for _, c := range changes {
		inf.notify(c.old, c.new, initial)
	}
}

func (inf *informer[T, P]) run(ctx context.Context) {
	b := backoff{min: 800 * time.Millisecond, max: 30 * time.Second}
	b.reset()
	rv, needSync := "", true
	for ctx.Err() == nil {
		var err error
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
	if !inf.ti.metadataOnly {
		return ""
	}
	if list {
		return listAccept
	}
	return watchAccept
}

func (inf *informer[T, P]) path() string {
	return inf.res.path(inf.cfg.namespace, "")
}

// relist does a paginated list and replaces the store's contents.
func (inf *informer[T, P]) relist(ctx context.Context) (string, error) {
	items := map[Key]*T{}
	decode := func(dec *json.Decoder) error {
		obj := new(T)
		if err := inf.check(dec.Decode(obj)); err != nil {
			return err
		}
		inf.normalize(obj)
		items[metaOf[T, P](obj).Key()] = obj
		return nil
	}
	rv, err := inf.c.ListAll(ctx, inf.path(), inf.query(), inf.accept(true), inf.cfg.pageSize, decode)
	if client.IsGone(err) {
		// The continue token expired between pages. List everything at once.
		clear(items)
		rv, err = inf.c.ListAll(ctx, inf.path(), inf.query(), inf.accept(true), 0, decode)
	}
	if err != nil {
		return "", err
	}
	inf.replaceAll(items)
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
	var first *time.Timer
	var timedOut atomic.Bool
	if initial {
		items = map[Key]*T{}
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
			obj, err := inf.decodeEvent(frame)
			if err != nil {
				return rv, synced, err
			}
			m := metaOf[T, P](obj)
			rv = m.ResourceVersion
			if items != nil {
				if typ == client.Deleted {
					delete(items, m.Key())
				} else {
					items[m.Key()] = obj
				}
				continue
			}
			if typ == client.Deleted {
				if old := inf.store.remove(m.Key()); old != nil {
					obj = old
				}
				inf.notify(obj, nil, false)
				continue
			}
			old := inf.store.put(obj)
			inf.notify(old, obj, false)
		case client.Bookmark:
			var b struct {
				Object bookmark `json:"object"`
			}
			if err := json.Unmarshal(frame, &b); err != nil {
				return rv, synced, err
			}
			rv = b.Object.Metadata.ResourceVersion
			if items != nil && b.Object.Metadata.Annotations[client.InitialEventsEndAnnotation] == "true" {
				inf.replaceAll(items)
				items, synced = nil, true
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
// object nearly doubles the cost.
func (inf *informer[T, P]) decodeEvent(frame []byte) (*T, error) {
	e := struct {
		Object *T `json:"object"`
	}{Object: new(T)}
	if err := inf.check(json.Unmarshal(frame, &e)); err != nil {
		return nil, err
	}
	inf.normalize(e.Object)
	return e.Object, nil
}

// check tolerates a field whose JSON type doesn't match the Go type: the rest
// of the object still decodes, and the mismatch is logged once per cache.
func (inf *informer[T, P]) check(err error) error {
	var te *json.UnmarshalTypeError
	if errors.As(err, &te) {
		if inf.warned.CompareAndSwap(false, true) {
			inf.log.Warn("a field's JSON type doesn't match its Go type; the field is left empty", "err", err)
		}
		return nil
	}
	return err
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
