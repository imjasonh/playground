package kube

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"reflect"
	"slices"
	"time"

	"github.com/imjasonh/playground/kube/internal/clone"
)

// Fake returns a context for calling a Reconcile or Finalize method directly
// in a unit test. In it, obj is the object being reconciled, and Get, List,
// Fetch, and Own read from world, which holds pointers to objects. Nothing is
// sent to a cluster; the returned Recorder holds what the reconciler asked
// for.
//
// As in a cluster, a read sees the world's objects of every type of a kind.
// A reconcile that reads a smaller type of Deployment sees each
// k8s.Deployment in world, with only the fields that its type declares. An
// object of the type itself hides one of another type with the same name.
//
// World can also hold FakeTokens for ReviewToken to accept. RequestToken
// returns the tokens "fake-token-1", "fake-token-2", and so on, for the
// service account test in the namespace default, and ReviewToken accepts
// them for the requested audience. Trigger queues a reconcile of an object
// that world holds, which Triggered reports, unless world holds
// FakeStandby. To test a Serve handler, use FakeRequest instead.
//
//	ctx, rec := kube.Fake(t.Context(), site, &k8s.Deployment{...})
//	if err := r.Reconcile(ctx, site); err != nil {
//		t.Fatal(err)
//	}
//	deps := kube.Owned[k8s.Deployment](rec)
func Fake[T any, P Resource[T]](ctx context.Context, obj P, world ...any) (context.Context, *Recorder) {
	w := newFakeWorld(append([]any{obj}, world...))
	ti, err := typeInfoFor[T, P]()
	c := &core{name: "test", labels: newLabelKeys("test")}
	if err == nil {
		c.ti = ti
		c.res, _ = w.resolve(ctx, ti)
	}
	ctx, s := newScope(ctx, w, c, P(obj).object().Key())
	if err != nil {
		s.fail(err)
	}
	return ctx, &Recorder{s: s}
}

// FakeRequest returns a context for one request to a Serve handler in a unit
// test. In it, Get, List, Fetch, ReviewToken, RequestToken, and Trigger use
// world, as in a Fake context. As in a cluster, the handler can only read. A
// call of Own, Apply, Delete, or RequeueAfter cancels the context, and the
// returned Recorder's Err returns the error.
//
//	ctx, rec := kube.FakeRequest(t.Context(), probe, kube.FakeToken{...})
//	req := httptest.NewRequest("POST", "/probes/team/api", nil).WithContext(ctx)
//	handler.ServeHTTP(httptest.NewRecorder(), req)
//	if err := rec.Err(); err != nil {
//		t.Error(err)
//	}
func FakeRequest(ctx context.Context, world ...any) (context.Context, *Recorder) {
	ctx, s := newWebhookScope(ctx, newFakeWorld(world))
	return ctx, &Recorder{s: s}
}

// FakeStandby, in the world of a Fake or FakeRequest context, makes the
// context act as a replica that reconciles no objects, such as one that
// doesn't hold the lease, so Trigger returns false.
type FakeStandby struct{}

// Recorder holds what a reconciler or a handler asked for in a Fake or
// FakeRequest context.
type Recorder struct {
	s *scope
}

// RequeueAfter returns the shortest duration passed to RequeueAfter, or zero.
func (r *Recorder) RequeueAfter() time.Duration { return r.s.requeue }

// Err returns the error that canceled the context, if any, for example
// because a reconciled struct doesn't embed Object, or because a handler
// called Apply.
func (r *Recorder) Err() error { return r.s.err }

// Owned returns the objects of type T passed to Own, in order.
func Owned[T any](r *Recorder) []*T { return intentsOf[T](r, intentOwn) }

// Applied returns the objects of type T passed to Apply, in order.
func Applied[T any](r *Recorder) []*T { return intentsOf[T](r, intentApply) }

// Deleted returns the objects of type T passed to Delete, in order.
func Deleted[T any](r *Recorder) []*T { return intentsOf[T](r, intentDelete) }

func intentsOf[T any](r *Recorder, kind intentKind) []*T {
	var out []*T
	for _, in := range r.s.intents {
		if o, ok := in.obj.(*T); ok && in.kind == kind {
			out = append(out, o)
		}
	}
	return out
}

// Triggered returns the keys of the objects of type T that Trigger queued a
// reconcile for, in order.
func Triggered[T any](r *Recorder) []Key {
	var out []Key
	for _, t := range r.s.w.(*fakeWorld).triggers {
		if t.t == reflect.TypeFor[T]() {
			out = append(out, t.key)
		}
	}
	return out
}

// FakeToken is a bearer token for ReviewToken to accept in a Fake context.
// It's valid for Audiences, or, when Audiences is empty, only for the API
// server's audience, "https://kubernetes.default.svc", like a token that
// the API server issues without audiences.
type FakeToken struct {
	Token     string
	User      UserInfo
	Audiences []string
}

type fakeWorld struct {
	byType map[reflect.Type]*memSource
	// types holds byType's keys in the order that the world added them.
	types []reflect.Type
	tr    *tracker
	// tokens are the tokens that ReviewToken accepts, and requested counts
	// the calls of RequestToken.
	tokens    []FakeToken
	requested int
	triggers  []triggered
	// standby is set when the world holds FakeStandby.
	standby bool
}

func newFakeWorld(objs []any) *fakeWorld {
	w := &fakeWorld{byType: map[reflect.Type]*memSource{}, tr: newTracker()}
	for _, o := range objs {
		w.add(o)
	}
	return w
}

type triggered struct {
	t   reflect.Type
	key Key
}

func (w *fakeWorld) src(t reflect.Type, ti *typeInfo) *memSource {
	s := w.byType[t]
	if s == nil {
		s = &memSource{idn: len(w.byType) + 1, objs: map[Key]any{}}
		w.byType[t] = s
		w.types = append(w.types, t)
	}
	if s.ti == nil {
		s.ti = ti
	}
	return s
}

// read returns the source for reads of ti. The first read of a type copies
// in the world's objects of other types of the same kind, converted to ti
// through JSON, except where an object of ti has the same name.
func (w *fakeWorld) read(ti *typeInfo) *memSource {
	s := w.src(ti.goType, ti)
	if s.merged {
		return s
	}
	s.merged = true
	for _, t := range w.types {
		if t == ti.goType {
			continue
		}
		if oti, err := parseType(t); err != nil || oti.apiVersion != ti.apiVersion || oti.kind != ti.kind {
			continue
		}
		for k, o := range w.byType[t].objs {
			if _, ok := s.objs[k]; ok {
				continue
			}
			b, err := json.Marshal(o)
			if err != nil {
				continue
			}
			v := reflect.New(ti.goType)
			// Like the cache, tolerate fields whose JSON type doesn't match.
			var te *json.UnmarshalTypeError
			if err := json.Unmarshal(b, v.Interface()); err != nil && !errors.As(err, &te) {
				continue
			}
			s.objs[k] = v.Interface()
		}
	}
	return s
}

func (w *fakeWorld) add(o any) {
	if o == nil {
		return
	}
	switch t := o.(type) {
	case FakeToken:
		w.tokens = append(w.tokens, *clone.Of(&t))
		return
	case *FakeToken:
		w.tokens = append(w.tokens, *clone.Of(t))
		return
	case FakeStandby, *FakeStandby:
		w.standby = true
		return
	}
	m := metaOfAny(o)
	w.src(reflect.TypeOf(o).Elem(), nil).objs[m.Key()] = clone.Value(o)
}

func (w *fakeWorld) source(_ context.Context, ti *typeInfo) (source, error) {
	return w.read(ti), nil
}

func (w *fakeWorld) existing(ti *typeInfo) source { return w.read(ti) }

func (w *fakeWorld) children(_ context.Context, _ *core, ti *typeInfo) (source, error) {
	return w.read(ti), nil
}

func (w *fakeWorld) fetch(_ context.Context, ti *typeInfo, k Key) (any, error) {
	return w.read(ti).get(k), nil
}

func (w *fakeWorld) resolve(_ context.Context, ti *typeInfo) (resolved, error) {
	plural := ti.plural
	if plural == "" {
		plural = pluralize(ti.kind)
	}
	return resolved{apiVersion: ti.apiVersion, plural: plural, namespaced: ti.scope != "Cluster"}, nil
}

func (w *fakeWorld) deps() *tracker { return w.tr }

// fakeAPIAudience is the API server's audience in a Fake context.
const fakeAPIAudience = "https://kubernetes.default.svc"

func (w *fakeWorld) reviewToken(_ context.Context, token string, want []string) (TokenReview, error) {
	for _, t := range w.tokens {
		if t.Token != token {
			continue
		}
		have := t.Audiences
		if len(have) == 0 {
			have = []string{fakeAPIAudience}
		}
		var both []string
		for _, a := range want {
			if slices.Contains(have, a) {
				both = append(both, a)
			}
		}
		if len(both) == 0 {
			return TokenReview{Error: fmt.Sprintf("token audiences %q is invalid for the target audiences %q", have, want)}, nil
		}
		return TokenReview{Authenticated: true, User: *clone.Of(&t.User), Audiences: both}, nil
	}
	return TokenReview{Error: "invalid bearer token"}, nil
}

func (w *fakeWorld) requestToken(_ context.Context, audience string) (string, time.Time, error) {
	w.requested++
	t := FakeToken{
		Token: fmt.Sprintf("fake-token-%d", w.requested),
		User: UserInfo{
			Username: "system:serviceaccount:default:test",
			Groups:   []string{"system:serviceaccounts", "system:serviceaccounts:default", "system:authenticated"},
		},
		Audiences: []string{audience},
	}
	w.tokens = append(w.tokens, t)
	return t.Token, time.Now().Add(time.Hour), nil
}

func (w *fakeWorld) trigger(ti *typeInfo, k Key) bool {
	if w.standby {
		return false
	}
	if res, _ := w.resolve(context.Background(), ti); !res.namespaced {
		k.Namespace = ""
	}
	if w.read(ti).peek(k) == nil {
		return false
	}
	w.triggers = append(w.triggers, triggered{t: ti.goType, key: k})
	return true
}

// memSource is an in-memory source for tests.
type memSource struct {
	idn  int
	ti   *typeInfo
	objs map[Key]any
	// merged reports whether objs holds the world's objects of other types
	// of the same kind.
	merged bool
}

func (s *memSource) id() int                          { return s.idn }
func (s *memSource) typeInfo() *typeInfo              { return s.ti }
func (s *memSource) waitSynced(context.Context) error { return nil }
func (s *memSource) owned(string) []any               { return nil }
func (s *memSource) peek(k Key) any                   { return s.objs[k] }
func (s *memSource) get(k Key) any {
	o, ok := s.objs[k]
	if !ok {
		return nil
	}
	return clone.Value(o)
}

func (s *memSource) list(namespace string, sel selector) []any {
	var out []any
	for k, o := range s.objs {
		if (namespace == "" || k.Namespace == namespace) && sel.matches(metaOfAny(o).Labels) {
			out = append(out, clone.Value(o))
		}
	}
	return out
}
