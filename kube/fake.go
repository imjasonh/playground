package kube

import (
	"context"
	"reflect"
	"time"

	"github.com/imjasonh/playground/kube/internal/clone"
)

// Fake returns a context for calling a Reconcile or Finalize method directly
// in a unit test. In it, obj is the object being reconciled, and Get, List,
// Fetch, and Own read from world, which holds pointers to objects. Nothing is
// sent to a cluster; the returned Recorder holds what the reconciler asked
// for.
//
//	ctx, rec := kube.Fake(t.Context(), site, &k8s.Deployment{...})
//	if err := r.Reconcile(ctx, site); err != nil {
//		t.Fatal(err)
//	}
//	deps := kube.Owned[k8s.Deployment](rec)
func Fake[T any, P Resource[T]](ctx context.Context, obj P, world ...any) (context.Context, *Recorder) {
	w := &fakeWorld{byType: map[reflect.Type]*memSource{}, tr: newTracker()}
	for _, o := range append([]any{obj}, world...) {
		w.add(o)
	}
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

// Recorder holds what a reconciler asked for in a Fake context.
type Recorder struct {
	s *scope
}

// RequeueAfter returns the shortest duration passed to RequeueAfter, or zero.
func (r *Recorder) RequeueAfter() time.Duration { return r.s.requeue }

// Err returns the error that canceled the reconcile's context, if any, for
// example a struct that doesn't embed Object.
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

type fakeWorld struct {
	byType map[reflect.Type]*memSource
	tr     *tracker
}

func (w *fakeWorld) src(t reflect.Type, ti *typeInfo) *memSource {
	s := w.byType[t]
	if s == nil {
		s = &memSource{idn: len(w.byType) + 1, objs: map[Key]any{}}
		w.byType[t] = s
	}
	if s.ti == nil {
		s.ti = ti
	}
	return s
}

func (w *fakeWorld) add(o any) {
	if o == nil {
		return
	}
	m := metaOfAny(o)
	w.src(reflect.TypeOf(o).Elem(), nil).objs[m.Key()] = clone.Value(o)
}

func (w *fakeWorld) source(_ context.Context, ti *typeInfo) (source, error) {
	return w.src(ti.goType, ti), nil
}

func (w *fakeWorld) existing(ti *typeInfo) source { return w.src(ti.goType, ti) }

func (w *fakeWorld) children(_ context.Context, _ *core, ti *typeInfo) (source, error) {
	return w.src(ti.goType, ti), nil
}

func (w *fakeWorld) fetch(_ context.Context, ti *typeInfo, k Key) (any, error) {
	return w.src(ti.goType, ti).get(k), nil
}

func (w *fakeWorld) resolve(_ context.Context, ti *typeInfo) (resolved, error) {
	plural := ti.plural
	if plural == "" {
		plural = pluralize(ti.kind)
	}
	return resolved{apiVersion: ti.apiVersion, plural: plural, namespaced: ti.scope != "Cluster"}, nil
}

func (w *fakeWorld) deps() *tracker { return w.tr }

// memSource is an in-memory source for tests.
type memSource struct {
	idn  int
	ti   *typeInfo
	objs map[Key]any
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
