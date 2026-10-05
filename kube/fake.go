package kube

import (
	"context"
	"encoding/json"
	"errors"
	"log/slog"
	"reflect"
	"time"

	"github.com/imjasonh/playground/kube/internal/clone"
)

// Fake returns a context for calling a Reconcile or Finalize method directly
// in a unit test. In it, obj is the object being reconciled, and Get, List,
// Fetch, and Own read from world, which holds pointers to objects. Nothing is
// sent to a cluster; the returned Recorder holds what the reconciler asked
// for. An error in world is what LastError returns, as if the previous
// reconcile had failed with it.
//
// As in a cluster, a read sees the world's objects of every type of a kind.
// A reconcile that reads a smaller type of Deployment sees each
// k8s.Deployment in world, with only the fields that its type declares. An
// object of the type itself hides one of another type with the same name.
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
	c := &core{name: "test", labels: newLabelKeys("test"), log: slog.Default()}
	if err == nil {
		c.ti = ti
		c.res, _ = w.resolve(ctx, ti)
	}
	ctx, s := newScope(ctx, w, c, P(obj).object().Key())
	for _, o := range world {
		if last, ok := o.(error); ok {
			s.lastErr = last
		}
	}
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

// Events returns the events that the reconciler recorded with Eventf, in
// order.
func (r *Recorder) Events() []Event {
	var out []Event
	for _, e := range r.s.events {
		out = append(out, e.Event)
	}
	return out
}

// Owned returns the objects of type T passed to Own, in order.
func Owned[T any](r *Recorder) []*T { return intentsOf[T](r, intentOwn) }

// Applied returns the objects of type T passed to Apply, in order. The
// framework applies the status of each one too, as Apply describes.
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
	// types holds byType's keys in the order that the world added them.
	types []reflect.Type
	tr    *tracker
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
	if _, ok := o.(error); o == nil || ok {
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
