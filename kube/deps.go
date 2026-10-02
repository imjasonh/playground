package kube

import (
	"sync"

	"github.com/imjasonh/playground/kube/internal/queue"
)

// enqueuer is a controller's work queue, as the tracker sees it.
type enqueuer interface {
	enqueue(k Key, p queue.Priority)
}

// ref is one controller's reconcile of one key.
type ref struct {
	c   enqueuer
	key Key
}

// dep is something a reconcile read: one object by name, or the objects in
// a namespace (all namespaces when ns is empty) that match a selector.
type dep struct {
	src  int
	ns   string
	name string
	sel  string
	list bool
}

type listDep struct {
	sel  selector
	refs map[ref]struct{}
}

// tracker records what each reconcile read, so a change to any of it
// enqueues the reconcile again. It replaces hand-written watch mappings and
// field indexes.
type tracker struct {
	mu    sync.Mutex
	names map[dep]map[ref]struct{}
	lists map[int]map[string]map[dep]*listDep // source -> namespace -> deps
	byRef map[ref]map[dep]struct{}
}

func newTracker() *tracker {
	return &tracker{
		names: map[dep]map[ref]struct{}{},
		lists: map[int]map[string]map[dep]*listDep{},
		byRef: map[ref]map[dep]struct{}{},
	}
}

// add records that r read d. Call it before reading, so a change that lands
// between the read and the call still enqueues r.
func (t *tracker) add(r ref, d dep, sel selector) {
	t.mu.Lock()
	defer t.mu.Unlock()
	deps := t.byRef[r]
	if deps == nil {
		deps = map[dep]struct{}{}
		t.byRef[r] = deps
	}
	if _, ok := deps[d]; ok {
		return
	}
	deps[d] = struct{}{}
	if !d.list {
		refs := t.names[d]
		if refs == nil {
			refs = map[ref]struct{}{}
			t.names[d] = refs
		}
		refs[r] = struct{}{}
		return
	}
	byNS := t.lists[d.src]
	if byNS == nil {
		byNS = map[string]map[dep]*listDep{}
		t.lists[d.src] = byNS
	}
	ds := byNS[d.ns]
	if ds == nil {
		ds = map[dep]*listDep{}
		byNS[d.ns] = ds
	}
	ld := ds[d]
	if ld == nil {
		ld = &listDep{sel: sel, refs: map[ref]struct{}{}}
		ds[d] = ld
	}
	ld.refs[r] = struct{}{}
}

// retain drops the dependencies of r that aren't in keep.
func (t *tracker) retain(r ref, keep map[dep]struct{}) {
	t.mu.Lock()
	defer t.mu.Unlock()
	for d := range t.byRef[r] {
		if _, ok := keep[d]; !ok {
			t.removeLocked(r, d)
		}
	}
	if len(t.byRef[r]) == 0 {
		delete(t.byRef, r)
	}
}

// forget drops every dependency of r.
func (t *tracker) forget(r ref) { t.retain(r, nil) }

func (t *tracker) removeLocked(r ref, d dep) {
	delete(t.byRef[r], d)
	if !d.list {
		if refs := t.names[d]; refs != nil {
			delete(refs, r)
			if len(refs) == 0 {
				delete(t.names, d)
			}
		}
		return
	}
	ds := t.lists[d.src][d.ns]
	if ld := ds[d]; ld != nil {
		delete(ld.refs, r)
		if len(ld.refs) == 0 {
			delete(ds, d)
		}
	}
}

// changed enqueues every reconcile that read an object from source src that
// changed from old to new metadata. Either may be nil.
func (t *tracker) changed(src int, old, new *ObjectMeta) {
	m := new
	if m == nil {
		m = old
	}
	t.mu.Lock()
	var hit []ref
	for r := range t.names[dep{src: src, ns: m.Namespace, name: m.Name}] {
		hit = append(hit, r)
	}
	for _, ns := range [...]string{m.Namespace, ""} {
		for _, ld := range t.lists[src][ns] {
			if (old != nil && ld.sel.matches(old.Labels)) || (new != nil && ld.sel.matches(new.Labels)) {
				for r := range ld.refs {
					hit = append(hit, r)
				}
			}
		}
		if m.Namespace == "" {
			break
		}
	}
	t.mu.Unlock()
	for _, r := range hit {
		r.c.enqueue(r.key, queue.High)
	}
}

// size returns how many dependencies are recorded, for metrics.
func (t *tracker) size() int {
	t.mu.Lock()
	defer t.mu.Unlock()
	n := 0
	for _, deps := range t.byRef {
		n += len(deps)
	}
	return n
}
