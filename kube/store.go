package kube

import (
	"slices"
	"sync"
	"unique"
)

// store holds the latest observed version of every object of one type.
// Stored objects are never mutated; readers that hand objects to user code
// copy them first.
//
// Reads return what this process's own writes stored in place of the
// watched object, until the watch delivers the event for the write.
type store[T any, P Resource[T]] struct {
	mu   sync.RWMutex
	objs map[string]map[string]*T // namespace -> name -> object
	n    int
	// ownerKey, when set, is the annotation that children carry to name
	// their owner. The store indexes children by its value.
	ownerKey string
	owners   map[string]map[Key]struct{}
	writes   map[Key]*ownWrite[T]
	flights  map[Key][]*flight
}

// ownWrite is what one of this process's writes stored. obj is nil when
// the object is gone, or doesn't match the store's label selector.
type ownWrite[T any] struct {
	obj *T
	// rv is the write's resource version. It's empty when the object is
	// gone, because a delete's response doesn't always carry the version of
	// the deletion, and then only the object's removal resolves the write.
	rv  string
	uid string
}

// flight is a write in progress.
type flight struct {
	key Key
	// seen holds the resource version that the store held for the key when
	// the write began, and those that its watch delivered since.
	seen []string
	// stale is set when the write's place among the object's versions is
	// unknown: a list replaced the store, or another write by this process
	// to the same object overlapped it.
	stale bool
}

type change[T any] struct {
	old, new *T
}

func metaOf[T any, P Resource[T]](obj *T) *ObjectMeta {
	return &P(obj).object().ObjectMeta
}

func (s *store[T, P]) get(k Key) *T {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.getLocked(k)
}

func (s *store[T, P]) getLocked(k Key) *T {
	if w, ok := s.writes[k]; ok {
		return w.obj
	}
	return s.objs[k.Namespace][k.Name]
}

func (s *store[T, P]) len() int {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.n
}

// each calls fn for every object in namespace ns, or in all namespaces when
// ns is empty, until fn returns false.
func (s *store[T, P]) each(ns string, fn func(*T) bool) {
	s.mu.RLock()
	defer s.mu.RUnlock()
	for k, w := range s.writes {
		if w.obj != nil && (ns == "" || k.Namespace == ns) && !fn(w.obj) {
			return
		}
	}
	visit := func(ns string, byName map[string]*T) bool {
		for name, o := range byName {
			if _, ok := s.writes[Key{Namespace: ns, Name: name}]; ok {
				continue
			}
			if !fn(o) {
				return false
			}
		}
		return true
	}
	if ns != "" {
		visit(ns, s.objs[ns])
		return
	}
	for ns, byName := range s.objs {
		if !visit(ns, byName) {
			return
		}
	}
}

func (s *store[T, P]) byOwner(owner string) []*T {
	s.mu.RLock()
	defer s.mu.RUnlock()
	var out []*T
	for k := range s.owners[owner] {
		if _, ok := s.writes[k]; ok {
			continue
		}
		if o := s.objs[k.Namespace][k.Name]; o != nil {
			out = append(out, o)
		}
	}
	for _, w := range s.writes {
		if w.obj != nil && metaOf[T, P](w.obj).Annotations[s.ownerKey] == owner {
			out = append(out, w.obj)
		}
	}
	return out
}

// put stores obj from a watch event.
func (s *store[T, P]) put(obj *T) (old *T) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.observe(metaOf[T, P](obj), false)
	return s.putLocked(obj)
}

func (s *store[T, P]) putLocked(obj *T) (old *T) {
	m := metaOf[T, P](obj)
	if s.objs == nil {
		s.objs = map[string]map[string]*T{}
	}
	byName := s.objs[m.Namespace]
	if byName == nil {
		byName = map[string]*T{}
		s.objs[m.Namespace] = byName
	}
	old = byName[m.Name]
	if old == nil {
		s.n++
	} else {
		s.unindex(old)
	}
	byName[m.Name] = obj
	s.index(obj)
	return old
}

// remove deletes the object that obj, from a watch event, names.
func (s *store[T, P]) remove(obj *T) (old *T) {
	s.mu.Lock()
	defer s.mu.Unlock()
	m := metaOf[T, P](obj)
	s.observe(m, true)
	return s.removeLocked(m.Key())
}

func (s *store[T, P]) removeLocked(k Key) (old *T) {
	byName := s.objs[k.Namespace]
	old = byName[k.Name]
	if old == nil {
		return nil
	}
	delete(byName, k.Name)
	if len(byName) == 0 {
		delete(s.objs, k.Namespace)
	}
	s.n--
	s.unindex(old)
	return old
}

// replace makes items the store's contents and returns the differences:
// objects that were added, changed (by resource version), or removed.
//
// A list's resource versions don't order it against this process's writes,
// so replace forgets what those writes stored, and writes still in progress
// leave nothing in the store when they end.
func (s *store[T, P]) replace(items map[Key]*T) []change[T] {
	s.mu.Lock()
	defer s.mu.Unlock()
	clear(s.writes)
	for _, fs := range s.flights {
		for _, f := range fs {
			f.stale = true
		}
	}
	var changes []change[T]
	for _, byName := range s.objs {
		for name, old := range byName {
			k := Key{Namespace: metaOf[T, P](old).Namespace, Name: name}
			if _, ok := items[k]; !ok {
				changes = append(changes, change[T]{old: old})
			}
		}
	}
	for _, c := range changes {
		s.removeLocked(metaOf[T, P](c.old).Key())
	}
	for _, obj := range items {
		old := s.putLocked(obj)
		if old == nil || metaOf[T, P](old).ResourceVersion != metaOf[T, P](obj).ResourceVersion {
			changes = append(changes, change[T]{old: old, new: obj})
		}
	}
	return changes
}

// begin records that this process is about to write the object at k.
func (s *store[T, P]) begin(k Key) *flight {
	s.mu.Lock()
	defer s.mu.Unlock()
	f := &flight{key: k}
	if o := s.objs[k.Namespace][k.Name]; o != nil {
		f.seen = []string{metaOf[T, P](o).ResourceVersion}
	}
	for _, g := range s.flights[k] {
		g.stale, f.stale = true, true
	}
	if s.flights == nil {
		s.flights = map[Key][]*flight{}
	}
	s.flights[k] = append(s.flights[k], f)
	return f
}

// end records what the write that began with f stored. w is nil if the
// write failed or its response didn't say.
//
// Not every API server orders resource versions, so end only tests them for
// equality, and only against versions of the key from this store's watch. A
// write's response carries the same resource version as the watch event
// that the write causes, or, if the write changed nothing, as the object's
// latest event. A watch delivers one key's events in order. So if the store
// held w.rv when the write began, or its watch delivered w.rv since, the
// store holds this write or a later version. Otherwise the event is still
// to come, and reads return w until it arrives.
func (s *store[T, P]) end(f *flight, w *ownWrite[T]) {
	s.mu.Lock()
	defer s.mu.Unlock()
	if fs := slices.DeleteFunc(s.flights[f.key], func(g *flight) bool { return g == f }); len(fs) > 0 {
		s.flights[f.key] = fs
	} else {
		delete(s.flights, f.key)
	}
	switch {
	case w == nil, f.stale, w.rv != "" && slices.Contains(f.seen, w.rv):
		return
	case w.obj == nil:
		// If the store doesn't show the object, there's nothing to hide,
		// and the event that would resolve the write might never come.
		if o := s.getLocked(f.key); o == nil || metaOf[T, P](o).UID != w.uid {
			return
		}
	}
	if s.writes == nil {
		s.writes = map[Key]*ownWrite[T]{}
	}
	s.writes[f.key] = w
}

// observe notes a watch event about the object that m describes. removed is
// set when the event removes the object from the store. The event resolves
// a write with its resource version, and the removal of an object resolves
// a write that hides it.
func (s *store[T, P]) observe(m *ObjectMeta, removed bool) {
	k := m.Key()
	for _, f := range s.flights[k] {
		f.seen = append(f.seen, m.ResourceVersion)
	}
	w, ok := s.writes[k]
	if ok && (w.rv != "" && w.rv == m.ResourceVersion || w.obj == nil && removed && w.uid == m.UID) {
		delete(s.writes, k)
	}
}

func (s *store[T, P]) index(obj *T) {
	if s.ownerKey == "" {
		return
	}
	m := metaOf[T, P](obj)
	owner, ok := m.Annotations[s.ownerKey]
	if !ok {
		return
	}
	if s.owners == nil {
		s.owners = map[string]map[Key]struct{}{}
	}
	set := s.owners[owner]
	if set == nil {
		set = map[Key]struct{}{}
		s.owners[owner] = set
	}
	set[m.Key()] = struct{}{}
}

func (s *store[T, P]) unindex(obj *T) {
	if s.ownerKey == "" {
		return
	}
	m := metaOf[T, P](obj)
	owner, ok := m.Annotations[s.ownerKey]
	if !ok {
		return
	}
	if set := s.owners[owner]; set != nil {
		delete(set, m.Key())
		if len(set) == 0 {
			delete(s.owners, owner)
		}
	}
}

// intern replaces strings that repeat across many objects (namespaces, label
// keys and values, annotation keys, owner kinds, finalizers) with one shared
// copy each.
func intern(m *ObjectMeta) {
	m.Namespace = internString(m.Namespace)
	if len(m.Labels) > 0 {
		labels := make(map[string]string, len(m.Labels))
		for k, v := range m.Labels {
			labels[internString(k)] = internString(v)
		}
		m.Labels = labels
	}
	if len(m.Annotations) > 0 {
		anns := make(map[string]string, len(m.Annotations))
		for k, v := range m.Annotations {
			anns[internString(k)] = v
		}
		m.Annotations = anns
	}
	for i := range m.OwnerReferences {
		r := &m.OwnerReferences[i]
		r.APIVersion, r.Kind = internString(r.APIVersion), internString(r.Kind)
	}
	for i, f := range m.Finalizers {
		m.Finalizers[i] = internString(f)
	}
}

func internString(s string) string {
	if s == "" {
		return s
	}
	return unique.Make(s).Value()
}
