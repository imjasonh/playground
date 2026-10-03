package kube

import (
	"sync"
	"unique"
)

// store holds the latest observed version of every object of one type.
// Stored objects are never mutated; readers that hand objects to user code
// copy them first.
type store[T any, P Resource[T]] struct {
	mu   sync.RWMutex
	objs map[string]map[string]*T // namespace -> name -> object
	n    int
	// ownerKey, when set, is the annotation that children carry to name
	// their owner. The store indexes children by its value.
	ownerKey string
	owners   map[string]map[Key]struct{}
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
	if ns != "" {
		for _, o := range s.objs[ns] {
			if !fn(o) {
				return
			}
		}
		return
	}
	for _, byName := range s.objs {
		for _, o := range byName {
			if !fn(o) {
				return
			}
		}
	}
}

func (s *store[T, P]) byOwner(owner string) []*T {
	s.mu.RLock()
	defer s.mu.RUnlock()
	var out []*T
	for k := range s.owners[owner] {
		if o := s.objs[k.Namespace][k.Name]; o != nil {
			out = append(out, o)
		}
	}
	return out
}

func (s *store[T, P]) put(obj *T) (old *T) {
	s.mu.Lock()
	defer s.mu.Unlock()
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

func (s *store[T, P]) remove(k Key) (old *T) {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.removeLocked(k)
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
func (s *store[T, P]) replace(items map[Key]*T) []change[T] {
	s.mu.Lock()
	defer s.mu.Unlock()
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
