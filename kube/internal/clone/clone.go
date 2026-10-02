// Package clone deep-copies values with reflection.
//
// It replaces generated DeepCopy methods. The first copy of a type builds a
// copier for it and caches it; types without pointers, slices, maps, or
// interfaces copy with a single assignment. Unexported fields are copied
// shallowly.
package clone

import (
	"reflect"
	"sync"
)

// Of returns a deep copy of *v, or nil if v is nil.
func Of[T any](v *T) *T {
	if v == nil {
		return nil
	}
	out := new(T)
	*out = *v
	if c := copierFor(reflect.TypeFor[T]()); c != nil {
		c(reflect.ValueOf(out).Elem(), reflect.ValueOf(v).Elem())
	}
	return out
}

// copier deep-copies src into dst. dst is settable and already holds a
// shallow copy of src.
type copier func(dst, src reflect.Value)

var cache sync.Map // reflect.Type -> copier

func copierFor(t reflect.Type) copier {
	if c, ok := cache.Load(t); ok {
		return c.(copier)
	}
	b := builder{building: map[reflect.Type]*copier{}}
	c := b.build(t)
	cache.Store(t, c)
	return c
}

type builder struct {
	building map[reflect.Type]*copier
}

func (b builder) build(t reflect.Type) copier {
	if p, ok := b.building[t]; ok {
		// t refers to itself. Look up its copier when the copy runs.
		return func(dst, src reflect.Value) {
			if *p != nil {
				(*p)(dst, src)
			}
		}
	}
	slot := new(copier)
	b.building[t] = slot
	defer delete(b.building, t)
	*slot = b.buildKind(t)
	return *slot
}

func (b builder) buildKind(t reflect.Type) copier {
	switch t.Kind() {
	case reflect.Pointer:
		elem := b.build(t.Elem())
		return func(dst, src reflect.Value) {
			if src.IsNil() {
				return
			}
			n := reflect.New(t.Elem())
			n.Elem().Set(src.Elem())
			if elem != nil {
				elem(n.Elem(), src.Elem())
			}
			dst.Set(n)
		}
	case reflect.Slice:
		elem := b.build(t.Elem())
		return func(dst, src reflect.Value) {
			if src.IsNil() {
				return
			}
			n := reflect.MakeSlice(t, src.Len(), src.Len())
			reflect.Copy(n, src)
			if elem != nil {
				for i := range src.Len() {
					elem(n.Index(i), src.Index(i))
				}
			}
			dst.Set(n)
		}
	case reflect.Map:
		elem := b.build(t.Elem())
		return func(dst, src reflect.Value) {
			if src.IsNil() {
				return
			}
			n := reflect.MakeMapWithSize(t, src.Len())
			it := src.MapRange()
			for it.Next() {
				v := it.Value()
				if elem != nil {
					nv := reflect.New(t.Elem()).Elem()
					nv.Set(v)
					elem(nv, v)
					v = nv
				}
				n.SetMapIndex(it.Key(), v)
			}
			dst.Set(n)
		}
	case reflect.Array:
		elem := b.build(t.Elem())
		if elem == nil {
			return nil
		}
		return func(dst, src reflect.Value) {
			for i := range src.Len() {
				elem(dst.Index(i), src.Index(i))
			}
		}
	case reflect.Interface:
		return func(dst, src reflect.Value) {
			if src.IsNil() {
				return
			}
			inner := src.Elem()
			c := copierFor(inner.Type())
			if c == nil {
				return
			}
			nv := reflect.New(inner.Type()).Elem()
			nv.Set(inner)
			c(nv, inner)
			dst.Set(nv)
		}
	case reflect.Struct:
		type field struct {
			index int
			copy  copier
		}
		var fields []field
		for i := range t.NumField() {
			f := t.Field(i)
			if !f.IsExported() {
				continue
			}
			if c := b.build(f.Type); c != nil {
				fields = append(fields, field{i, c})
			}
		}
		if len(fields) == 0 {
			return nil
		}
		return func(dst, src reflect.Value) {
			for _, f := range fields {
				f.copy(dst.Field(f.index), src.Field(f.index))
			}
		}
	default:
		// Scalars copy by assignment. Channels, functions, and unsafe
		// pointers are shared.
		return nil
	}
}
