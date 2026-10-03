// Package jsonpatch computes and applies JSON patches (RFC 6902) between
// JSON documents decoded into Go values: map[string]any, []any, string,
// json.Number or float64, bool, and nil.
package jsonpatch

import (
	"encoding/json"
	"fmt"
	"reflect"
	"slices"
	"strconv"
	"strings"
)

// Op is one JSON patch operation.
type Op struct {
	Op    string
	Path  string
	Value any
}

// MarshalJSON includes value for add and replace, even when it's null.
func (o Op) MarshalJSON() ([]byte, error) {
	if o.Op == "remove" {
		return json.Marshal(struct {
			Op   string `json:"op"`
			Path string `json:"path"`
		}{o.Op, o.Path})
	}
	return json.Marshal(struct {
		Op    string `json:"op"`
		Path  string `json:"path"`
		Value any    `json:"value"`
	}{o.Op, o.Path, o.Value})
}

// Diff returns operations that turn from into to. Every replace or remove
// targets a path that exists in from, so the patch applies to from as is.
func Diff(from, to any) []Op {
	var ops []Op
	diff("", from, to, &ops)
	return ops
}

func diff(path string, a, b any, ops *[]Op) {
	if reflect.DeepEqual(a, b) {
		return
	}
	am, aok := a.(map[string]any)
	bm, bok := b.(map[string]any)
	if aok && bok {
		for _, k := range sortedKeys(am) {
			if _, ok := bm[k]; !ok {
				*ops = append(*ops, Op{Op: "remove", Path: path + "/" + escape(k)})
			}
		}
		for _, k := range sortedKeys(bm) {
			if av, ok := am[k]; ok {
				diff(path+"/"+escape(k), av, bm[k], ops)
			} else {
				*ops = append(*ops, Op{Op: "add", Path: path + "/" + escape(k), Value: bm[k]})
			}
		}
		return
	}
	as, aok := a.([]any)
	bs, bok := b.([]any)
	if aok && bok {
		n := min(len(as), len(bs))
		for i := range n {
			diff(path+"/"+strconv.Itoa(i), as[i], bs[i], ops)
		}
		for i := n; i < len(bs); i++ {
			*ops = append(*ops, Op{Op: "add", Path: path + "/" + strconv.Itoa(i), Value: bs[i]})
		}
		for i := len(as) - 1; i >= n; i-- {
			*ops = append(*ops, Op{Op: "remove", Path: path + "/" + strconv.Itoa(i)})
		}
		return
	}
	*ops = append(*ops, Op{Op: "replace", Path: path, Value: b})
}

// Overlay returns doc with the changes that turn before into after, where
// before and after are partial views of doc: they hold only some of its
// fields, such as a Go struct that declares a few of them, decoded from doc
// and encoded again. Overlay changes only what differs between before and
// after, so fields that the views leave out keep their values, including
// fields inside list items. List items correspond by position; items that
// after adds come from after, and items it drops are removed.
func Overlay(doc, before, after any) any {
	if reflect.DeepEqual(before, after) {
		return doc
	}
	bm, bok := before.(map[string]any)
	am, aok := after.(map[string]any)
	if bok && aok {
		dm, _ := doc.(map[string]any)
		out := make(map[string]any, len(dm)+len(am))
		for k, v := range dm {
			out[k] = v
		}
		for k, av := range am {
			bv, inBefore := bm[k]
			if inBefore && reflect.DeepEqual(bv, av) {
				continue
			}
			out[k] = Overlay(dm[k], bv, av)
		}
		for k := range bm {
			if _, ok := am[k]; !ok {
				delete(out, k)
			}
		}
		return out
	}
	bs, bok := before.([]any)
	as, aok := after.([]any)
	if bok && aok {
		ds, _ := doc.([]any)
		out := make([]any, len(as))
		for i, av := range as {
			if i < len(bs) && i < len(ds) {
				out[i] = Overlay(ds[i], bs[i], av)
			} else {
				out[i] = av
			}
		}
		return out
	}
	return after
}

// Apply applies ops to doc and returns the result. It supports add, remove,
// and replace, which are what Diff produces.
func Apply(doc any, ops []Op) (any, error) {
	doc = deepCopy(doc)
	for _, op := range ops {
		var err error
		doc, err = apply(doc, op)
		if err != nil {
			return nil, fmt.Errorf("%s %s: %w", op.Op, op.Path, err)
		}
	}
	return doc, nil
}

func apply(doc any, op Op) (any, error) {
	if op.Path == "" {
		if op.Op != "replace" && op.Op != "add" {
			return nil, fmt.Errorf("can't %s the whole document", op.Op)
		}
		return deepCopy(op.Value), nil
	}
	parts := strings.Split(op.Path, "/")[1:]
	for i, p := range parts {
		parts[i] = unescape(p)
	}
	parentPath, last := parts[:len(parts)-1], parts[len(parts)-1]
	parent := doc
	for _, p := range parentPath {
		next, err := child(parent, p)
		if err != nil {
			return nil, err
		}
		parent = next
	}
	switch c := parent.(type) {
	case map[string]any:
		_, exists := c[last]
		switch op.Op {
		case "add":
			c[last] = deepCopy(op.Value)
		case "replace":
			if !exists {
				return nil, fmt.Errorf("member %q doesn't exist", last)
			}
			c[last] = deepCopy(op.Value)
		case "remove":
			if !exists {
				return nil, fmt.Errorf("member %q doesn't exist", last)
			}
			delete(c, last)
		default:
			return nil, fmt.Errorf("unsupported op")
		}
		return doc, nil
	case []any:
		i, err := index(last, len(c), op.Op == "add")
		if err != nil {
			return nil, err
		}
		var out []any
		switch op.Op {
		case "add":
			out = slices.Insert(slices.Clone(c), i, deepCopy(op.Value))
		case "replace":
			out = slices.Clone(c)
			out[i] = deepCopy(op.Value)
		case "remove":
			out = slices.Delete(slices.Clone(c), i, i+1)
		default:
			return nil, fmt.Errorf("unsupported op")
		}
		return set(doc, parentPath, out)
	default:
		return nil, fmt.Errorf("parent of %q isn't an object or array", last)
	}
}

func child(v any, p string) (any, error) {
	switch c := v.(type) {
	case map[string]any:
		n, ok := c[p]
		if !ok {
			return nil, fmt.Errorf("member %q doesn't exist", p)
		}
		return n, nil
	case []any:
		i, err := index(p, len(c), false)
		if err != nil {
			return nil, err
		}
		return c[i], nil
	default:
		return nil, fmt.Errorf("%q isn't inside an object or array", p)
	}
}

func index(p string, n int, adding bool) (int, error) {
	if p == "-" && adding {
		return n, nil
	}
	i, err := strconv.Atoi(p)
	limit := n
	if adding {
		limit = n + 1
	}
	if err != nil || i < 0 || i >= limit {
		return 0, fmt.Errorf("index %q out of range", p)
	}
	return i, nil
}

// set replaces the value at path in doc, which is how array operations,
// which make a new slice, take effect.
func set(doc any, path []string, v any) (any, error) {
	if len(path) == 0 {
		return v, nil
	}
	parent := doc
	for _, p := range path[:len(path)-1] {
		next, err := child(parent, p)
		if err != nil {
			return nil, err
		}
		parent = next
	}
	last := path[len(path)-1]
	switch c := parent.(type) {
	case map[string]any:
		c[last] = v
	case []any:
		i, err := index(last, len(c), false)
		if err != nil {
			return nil, err
		}
		c[i] = v
	}
	return doc, nil
}

func deepCopy(v any) any {
	switch c := v.(type) {
	case map[string]any:
		out := make(map[string]any, len(c))
		for k, x := range c {
			out[k] = deepCopy(x)
		}
		return out
	case []any:
		out := make([]any, len(c))
		for i, x := range c {
			out[i] = deepCopy(x)
		}
		return out
	default:
		return v
	}
}

func sortedKeys(m map[string]any) []string {
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	slices.Sort(keys)
	return keys
}

func escape(s string) string {
	return strings.ReplaceAll(strings.ReplaceAll(s, "~", "~0"), "/", "~1")
}

func unescape(s string) string {
	return strings.ReplaceAll(strings.ReplaceAll(s, "~1", "/"), "~0", "~")
}
