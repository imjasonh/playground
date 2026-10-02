// Package schema generates OpenAPI v3 schemas and CustomResourceDefinitions
// from Go types.
//
// Field names come from encoding/json struct tags. A field is required when
// its json tag has neither omitempty nor omitzero and it isn't a pointer,
// slice, map, or interface. Other struct tags add validation and display
// hints:
//
//	kube:"min=1,max=10"           numeric bounds (minimum, maximum)
//	kube:"minLength=1,maxLength=63"
//	kube:"minItems=1,maxItems=5"
//	kube:"enum=A|AAAA|CNAME"      allowed values
//	kube:"default=80"             server-side default
//	kube:"format=hostname"        OpenAPI string format
//	kube:"immutable"              rejects changes after creation (CEL rule)
//	kube:"optional" / "required"  overrides the json tag rule
//	kube:"listType=map,listMapKey=name"
//	kube:"column=Ready"           adds a kubectl get column for the field
//	pattern:"^[a-z]+$"            regular expression for strings
//	doc:"..."                     description shown by kubectl explain
//
// A type can supply its own schema with an OpenAPISchema() map[string]any
// method, and an element type can make its slices server-side-apply maps
// keyed by some fields with a ListMapKeys() []string method.
package schema

import (
	"encoding/json"
	"fmt"
	"reflect"
	"slices"
	"strconv"
	"strings"
	"time"
)

// Column is an additional printer column for kubectl get.
type Column struct {
	Name     string `json:"name"`
	Type     string `json:"type"`
	JSONPath string `json:"jsonPath"`
}

// Result is a generated schema.
type Result struct {
	// Schema is the OpenAPI v3 schema of the whole object.
	Schema map[string]any
	// Columns are printer columns requested with the column tag.
	Columns []Column
	// HasStatus is true when the object has a top-level status field.
	HasStatus bool
}

type schemaer interface{ OpenAPISchema() map[string]any }

type listMapKeyer interface{ ListMapKeys() []string }

var (
	timeType        = reflect.TypeFor[time.Time]()
	rawMessageType  = reflect.TypeFor[json.RawMessage]()
	schemaerType    = reflect.TypeFor[schemaer]()
	listMapKeyType  = reflect.TypeFor[listMapKeyer]()
	topLevelStrings = []string{"apiVersion", "kind"}
)

// Generate returns the schema for the struct type t, which describes a
// whole Kubernetes object. The apiVersion, kind, and metadata fields get the
// minimal schemas that CustomResourceDefinitions allow.
func Generate(t reflect.Type) (*Result, error) {
	if t.Kind() != reflect.Struct {
		return nil, fmt.Errorf("schema: %v is not a struct", t)
	}
	g := &gen{seen: map[reflect.Type]bool{}}
	s, err := g.schema(t, "", fieldTags{})
	if err != nil {
		return nil, err
	}
	props, _ := s["properties"].(map[string]any)
	if props == nil {
		props = map[string]any{}
		s["properties"] = props
	}
	for _, k := range topLevelStrings {
		props[k] = map[string]any{"type": "string"}
	}
	props["metadata"] = map[string]any{"type": "object"}
	if req, ok := s["required"].([]string); ok {
		req = slices.DeleteFunc(req, func(k string) bool {
			return k == "metadata" || slices.Contains(topLevelStrings, k)
		})
		if len(req) == 0 {
			delete(s, "required")
		} else {
			s["required"] = req
		}
	}
	_, hasStatus := props["status"]
	return &Result{Schema: s, Columns: g.columns, HasStatus: hasStatus}, nil
}

type gen struct {
	seen    map[reflect.Type]bool
	columns []Column
}

type fieldTags struct {
	opts    map[string]string
	pattern string
	doc     string
}

func parseTags(f reflect.StructField) fieldTags {
	ft := fieldTags{opts: map[string]string{}, pattern: f.Tag.Get("pattern"), doc: f.Tag.Get("doc")}
	for part := range strings.SplitSeq(f.Tag.Get("kube"), ",") {
		part = strings.TrimSpace(part)
		if part == "" {
			continue
		}
		k, v, _ := strings.Cut(part, "=")
		ft.opts[k] = v
	}
	return ft
}

func (g *gen) schema(t reflect.Type, path string, tags fieldTags) (map[string]any, error) {
	s, err := g.typeSchema(t, path)
	if err != nil {
		return nil, err
	}
	return s, applyTags(s, t, tags)
}

func (g *gen) typeSchema(t reflect.Type, path string) (map[string]any, error) {
	if t.Implements(schemaerType) {
		return reflect.Zero(t).Interface().(schemaer).OpenAPISchema(), nil
	}
	if t.Kind() != reflect.Pointer && reflect.PointerTo(t).Implements(schemaerType) {
		return reflect.New(t).Interface().(schemaer).OpenAPISchema(), nil
	}
	switch t {
	case timeType:
		return map[string]any{"type": "string", "format": "date-time"}, nil
	case rawMessageType:
		return map[string]any{"x-kubernetes-preserve-unknown-fields": true}, nil
	}
	switch t.Kind() {
	case reflect.Bool:
		return map[string]any{"type": "boolean"}, nil
	case reflect.Int8, reflect.Int16, reflect.Int32, reflect.Uint8, reflect.Uint16:
		return map[string]any{"type": "integer", "format": "int32"}, nil
	case reflect.Int, reflect.Int64, reflect.Uint, reflect.Uint32, reflect.Uint64:
		return map[string]any{"type": "integer", "format": "int64"}, nil
	case reflect.Float32, reflect.Float64:
		return map[string]any{"type": "number"}, nil
	case reflect.String:
		return map[string]any{"type": "string"}, nil
	case reflect.Pointer:
		return g.typeSchema(t.Elem(), path)
	case reflect.Interface:
		return map[string]any{"x-kubernetes-preserve-unknown-fields": true}, nil
	case reflect.Slice, reflect.Array:
		if t.Elem().Kind() == reflect.Uint8 {
			return map[string]any{"type": "string", "format": "byte"}, nil
		}
		items, err := g.typeSchema(t.Elem(), path+"[*]")
		if err != nil {
			return nil, err
		}
		s := map[string]any{"type": "array", "items": items}
		if keys := listMapKeys(t.Elem()); keys != nil {
			s["x-kubernetes-list-type"] = "map"
			s["x-kubernetes-list-map-keys"] = keys
		}
		return s, nil
	case reflect.Map:
		if t.Key().Kind() != reflect.String {
			return nil, fmt.Errorf("schema: %s: map keys must be strings, not %v", path, t.Key())
		}
		if t.Elem().Kind() == reflect.Interface {
			return map[string]any{"type": "object", "x-kubernetes-preserve-unknown-fields": true}, nil
		}
		elem, err := g.typeSchema(t.Elem(), path+".*")
		if err != nil {
			return nil, err
		}
		return map[string]any{"type": "object", "additionalProperties": elem}, nil
	case reflect.Struct:
		if g.seen[t] {
			return nil, fmt.Errorf("schema: %s: recursive type %v is not supported in a CustomResourceDefinition", path, t)
		}
		g.seen[t] = true
		defer delete(g.seen, t)
		props := map[string]any{}
		var required []string
		if err := g.fields(t, path, props, &required); err != nil {
			return nil, err
		}
		s := map[string]any{"type": "object"}
		if len(props) > 0 {
			s["properties"] = props
		}
		if len(required) > 0 {
			slices.Sort(required)
			s["required"] = required
		}
		return s, nil
	default:
		return nil, fmt.Errorf("schema: %s: unsupported type %v", path, t)
	}
}

func (g *gen) fields(t reflect.Type, path string, props map[string]any, required *[]string) error {
	for i := range t.NumField() {
		f := t.Field(i)
		name, omit, skip := jsonName(f)
		if skip {
			continue
		}
		if f.Anonymous && name == "" {
			ft := f.Type
			if ft.Kind() == reflect.Pointer {
				ft = ft.Elem()
			}
			if ft.Kind() == reflect.Struct {
				if err := g.fields(ft, path, props, required); err != nil {
					return err
				}
				continue
			}
		}
		if !f.IsExported() {
			continue
		}
		if name == "" {
			name = f.Name
		}
		tags := parseTags(f)
		fpath := path + "." + name
		s, err := g.schema(f.Type, fpath, tags)
		if err != nil {
			return err
		}
		props[name] = s
		if col, ok := tags.opts["column"]; ok {
			if col == "" {
				col = f.Name
			}
			g.columns = append(g.columns, Column{Name: col, Type: columnType(f.Type, s), JSONPath: fpath})
		}
		_, optional := tags.opts["optional"]
		_, forced := tags.opts["required"]
		k := f.Type.Kind()
		nilable := k == reflect.Pointer || k == reflect.Slice || k == reflect.Map || k == reflect.Interface
		if forced || (!omit && !nilable && !optional) {
			*required = append(*required, name)
		}
	}
	return nil
}

// listMapKeys returns the keys that a ListMapKeys method on elem declares, or
// nil.
func listMapKeys(elem reflect.Type) []string {
	if elem.Kind() == reflect.Pointer {
		elem = elem.Elem()
	}
	if !reflect.PointerTo(elem).Implements(listMapKeyType) {
		return nil
	}
	return reflect.New(elem).Interface().(listMapKeyer).ListMapKeys()
}

// jsonName returns the field's JSON name (empty if the tag has none),
// whether the tag has omitempty or omitzero, and whether the field is skipped.
func jsonName(f reflect.StructField) (name string, omit, skip bool) {
	tag, ok := f.Tag.Lookup("json")
	if !ok {
		return "", false, false
	}
	if tag == "-" {
		return "", false, true
	}
	name, opts, _ := strings.Cut(tag, ",")
	for o := range strings.SplitSeq(opts, ",") {
		if o == "omitempty" || o == "omitzero" {
			omit = true
		}
		if o == "inline" {
			name = ""
		}
	}
	return name, omit, false
}

func columnType(t reflect.Type, s map[string]any) string {
	if t == timeType || (t.Kind() == reflect.Pointer && t.Elem() == timeType) {
		return "date"
	}
	switch s["type"] {
	case "integer", "number", "boolean":
		return s["type"].(string)
	default:
		return "string"
	}
}

func applyTags(s map[string]any, t reflect.Type, tags fieldTags) error {
	if tags.doc != "" {
		s["description"] = tags.doc
	}
	if tags.pattern != "" {
		s["pattern"] = tags.pattern
	}
	typ, _ := s["type"].(string)
	for k, v := range tags.opts {
		switch k {
		case "min", "max":
			n, err := strconv.ParseFloat(v, 64)
			if err != nil {
				return fmt.Errorf("schema: %s=%q: %w", k, v, err)
			}
			s[map[string]string{"min": "minimum", "max": "maximum"}[k]] = jsonNumber(n)
		case "minLength", "maxLength", "minItems", "maxItems":
			n, err := strconv.ParseInt(v, 10, 64)
			if err != nil {
				return fmt.Errorf("schema: %s=%q: %w", k, v, err)
			}
			s[k] = n
		case "enum":
			var vals []any
			for e := range strings.SplitSeq(v, "|") {
				ev, err := scalar(typ, e)
				if err != nil {
					return fmt.Errorf("schema: enum value %q: %w", e, err)
				}
				vals = append(vals, ev)
			}
			s["enum"] = vals
		case "default":
			dv, err := scalar(typ, v)
			if err != nil {
				return fmt.Errorf("schema: default %q: %w", v, err)
			}
			s["default"] = dv
		case "format":
			s["format"] = v
		case "immutable":
			s["x-kubernetes-validations"] = []any{map[string]any{"rule": "self == oldSelf", "message": "field is immutable"}}
		case "listType":
			s["x-kubernetes-list-type"] = v
		case "listMapKey":
			keys, _ := s["x-kubernetes-list-map-keys"].([]string)
			s["x-kubernetes-list-map-keys"] = append(keys, v)
		case "column", "optional", "required":
		default:
			return fmt.Errorf("schema: unknown kube tag option %q on %v", k, t)
		}
	}
	return nil
}

// jsonNumber keeps whole numbers integral in the generated JSON.
func jsonNumber(f float64) any {
	if f == float64(int64(f)) {
		return int64(f)
	}
	return f
}

func scalar(typ, v string) (any, error) {
	switch typ {
	case "integer":
		return strconv.ParseInt(v, 10, 64)
	case "number":
		return strconv.ParseFloat(v, 64)
	case "boolean":
		return strconv.ParseBool(v)
	case "string", "":
		return v, nil
	default:
		var out any
		if err := json.Unmarshal([]byte(v), &out); err != nil {
			return nil, err
		}
		return out, nil
	}
}

// CRDSpec names a CustomResourceDefinition.
type CRDSpec struct {
	Group, Version, Kind, Plural, Singular string
	ShortNames, Categories                 []string
	Namespaced                             bool
	Labels                                 map[string]string
}

// CRD returns a CustomResourceDefinition for objects of struct type t, as a
// document ready for server-side apply.
func CRD(t reflect.Type, spec CRDSpec) (map[string]any, error) {
	r, err := Generate(t)
	if err != nil {
		return nil, err
	}
	scope := "Cluster"
	if spec.Namespaced {
		scope = "Namespaced"
	}
	names := map[string]any{
		"kind":     spec.Kind,
		"listKind": spec.Kind + "List",
		"plural":   spec.Plural,
		"singular": spec.Singular,
	}
	if len(spec.ShortNames) > 0 {
		names["shortNames"] = spec.ShortNames
	}
	if len(spec.Categories) > 0 {
		names["categories"] = spec.Categories
	}
	version := map[string]any{
		"name":    spec.Version,
		"served":  true,
		"storage": true,
		"schema":  map[string]any{"openAPIV3Schema": r.Schema},
	}
	if r.HasStatus {
		version["subresources"] = map[string]any{"status": map[string]any{}}
	}
	if len(r.Columns) > 0 {
		cols := append(slices.Clone(r.Columns), Column{Name: "Age", Type: "date", JSONPath: ".metadata.creationTimestamp"})
		version["additionalPrinterColumns"] = cols
	}
	meta := map[string]any{"name": spec.Plural + "." + spec.Group}
	if len(spec.Labels) > 0 {
		meta["labels"] = spec.Labels
	}
	return map[string]any{
		"apiVersion": "apiextensions.k8s.io/v1",
		"kind":       "CustomResourceDefinition",
		"metadata":   meta,
		"spec": map[string]any{
			"group":    spec.Group,
			"names":    names,
			"scope":    scope,
			"versions": []any{version},
		},
	}, nil
}
