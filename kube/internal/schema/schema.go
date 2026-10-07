// Package schema generates OpenAPI v3 schemas and CustomResourceDefinitions
// from Go types.
//
// Field names come from encoding/json struct tags. A field is required when
// its json tag has neither omitempty nor omitzero and it isn't a pointer,
// slice, map, or interface. The top-level status is never required, because
// the API server drops it from the objects that it creates. An integer field
// accepts only the values that its Go type can hold. Other struct tags add
// validation and display hints:
//
//	kube:"min=1,max=10"           numeric bounds (minimum, maximum)
//	kube:"minLength=1,maxLength=63"
//	kube:"minItems=1,maxItems=5"
//	kube:"enum=A|AAAA|CNAME"      allowed values
//	kube:"default=80"             server-side default
//	kube:"format=hostname"        OpenAPI string format
//	kube:"immutable"              rejects updates that change, set, or unset it
//	kube:"optional" / "required"  overrides the json tag rule
//	kube:"listType=map,listMapKey=name,listMapKey=protocol"
//	kube:"mapType=atomic"         server-side apply replaces the whole map
//	kube:"column=Ready"           adds a kubectl get column for the field
//	pattern:"^[a-z]+$"            regular expression for strings
//	doc:"..."                     description shown by kubectl explain
//
// Commas separate kube options. A value in single quotes can hold commas,
// and two single quotes in it stand for one, as in kube:"default='a, b'".
// Each enum value can be quoted the same way to hold a | or a comma. Only
// listMapKey can be repeated, once for each key.
//
// The API server enforces the immutable option with CEL rules. An update can
// still add or remove a whole list item or map value, with its immutable
// fields. The top-level status and its fields can't be immutable, because the
// API server creates objects without their status.
//
// A type can supply its own schema with an OpenAPISchema() map[string]any
// method, and an element type can make its slices server-side-apply maps
// keyed by some fields with a ListMapKeys() []string method. A field's
// listMapKey options replace the keys that its element type declares.
package schema

import (
	"encoding/json"
	"errors"
	"fmt"
	"reflect"
	"slices"
	"strconv"
	"strings"
	"time"
	"unicode"
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
	for _, p := range g.presence {
		if p.path[0] == "status" {
			return nil, fmt.Errorf("schema: %s: the top-level status and its fields can't be immutable, because the API server creates objects without their status", p.fpath)
		}
	}
	if err := addPresenceRules(s, g.presence); err != nil {
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
	// presence holds the immutable fields that need a rule in the nearest
	// object that exists whenever they can: the whole object, a list item,
	// a map value, or a required field of one of those. path names the
	// fields from that object to the field being generated.
	presence []presence
	path     []string
}

// presence is an immutable field that an update can add or remove.
type presence struct {
	// fpath is the field's path from the whole object, for errors.
	fpath string
	// path names the fields from the object that holds the rule.
	path []string
}

// anchored returns the schema that gen returns, with rules that keep updates
// from adding or removing the immutable fields within it.
func (g *gen) anchored(gen func() (map[string]any, error)) (map[string]any, error) {
	presence, path := g.presence, g.path
	g.presence, g.path = nil, nil
	defer func() { g.presence, g.path = presence, path }()
	s, err := gen()
	if err != nil {
		return nil, err
	}
	return s, addPresenceRules(s, g.presence)
}

// addPresenceRules adds a rule to the object schema s for each field in ps.
// The API server skips a field's own rules while the field is absent, so
// self == oldSelf can't stop an update that adds or removes it.
func addPresenceRules(s map[string]any, ps []presence) error {
	for _, p := range ps {
		var self, old []string
		var ref, fieldPath string
		for _, name := range p.path {
			id, ok := celName(name)
			if !ok {
				return fmt.Errorf("schema: %s: immutable needs a CEL rule, and CEL can't name the field %q", p.fpath, name)
			}
			ref += "." + id
			self = append(self, "has(self"+ref+")")
			old = append(old, "has(oldSelf"+ref+")")
			if strings.Contains(name, ".") {
				fieldPath += "['" + name + "']"
			} else {
				fieldPath += "." + name
			}
		}
		rule := self[0] + " == " + old[0]
		if len(self) > 1 {
			rule = "(" + strings.Join(self, " && ") + ") == (" + strings.Join(old, " && ") + ")"
		}
		addRule(s, map[string]any{"rule": rule, "message": "field is immutable", "fieldPath": fieldPath})
	}
	return nil
}

func addRule(s, rule map[string]any) {
	rules, _ := s["x-kubernetes-validations"].([]any)
	s["x-kubernetes-validations"] = append(slices.Clip(rules), rule)
}

var celReserved = []string{
	"true", "false", "null", "in", "as", "break", "const", "continue", "else",
	"for", "function", "if", "import", "let", "loop", "package", "namespace",
	"return", "var", "void", "while",
}

// celName returns the identifier that names the property name in a CEL rule
// of a CustomResourceDefinition, or false if a rule can't name it. It
// escapes names the way the API server does.
func celName(name string) (string, bool) {
	if name == "" || '0' <= name[0] && name[0] <= '9' {
		return "", false
	}
	if slices.Contains(celReserved, name) {
		return "__" + name + "__", true
	}
	var b strings.Builder
	for i := 0; i < len(name); i++ {
		switch c := name[i]; {
		case c == '_' && i+1 < len(name) && name[i+1] == '_':
			b.WriteString("__underscores__")
			i++
		case c == '.':
			b.WriteString("__dot__")
		case c == '-':
			b.WriteString("__dash__")
		case c == '/':
			b.WriteString("__slash__")
		case c == '_' || 'a' <= c && c <= 'z' || 'A' <= c && c <= 'Z' || '0' <= c && c <= '9':
			b.WriteByte(c)
		default:
			return "", false
		}
	}
	return b.String(), true
}

type fieldTags struct {
	// opts holds the kube options other than listMapKey, by name.
	opts        map[string]string
	enum        []string
	listMapKeys []string
	pattern     string
	doc         string
}

func parseTags(f reflect.StructField) (fieldTags, error) {
	ft := fieldTags{opts: map[string]string{}, pattern: f.Tag.Get("pattern"), doc: f.Tag.Get("doc")}
	opts, err := parseKubeTag(f.Tag.Get("kube"))
	if err != nil {
		return ft, err
	}
	for _, o := range opts {
		v := ""
		if len(o.values) > 0 {
			v = o.values[0]
		}
		if o.name == "listMapKey" {
			if v == "" {
				return ft, errors.New("listMapKey needs a key")
			}
			if slices.Contains(ft.listMapKeys, v) {
				return ft, fmt.Errorf("listMapKey=%s is repeated", v)
			}
			ft.listMapKeys = append(ft.listMapKeys, v)
			continue
		}
		if _, ok := ft.opts[o.name]; ok {
			return ft, fmt.Errorf("option %s is repeated", o.name)
		}
		ft.opts[o.name] = v
		if o.name == "enum" {
			ft.enum = o.values
		}
	}
	return ft, nil
}

type tagOption struct {
	name string
	// values is empty for an option without a value. Only enum can have
	// more than one.
	values []string
}

// parseKubeTag splits a kube field tag into its options, which commas
// separate. An option is a name or name=value. A value that starts with a
// single quote ends at the next single quote, and two single quotes in it
// stand for one, so a quoted value can hold commas. An enum value is a list
// of such values that | separates.
func parseKubeTag(tag string) ([]tagOption, error) {
	var opts []tagOption
	for rest := tag; rest != ""; {
		i := strings.IndexAny(rest, ",=")
		if i < 0 {
			i = len(rest)
		}
		o := tagOption{name: strings.TrimSpace(rest[:i])}
		rest = rest[i:]
		if strings.HasPrefix(rest, "=") {
			for {
				v, r, err := tagValue(rest[1:], o.name == "enum")
				if err != nil {
					return nil, fmt.Errorf("option %s: %w", o.name, err)
				}
				o.values = append(o.values, v)
				if rest = r; !strings.HasPrefix(rest, "|") {
					break
				}
			}
		}
		rest = strings.TrimPrefix(rest, ",")
		if o.name != "" || o.values != nil {
			opts = append(opts, o)
		}
	}
	return opts, nil
}

// tagValue reads the value at the start of s, which ends at a comma or, in a
// list, at a |. It returns the value and the rest of s, starting at the
// comma or |.
func tagValue(s string, list bool) (value, rest string, err error) {
	end := ","
	if list {
		end = ",|"
	}
	q := strings.TrimLeftFunc(s, unicode.IsSpace)
	if !strings.HasPrefix(q, "'") {
		i := strings.IndexAny(s, end)
		if i < 0 {
			i = len(s)
		}
		return strings.TrimSpace(s[:i]), s[i:], nil
	}
	var b strings.Builder
	for i := 1; i < len(q); i++ {
		if q[i] != '\'' {
			b.WriteByte(q[i])
			continue
		}
		if i+1 < len(q) && q[i+1] == '\'' {
			b.WriteByte('\'')
			i++
			continue
		}
		rest = strings.TrimLeftFunc(q[i+1:], unicode.IsSpace)
		if rest != "" && !strings.ContainsRune(end, rune(rest[0])) {
			return "", "", fmt.Errorf("%q follows the closing quote", rest)
		}
		return b.String(), rest, nil
	}
	return "", "", errors.New("the quoted value has no closing quote")
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
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64,
		reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64:
		return integerSchema(t), nil
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
		items, err := g.anchored(func() (map[string]any, error) { return g.typeSchema(t.Elem(), path+"[*]") })
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
		elem, err := g.anchored(func() (map[string]any, error) { return g.typeSchema(t.Elem(), path+".*") })
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

// integerSchema returns the schema of an integer type, bounded to the values
// that the type can hold, so that the API server rejects values that the
// program can't decode. The int32 bounds are explicit because older API
// servers don't check that a value fits the int32 format.
func integerSchema(t reflect.Type) map[string]any {
	s := map[string]any{"type": "integer", "format": "int64"}
	switch t.Kind() {
	case reflect.Int8, reflect.Int16, reflect.Int32:
		s["format"] = "int32"
		s["minimum"], s["maximum"] = -int64(1)<<(t.Bits()-1), int64(1)<<(t.Bits()-1)-1
	case reflect.Uint8, reflect.Uint16:
		s["format"] = "int32"
		s["minimum"], s["maximum"] = int64(0), int64(1)<<t.Bits()-1
	case reflect.Uint32:
		s["minimum"], s["maximum"] = int64(0), int64(1)<<32-1
	case reflect.Uint, reflect.Uint64:
		s["minimum"] = int64(0)
	}
	return s
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
		fpath := path + "." + name
		tags, err := parseTags(f)
		if err != nil {
			return fmt.Errorf("schema: %s: kube:%q: %w", fpath, f.Tag.Get("kube"), err)
		}
		_, optional := tags.opts["optional"]
		_, forced := tags.opts["required"]
		k := f.Type.Kind()
		nilable := k == reflect.Pointer || k == reflect.Slice || k == reflect.Map || k == reflect.Interface
		req := forced || (!omit && !nilable && !optional)
		if path == "" && name == "status" {
			// The API server drops the top-level status from every object
			// that it creates, so requiring it would reject every create.
			req = false
		}
		if _, ok := tags.opts["immutable"]; ok && (len(g.path) > 0 || !req) {
			g.presence = append(g.presence, presence{fpath, append(slices.Clone(g.path), name)})
		}
		var s map[string]any
		if len(g.path) == 0 && req {
			s, err = g.anchored(func() (map[string]any, error) { return g.schema(f.Type, fpath, tags) })
		} else {
			g.path = append(g.path, name)
			s, err = g.schema(f.Type, fpath, tags)
			g.path = g.path[:len(g.path)-1]
		}
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
		if req {
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
			if len(tags.enum) == 0 {
				return errors.New("schema: enum needs at least one value")
			}
			var vals []any
			for _, e := range tags.enum {
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
			addRule(s, map[string]any{"rule": "self == oldSelf", "message": "field is immutable"})
		case "listType":
			s["x-kubernetes-list-type"] = v
		case "mapType":
			s["x-kubernetes-map-type"] = v
		case "column", "optional", "required":
		default:
			return fmt.Errorf("schema: unknown kube tag option %q on %v", k, t)
		}
	}
	if len(tags.listMapKeys) > 0 {
		// The field's keys replace the keys of the element type's
		// ListMapKeys method.
		s["x-kubernetes-list-map-keys"] = tags.listMapKeys
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
	// Deprecated marks Version deprecated.
	Deprecated bool
	// Versions are other versions that the API server serves, each with
	// its own struct type. Version is the one it stores.
	Versions []VersionSpec
	// Conversion is spec.conversion, or nil to leave it out.
	Conversion map[string]any
}

// VersionSpec is a version of a CustomResourceDefinition.
type VersionSpec struct {
	Name       string
	Type       reflect.Type
	Deprecated bool
	// Unserved versions stay in the CustomResourceDefinition, but the API
	// server doesn't serve them.
	Unserved bool
}

// CRD returns a CustomResourceDefinition for objects of struct type t, as a
// document ready for server-side apply.
func CRD(t reflect.Type, spec CRDSpec) (map[string]any, error) {
	versions := []any{}
	for i, v := range append([]VersionSpec{{Name: spec.Version, Type: t, Deprecated: spec.Deprecated}}, spec.Versions...) {
		version, err := crdVersion(v, i == 0)
		if err != nil {
			return nil, err
		}
		versions = append(versions, version)
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
	meta := map[string]any{"name": spec.Plural + "." + spec.Group}
	if len(spec.Labels) > 0 {
		meta["labels"] = spec.Labels
	}
	crdSpec := map[string]any{
		"group":    spec.Group,
		"names":    names,
		"scope":    scope,
		"versions": versions,
	}
	if spec.Conversion != nil {
		crdSpec["conversion"] = spec.Conversion
	}
	return map[string]any{
		"apiVersion": "apiextensions.k8s.io/v1",
		"kind":       "CustomResourceDefinition",
		"metadata":   meta,
		"spec":       crdSpec,
	}, nil
}

// crdVersion returns the spec.versions entry for one version.
func crdVersion(v VersionSpec, storage bool) (map[string]any, error) {
	r, err := Generate(v.Type)
	if err != nil {
		return nil, err
	}
	version := map[string]any{
		"name":    v.Name,
		"served":  !v.Unserved,
		"storage": storage,
		"schema":  map[string]any{"openAPIV3Schema": r.Schema},
	}
	if v.Deprecated {
		version["deprecated"] = true
	}
	if r.HasStatus {
		version["subresources"] = map[string]any{"status": map[string]any{}}
	}
	if len(r.Columns) > 0 {
		cols := append(slices.Clone(r.Columns), Column{Name: "Age", Type: "date", JSONPath: ".metadata.creationTimestamp"})
		version["additionalPrinterColumns"] = cols
	}
	return version, nil
}
