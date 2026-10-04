package kube

import (
	"context"
	"fmt"
	"log/slog"
	"reflect"
	"strings"
	"sync"

	"github.com/imjasonh/playground/kube/internal/client"
)

// typeInfo is what the framework knows about a Go type from its definition.
// Facts that depend on the cluster, such as the plural name of an existing
// type, are resolved later with discovery.
type typeInfo struct {
	goType     reflect.Type
	group      string
	version    string
	apiVersion string
	kind       string
	plural     string
	singular   string
	// scope is "Namespaced", "Cluster", or empty when discovery decides.
	scope      string
	custom     bool
	shortNames []string
	categories []string
	// deprecated makes the API server warn clients that use this version.
	deprecated bool
	// unserved keeps this version in the CustomResourceDefinition without
	// serving it, so it can be removed safely in a later release.
	unserved bool
	// local types are read and written only in the program's own
	// namespace, so their rules go in the Role there. Caches watch every
	// namespace that the program watches, so local types can't have them.
	local bool

	// status is the index of the top-level status field, or nil.
	status []int
	// conditions and observedGeneration index into the status struct.
	conditions         []int
	observedGeneration []int
	// metadataOnly types declare no fields besides Object, so the framework
	// asks the API server for metadata only.
	metadataOnly bool

	// newCache builds a cache for this type. It's captured where the Go
	// type is known statically, so caches are typed without reflection.
	newCache func(id int, res resolved, c *client.Client, cfg informerConfig, log *slog.Logger, m *metrics) cache
}

// cache is a running informer of any type.
type cache interface {
	source
	run(ctx context.Context)
	onChange(func(old, new *ObjectMeta, initial bool))
	size() int
}

func (inf *informer[T, P]) onChange(h func(old, new *ObjectMeta, initial bool)) {
	inf.addHandler(func(old, new *T, initial bool) {
		var om, nm *ObjectMeta
		if old != nil {
			om = metaOf[T, P](old)
		}
		if new != nil {
			nm = metaOf[T, P](new)
		}
		h(om, nm, initial)
	})
}

func (inf *informer[T, P]) size() int { return inf.store.len() }

func (ti *typeInfo) String() string {
	return ti.kind + "." + ti.apiVersion
}

var (
	typeCache  sync.Map // reflect.Type -> *typeInfo or error
	objectType = reflect.TypeFor[Object]()
	condsType  = reflect.TypeFor[[]Condition]()
)

func typeInfoFor[T any, P Resource[T]]() (*typeInfo, error) {
	t := reflect.TypeFor[T]()
	if v, ok := typeCache.Load(t); ok {
		if err, ok := v.(error); ok {
			return nil, err
		}
		return v.(*typeInfo), nil
	}
	ti, err := parseType(t)
	if err != nil {
		typeCache.Store(t, err)
		return nil, err
	}
	ti.newCache = func(id int, res resolved, c *client.Client, cfg informerConfig, log *slog.Logger, m *metrics) cache {
		return newInformer[T, P](id, ti, res, c, cfg, log, m)
	}
	v, _ := typeCache.LoadOrStore(t, ti)
	return v.(*typeInfo), nil
}

func parseType(t reflect.Type) (*typeInfo, error) {
	if t.Kind() != reflect.Struct {
		return nil, fmt.Errorf("kube: %v is not a struct", t)
	}
	var tag reflect.StructTag
	found := false
	ti := &typeInfo{goType: t, metadataOnly: true}
	for i := range t.NumField() {
		f := t.Field(i)
		if f.Anonymous && f.Type == objectType {
			if _, named := f.Tag.Lookup("json"); named {
				return nil, fmt.Errorf("kube: %v embeds kube.Object with a json tag; remove it so apiVersion, kind, and metadata stay at the top level", t)
			}
			tag, found = f.Tag, true
			continue
		}
		name, _, _ := strings.Cut(f.Tag.Get("json"), ",")
		if !f.IsExported() || name == "-" {
			continue
		}
		ti.metadataOnly = false
		if name == "status" {
			ti.status = []int{i}
			findStatusFields(ti, f.Type)
		}
	}
	if !found {
		return nil, fmt.Errorf("kube: %v doesn't embed kube.Object", t)
	}
	if err := ti.parseTag(t.String(), t.Name(), tag.Get("kube")); err != nil {
		return nil, err
	}
	return ti, nil
}

// parseTag sets ti from the kube tag of a type's embedded Object. typeName
// names the type in errors, and name is its name without the package,
// which is the default kind.
func (ti *typeInfo) parseTag(typeName, name, tag string) error {
	for part := range strings.SplitSeq(tag, ",") {
		part = strings.TrimSpace(part)
		if part == "" {
			continue
		}
		switch part {
		case "deprecated":
			ti.deprecated = true
			continue
		case "unserved":
			ti.unserved = true
			continue
		case "local":
			ti.local = true
			continue
		}
		k, v, ok := strings.Cut(part, "=")
		if !ok || v == "" {
			return fmt.Errorf("kube: %s: tag option %q needs a value", typeName, part)
		}
		switch k {
		case "group":
			ti.group = v
		case "version":
			ti.version = v
		case "apiVersion":
			ti.apiVersion = v
		case "kind":
			ti.kind = v
		case "plural":
			ti.plural = v
		case "singular":
			ti.singular = v
		case "scope":
			if v != "Namespaced" && v != "Cluster" {
				return fmt.Errorf("kube: %s: scope must be Namespaced or Cluster, not %q", typeName, v)
			}
			ti.scope = v
		case "shortName":
			ti.shortNames = append(ti.shortNames, v)
		case "category":
			ti.categories = append(ti.categories, v)
		default:
			return fmt.Errorf("kube: %s: unknown tag option %q", typeName, k)
		}
	}
	if ti.kind == "" {
		ti.kind = name
	}
	switch {
	case ti.apiVersion != "" && (ti.group != "" || ti.version != ""):
		return fmt.Errorf("kube: %s: give either apiVersion or group and version, not both", typeName)
	case ti.apiVersion != "":
		if g, v, ok := strings.Cut(ti.apiVersion, "/"); ok {
			ti.group, ti.version = g, v
		} else {
			ti.version = ti.apiVersion
		}
	case ti.group != "":
		if !strings.Contains(ti.group, ".") {
			return fmt.Errorf("kube: %s: group %q must be a domain name with a dot, like example.dev", typeName, ti.group)
		}
		ti.custom = true
		if ti.version == "" {
			ti.version = "v1"
		}
		ti.apiVersion = ti.group + "/" + ti.version
		if ti.scope == "" {
			ti.scope = "Namespaced"
		}
	default:
		return fmt.Errorf(`kube: %s: the embedded kube.Object needs a kube struct tag: kube:"group=example.dev" for a type you define, or kube:"apiVersion=apps/v1,kind=Deployment" for one that exists`, typeName)
	}
	if ti.local {
		if ti.scope == "Cluster" {
			return fmt.Errorf("kube: %s: a local type lives in a namespace, so it can't have scope=Cluster", typeName)
		}
		ti.scope = "Namespaced"
	}
	if ti.singular == "" {
		ti.singular = strings.ToLower(ti.kind)
	}
	if ti.plural == "" && ti.custom {
		ti.plural = pluralize(ti.kind)
	}
	return nil
}

func findStatusFields(ti *typeInfo, st reflect.Type) {
	if st.Kind() != reflect.Struct {
		return
	}
	for i := range st.NumField() {
		f := st.Field(i)
		name, _, _ := strings.Cut(f.Tag.Get("json"), ",")
		switch {
		case name == "conditions" && f.Type == condsType:
			ti.conditions = []int{i}
		case name == "observedGeneration" && f.Type.Kind() == reflect.Int64:
			ti.observedGeneration = []int{i}
		}
	}
}

// pluralize applies the English rules that cover Kubernetes kind names.
func pluralize(kind string) string {
	s := strings.ToLower(kind)
	switch {
	case strings.HasSuffix(s, "s"), strings.HasSuffix(s, "x"), strings.HasSuffix(s, "z"),
		strings.HasSuffix(s, "ch"), strings.HasSuffix(s, "sh"):
		return s + "es"
	case strings.HasSuffix(s, "y") && len(s) > 1 && !strings.ContainsRune("aeiou", rune(s[len(s)-2])):
		return s[:len(s)-1] + "ies"
	default:
		return s + "s"
	}
}
