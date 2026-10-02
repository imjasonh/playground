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
	for part := range strings.SplitSeq(tag.Get("kube"), ",") {
		part = strings.TrimSpace(part)
		if part == "" {
			continue
		}
		k, v, ok := strings.Cut(part, "=")
		if !ok || v == "" {
			return nil, fmt.Errorf("kube: %v: tag option %q needs a value", t, part)
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
				return nil, fmt.Errorf("kube: %v: scope must be Namespaced or Cluster, not %q", t, v)
			}
			ti.scope = v
		case "shortName":
			ti.shortNames = append(ti.shortNames, v)
		case "category":
			ti.categories = append(ti.categories, v)
		default:
			return nil, fmt.Errorf("kube: %v: unknown tag option %q", t, k)
		}
	}
	if ti.kind == "" {
		ti.kind = t.Name()
	}
	switch {
	case ti.apiVersion != "" && (ti.group != "" || ti.version != ""):
		return nil, fmt.Errorf("kube: %v: give either apiVersion or group and version, not both", t)
	case ti.apiVersion != "":
		if g, v, ok := strings.Cut(ti.apiVersion, "/"); ok {
			ti.group, ti.version = g, v
		} else {
			ti.version = ti.apiVersion
		}
	case ti.group != "":
		if !strings.Contains(ti.group, ".") {
			return nil, fmt.Errorf("kube: %v: group %q must be a domain name with a dot, like example.dev", t, ti.group)
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
		return nil, fmt.Errorf(`kube: %v: the embedded kube.Object needs a kube struct tag: kube:"group=example.dev" for a type you define, or kube:"apiVersion=apps/v1,kind=Deployment" for one that exists`, t)
	}
	if ti.singular == "" {
		ti.singular = strings.ToLower(ti.kind)
	}
	if ti.plural == "" && ti.custom {
		ti.plural = pluralize(ti.kind)
	}
	return ti, nil
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
