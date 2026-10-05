package kube

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"log/slog"
	"maps"
	"net/http"
	"net/url"
	"regexp"
	"slices"
	"strconv"
	"strings"
	"time"

	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/schema"
)

// crdSpec describes a CustomResourceDefinition: the stored version, other
// versions, and how to convert between them.
type crdSpec struct {
	ti         *typeInfo
	versions   []*typeInfo
	conversion map[string]any
}

func (s crdSpec) name() string { return s.ti.plural + "." + s.ti.group }

func crdPath(name string) string {
	return "/apis/apiextensions.k8s.io/v1/customresourcedefinitions/" + name
}

// liveCRD is a CustomResourceDefinition as the API server has it.
type liveCRD struct {
	Metadata struct {
		ResourceVersion string            `json:"resourceVersion"`
		Labels          map[string]string `json:"labels"`
	} `json:"metadata"`
	Spec struct {
		Versions   []map[string]any `json:"versions"`
		Conversion struct {
			Strategy string `json:"strategy"`
			Webhook  struct {
				ClientConfig struct {
					CABundle []byte `json:"caBundle"`
				} `json:"clientConfig"`
			} `json:"webhook"`
		} `json:"conversion"`
	} `json:"spec"`
	Status struct {
		StoredVersions []string    `json:"storedVersions"`
		Conditions     []Condition `json:"conditions"`
	} `json:"status"`
}

func (l *liveCRD) version(name string) map[string]any {
	for _, v := range l.Spec.Versions {
		if versionName(v) == name {
			return v
		}
	}
	return nil
}

func (l *liveCRD) storage() string {
	for _, v := range l.Spec.Versions {
		if v["storage"] == true {
			return versionName(v)
		}
	}
	return ""
}

func versionName(v map[string]any) string { s, _ := v["name"].(string); return s }
func served(v map[string]any) bool        { return v["served"] == true }

func openAPISchema(v map[string]any) map[string]any {
	s, _ := v["schema"].(map[string]any)
	o, _ := s["openAPIV3Schema"].(map[string]any)
	return o
}

// getCRD returns the named CustomResourceDefinition, or nil if there isn't
// one.
func (m *Manager) getCRD(ctx context.Context, name string) (*liveCRD, error) {
	var live liveCRD
	if err := m.client.Get(ctx, crdPath(name), &live); err != nil {
		if client.IsNotFound(err) {
			return nil, nil
		}
		return nil, err
	}
	return &live, nil
}

func (m *Manager) ownsCRD(live *liveCRD) bool {
	return live != nil && live.Metadata.Labels[newLabelKeys(m.Domain).managedBy] != ""
}

// installedElsewhere explains, for an error about a version of live that
// this program doesn't declare, that another program installed live, if its
// label names one. A program that owns the type without reconciling it
// creates the CRD with only its own version.
func (m *Manager) installedElsewhere(live *liveCRD, version string) string {
	by := live.Metadata.Labels[newLabelKeys(m.Domain).managedBy]
	if by == labelValue(m.Name) {
		return ""
	}
	return fmt.Sprintf("%s installed the CustomResourceDefinition and may own the type without reconciling it; declare %s with kube.Version, or delete the CustomResourceDefinition while it has no objects", by, version)
}

// desiredCRD generates the CustomResourceDefinition for spec, in the form
// encoding/json decodes so that it compares with what the API server
// returns.
func (m *Manager) desiredCRD(spec crdSpec) (map[string]any, error) {
	ti := spec.ti
	cs := schema.CRDSpec{
		Group: ti.group, Version: ti.version, Kind: ti.kind, Plural: ti.plural, Singular: ti.singular,
		ShortNames: ti.shortNames, Categories: ti.categories, Namespaced: ti.scope == "Namespaced",
		Labels:     map[string]string{newLabelKeys(m.Domain).managedBy: labelValue(m.Name)},
		Deprecated: ti.deprecated, Conversion: spec.conversion,
	}
	for _, v := range spec.versions {
		cs.Versions = append(cs.Versions, schema.VersionSpec{Name: v.version, Type: v.goType, Deprecated: v.deprecated, Unserved: v.unserved})
	}
	crd, err := schema.CRD(ti.goType, cs)
	if err != nil {
		return nil, err
	}
	b, err := json.Marshal(crd)
	if err != nil {
		return nil, err
	}
	var out map[string]any
	return out, json.Unmarshal(b, &out)
}

// installCRD applies the CustomResourceDefinition for a type the program
// defines and waits until the API server serves it. It leaves alone a CRD
// that something else installed or that a newer version of the program
// installed, and it changes the CRD only in ways that lose no data.
func (m *Manager) installCRD(ctx context.Context, spec crdSpec) error {
	name := spec.name()
	live, err := m.getCRD(ctx, name)
	if err != nil {
		return fmt.Errorf("reading CustomResourceDefinition %s: %w", name, err)
	}
	if live != nil && !m.ownsCRD(live) {
		m.log.Info("using CustomResourceDefinition that something else installed", "crd", name)
		return nil
	}
	desired, err := m.desiredCRD(spec)
	if err != nil {
		return err
	}
	if live != nil {
		apply, err := m.planCRD(ctx, spec, live, desired)
		if err != nil || !apply {
			return err
		}
	}
	if err := m.client.Apply(ctx, crdPath(name), m.Name, true, desired, nil); err != nil {
		return fmt.Errorf("installing CustomResourceDefinition %s: %w", name, err)
	}
	if _, err := m.waitEstablished(ctx, name); err != nil {
		return err
	}
	m.log.Info("installed CustomResourceDefinition", "crd", name)
	return nil
}

// createCRD creates the CustomResourceDefinition for a type that the program
// defines and owns, but doesn't reconcile, if the cluster doesn't have one,
// and waits until the API server serves it. It never changes a CRD that
// exists, because only a program that reconciles the type knows all of the
// type's versions. That program installs its own CRD over this one.
func (m *Manager) createCRD(ctx context.Context, ti *typeInfo) error {
	spec := crdSpec{ti: ti}
	name := spec.name()
	live, err := m.getCRD(ctx, name)
	switch {
	case client.IsForbidden(err):
		m.log.Warn("can't check for CustomResourceDefinition without permission to get it", "crd", name, "err", err)
		return nil
	case err != nil:
		return fmt.Errorf("reading CustomResourceDefinition %s: %w", name, err)
	case live == nil:
		desired, err := m.desiredCRD(spec)
		if err != nil {
			return err
		}
		body, err := json.Marshal(desired)
		if err != nil {
			return err
		}
		err = m.client.Call(ctx, client.Request{
			Method: http.MethodPost, Path: client.Path("apiextensions.k8s.io/v1", "customresourcedefinitions", "", ""),
			Query: url.Values{"fieldManager": {m.Name}}, Body: body, ContentType: "application/json",
		}, nil)
		switch {
		case err == nil:
			m.log.Info("created CustomResourceDefinition", "crd", name)
		case client.IsAlreadyExists(err):
			// Another program created it first.
		default:
			return fmt.Errorf("creating CustomResourceDefinition %s: %w", name, err)
		}
	}
	if live == nil || !established(live) {
		if live, err = m.waitEstablished(ctx, name); err != nil {
			return err
		}
	}
	if v := live.version(ti.version); v == nil || !served(v) {
		return fmt.Errorf("kube: CustomResourceDefinition %s doesn't serve version %s, which %v uses", name, ti.version, ti.goType)
	}
	return nil
}

// waitEstablished waits until the API server serves the named
// CustomResourceDefinition, and returns it.
func (m *Manager) waitEstablished(ctx context.Context, name string) (*liveCRD, error) {
	deadline := time.Now().Add(time.Minute)
	for {
		got, err := m.getCRD(ctx, name)
		if err != nil {
			return nil, err
		}
		if got != nil && established(got) {
			return got, nil
		}
		if time.Now().After(deadline) {
			return nil, fmt.Errorf("CustomResourceDefinition %s was not established after a minute", name)
		}
		select {
		case <-ctx.Done():
			return nil, ctx.Err()
		case <-time.After(100 * time.Millisecond):
		}
	}
}

func established(l *liveCRD) bool {
	c := FindCondition(l.Status.Conditions, "Established")
	return c != nil && c.Status == True
}

// planCRD checks an update to a CustomResourceDefinition that the framework
// installed, maybe from another version of the program, and changes desired
// so that applying it loses no data. It reports false if a newer version of
// the program installed the CRD, which should then stay as it is.
func (m *Manager) planCRD(ctx context.Context, spec crdSpec, live *liveCRD, desired map[string]any) (bool, error) {
	name := spec.name()
	ours := map[string]bool{spec.ti.version: true}
	newest := spec.ti.version
	for _, v := range spec.versions {
		ours[v.version] = true
		if compareVersions(v.version, newest) > 0 {
			newest = v.version
		}
	}
	var dropped []string
	for _, lv := range live.Spec.Versions {
		v := versionName(lv)
		if ours[v] {
			continue
		}
		if compareVersions(v, newest) > 0 {
			if hub := live.version(spec.ti.version); hub == nil || !served(hub) {
				err := fmt.Errorf("kube: CustomResourceDefinition %s has version %s, which is newer than this program's versions, and doesn't serve %s, which this program reconciles", name, v, spec.ti.version)
				if hint := m.installedElsewhere(live, v); hint != "" {
					err = fmt.Errorf("%w; %s", err, hint)
				}
				return false, err
			}
			m.log.Warn("leaving CustomResourceDefinition as a newer version of this program installed it", "crd", name, "version", v)
			return false, nil
		}
		dropped = append(dropped, v)
	}
	m.keepData(ctx, spec, live, desired)
	if len(dropped) > 0 {
		if err := m.checkDropped(ctx, spec, live, dropped); err != nil {
			return false, err
		}
	}
	return true, nil
}

// keepData compares the schema of each served version in live and desired.
// Where desired drops a field, or changes its type, and objects have values
// there, it keeps the field as live has it, because a field that leaves the
// schema loses its values the next time the API server writes each object.
// It warns about newly required fields that objects don't set.
func (m *Manager) keepData(ctx context.Context, spec crdSpec, live *liveCRD, desired map[string]any) {
	name := spec.name()
	body, _ := desired["spec"].(map[string]any)
	versions, _ := body["versions"].([]any)
	for _, dv := range versions {
		d, _ := dv.(map[string]any)
		version := versionName(d)
		l := live.version(version)
		if l == nil || !served(l) {
			continue
		}
		ls, ds := openAPISchema(l), openAPISchema(d)
		var changes []schemaChange
		diffSchemas(ls, ds, nil, &changes)
		if len(changes) == 0 {
			continue
		}
		counts, err := m.scanObjects(ctx, spec, version, changes)
		for i, ch := range changes {
			field := formatPath(ch.path)
			switch {
			case ch.kind == changeRequired:
				if err == nil && counts[i] > 0 {
					m.log.Warn("objects don't set a newly required field, so changing their spec fails until they do; give the field a default or make it optional",
						"crd", name, "version", version, "field", field, "objects", counts[i])
				}
			case err != nil:
				setSchemaAt(ds, ch.path, schemaAt(ls, ch.path))
				m.log.Warn("keeping field in CustomResourceDefinition because objects can't be checked for values", "crd", name, "version", version, "field", field, "err", err)
			case counts[i] > 0:
				setSchemaAt(ds, ch.path, schemaAt(ls, ch.path))
				msg := "keeping field that objects set, which this program's type doesn't declare; clear it in those objects, or add a version without it"
				if ch.kind == changeType {
					msg = "keeping the type of field that objects set, which this program's type changes; add a version to change it"
				}
				m.log.Warn(msg, "crd", name, "version", version, "field", field, "objects", counts[i])
			}
		}
	}
}

// scanObjects counts, for each change, the objects that would lose data:
// those with a value at a removed or retyped field, or without a newly
// required one.
func (m *Manager) scanObjects(ctx context.Context, spec crdSpec, version string, changes []schemaChange) ([]int, error) {
	counts := make([]int, len(changes))
	path := client.Path(spec.ti.group+"/"+version, spec.ti.plural, "", "")
	_, err := m.client.ListAll(ctx, path, nil, "", 500, func(dec *json.Decoder) error {
		var obj any
		if err := dec.Decode(&obj); err != nil {
			return err
		}
		for i, ch := range changes {
			if ch.kind == changeRequired && missingAt(obj, ch.path) || ch.kind != changeRequired && hasValueAt(obj, ch.path) {
				counts[i]++
			}
		}
		return nil
	})
	return counts, err
}

// checkDropped makes sure that removing versions from a
// CustomResourceDefinition strands nothing: no object may still be stored
// in one, and no object may have managedFields entries for one, because
// server-side apply fails on such objects once the version is gone
// (https://github.com/kubernetes/kubernetes/issues/111937), and the entries
// can't be removed after that.
func (m *Manager) checkDropped(ctx context.Context, spec crdSpec, live *liveCRD, dropped []string) error {
	name := spec.name()
	for _, v := range dropped {
		if slices.Contains(live.Status.StoredVersions, v) {
			if hint := m.installedElsewhere(live, v); hint != "" {
				return fmt.Errorf("kube: can't remove version %s from CustomResourceDefinition %s yet: objects may still be stored as %s; %s", v, name, v, hint)
			}
			return fmt.Errorf("kube: can't remove version %s from CustomResourceDefinition %s yet: objects may still be stored as %s; keep its kube.Version until the framework rewrites them, which it records by removing %s from the CustomResourceDefinition's status.storedVersions", v, name, v, v)
		}
	}
	stale := map[string]bool{}
	for _, v := range dropped {
		stale[spec.ti.group+"/"+v] = true
	}
	n := 0
	if err := m.eachObject(ctx, spec, live.storage(), func(it crdItem) error {
		if slices.ContainsFunc(it.Metadata.ManagedFields, func(e json.RawMessage) bool { return stale[entryAPIVersion(e)] }) {
			n++
		}
		return nil
	}); err != nil {
		return fmt.Errorf("kube: checking objects before removing versions %v from CustomResourceDefinition %s: %w", dropped, name, err)
	}
	if n > 0 {
		return fmt.Errorf("kube: can't remove versions %v from CustomResourceDefinition %s yet: %d objects have managedFields entries for them, which break server-side apply once the versions are gone; first run a release that keeps their kube.Version with unserved in the version's kube tag, so the framework removes the entries", dropped, name, n)
	}
	return nil
}

// crdItem is the metadata of a custom object, as a metadata-only list
// returns it.
type crdItem struct {
	Metadata struct {
		Name            string            `json:"name"`
		Namespace       string            `json:"namespace"`
		ResourceVersion string            `json:"resourceVersion"`
		ManagedFields   []json.RawMessage `json:"managedFields"`
	} `json:"metadata"`
}

// eachObject calls fn with the metadata of every object of spec's type, in
// every namespace, read at version.
func (m *Manager) eachObject(ctx context.Context, spec crdSpec, version string, fn func(crdItem) error) error {
	path := client.Path(spec.ti.group+"/"+version, spec.ti.plural, "", "")
	_, err := m.client.ListAll(ctx, path, nil, listAccept, 500, func(dec *json.Decoder) error {
		var it crdItem
		if err := dec.Decode(&it); err != nil {
			return err
		}
		return fn(it)
	})
	return err
}

func entryAPIVersion(e json.RawMessage) string {
	var v struct {
		APIVersion string `json:"apiVersion"`
	}
	_ = json.Unmarshal(e, &v)
	return v.APIVersion
}

// maintainCRD finishes what a change to the controller's
// CustomResourceDefinition started: it rewrites objects stored in older
// versions, then records in the CRD's status.storedVersions that only the
// current version holds data, and it removes managedFields entries for
// unserved versions. It retries until it succeeds or ctx is done.
func (c *controller[T, P]) maintainCRD(ctx context.Context) {
	// Only the replica that holds the shard of the CRD's name does this.
	// Others wait in case the shard moves to them.
	for key := (Key{Name: c.crd().name()}); !c.sh.owns(key); {
		select {
		case <-ctx.Done():
			return
		case <-time.After(5 * time.Second):
		}
	}
	delay := 5 * time.Second
	for {
		err := c.m.migrateCRD(ctx, c.crd(), c.ti.status != nil, c.log)
		switch {
		case err == nil || ctx.Err() != nil:
			return
		case client.IsForbidden(err):
			c.log.Warn("can't migrate stored objects without permission to list and patch them in every namespace", "crd", c.crd().name(), "err", err)
			return
		}
		c.log.Warn("CustomResourceDefinition migration failed; retrying", "crd", c.crd().name(), "err", err, "retry", delay)
		select {
		case <-ctx.Done():
			return
		case <-time.After(delay):
		}
		delay = min(2*delay, 5*time.Minute)
	}
}

func (m *Manager) migrateCRD(ctx context.Context, spec crdSpec, status bool, log *slog.Logger) error {
	name := spec.name()
	live, err := m.getCRD(ctx, name)
	if err != nil || !m.ownsCRD(live) || live.storage() != spec.ti.version {
		return err
	}
	storage := live.storage()
	migrate := !slices.Equal(live.Status.StoredVersions, []string{storage})
	unserved := map[string]bool{}
	for _, v := range live.Spec.Versions {
		if !served(v) {
			unserved[spec.ti.group+"/"+versionName(v)] = true
		}
	}
	if !migrate && len(unserved) == 0 {
		return nil
	}
	var errs []error
	rewritten, cleaned := 0, 0
	err = m.eachObject(ctx, spec, storage, func(it crdItem) error {
		path := client.Path(spec.ti.group+"/"+storage, spec.ti.plural, it.Metadata.Namespace, it.Metadata.Name)
		if slices.ContainsFunc(it.Metadata.ManagedFields, func(e json.RawMessage) bool { return unserved[entryAPIVersion(e)] }) {
			// Writing the object also stores it in the current version.
			if err := m.cleanManagedFields(ctx, path, spec.ti.group+"/"+storage, unserved, it); err != nil {
				errs = append(errs, fmt.Errorf("%s/%s: %w", it.Metadata.Namespace, it.Metadata.Name, err))
			} else {
				cleaned++
			}
			return nil
		}
		if !migrate {
			return nil
		}
		if status {
			// Admission webhooks don't intercept the status subresource, and
			// a write there stores the whole object.
			path += "/status"
		}
		body := fmt.Appendf(nil, `{"metadata":{"resourceVersion":%q}}`, it.Metadata.ResourceVersion)
		switch err := m.client.Patch(ctx, path, client.MergePatch, nil, body, nil); {
		case err == nil:
			rewritten++
		case client.IsNotFound(err), client.IsConflict(err):
			// It's gone, or something else wrote it in the current version.
		default:
			errs = append(errs, fmt.Errorf("%s/%s: %w", it.Metadata.Namespace, it.Metadata.Name, err))
		}
		return nil
	})
	if err != nil {
		return err
	}
	if cleaned > 0 {
		log.Info("removed managedFields entries for unserved versions", "crd", name, "objects", cleaned)
	}
	if len(errs) > 0 {
		return fmt.Errorf("%d objects: %w", len(errs), errors.Join(errs[:min(len(errs), 3)]...))
	}
	if !migrate {
		return nil
	}
	body := fmt.Appendf(nil, `{"metadata":{"resourceVersion":%q},"status":{"storedVersions":[%q]}}`, live.Metadata.ResourceVersion, storage)
	if err := m.client.Patch(ctx, crdPath(name)+"/status", client.MergePatch, nil, body, nil); err != nil {
		// A conflict means the CustomResourceDefinition changed while
		// objects were being rewritten, so they must be rewritten again.
		return fmt.Errorf("updating status.storedVersions: %w", err)
	}
	log.Info("migrated stored objects", "crd", name, "storageVersion", storage, "previous", live.Status.StoredVersions, "rewritten", rewritten+cleaned)
	return nil
}

// cleanManagedFields removes an object's managedFields entries whose
// apiVersion is in remove.
func (m *Manager) cleanManagedFields(ctx context.Context, path, apiVersion string, remove map[string]bool, it crdItem) error {
	for attempt := 0; ; attempt++ {
		var keep []json.RawMessage
		var first json.RawMessage
		for _, e := range it.Metadata.ManagedFields {
			switch {
			case !remove[entryAPIVersion(e)]:
				keep = append(keep, e)
			case first == nil:
				first = e
			}
		}
		if first == nil {
			return nil
		}
		if len(keep) == 0 {
			// Without any entry, the next server-side apply would record an
			// inferred one that co-owns every field. Keep a minimal entry
			// for the same manager instead.
			var e map[string]any
			_ = json.Unmarshal(first, &e)
			seed, _ := json.Marshal(map[string]any{
				"manager": e["manager"], "operation": e["operation"], "apiVersion": apiVersion,
				"time": time.Now().UTC().Format(time.RFC3339), "fieldsType": "FieldsV1",
				"fieldsV1": map[string]any{"f:metadata": map[string]any{"f:name": map[string]any{}}},
			})
			keep = []json.RawMessage{seed}
		}
		body, err := json.Marshal([]map[string]any{
			{"op": "replace", "path": "/metadata/managedFields", "value": keep},
			{"op": "replace", "path": "/metadata/resourceVersion", "value": it.Metadata.ResourceVersion},
		})
		if err != nil {
			return err
		}
		err = m.client.Patch(ctx, path, client.JSONPatch, nil, body, nil)
		if err == nil || client.IsNotFound(err) {
			return nil
		}
		if !client.IsConflict(err) || attempt == 2 {
			return err
		}
		it = crdItem{}
		if err := m.client.Get(ctx, path, &it); err != nil {
			if client.IsNotFound(err) {
				return nil
			}
			return err
		}
	}
}

// updateConversionBundle puts bundle in the conversion webhook
// configuration of a CustomResourceDefinition that the framework installed.
func (m *Manager) updateConversionBundle(ctx context.Context, ti *typeInfo, clientConfig map[string]any) error {
	name := ti.plural + "." + ti.group
	live, err := m.getCRD(ctx, name)
	if err != nil || !m.ownsCRD(live) || live.Spec.Conversion.Strategy != "Webhook" {
		return err
	}
	bundle, _ := clientConfig["caBundle"].([]byte)
	if bytes.Equal(live.Spec.Conversion.Webhook.ClientConfig.CABundle, bundle) {
		return nil
	}
	body, err := json.Marshal(map[string]any{"spec": map[string]any{"conversion": map[string]any{
		"webhook": map[string]any{"clientConfig": map[string]any{"caBundle": bundle}},
	}}})
	if err != nil {
		return err
	}
	return m.client.Patch(ctx, crdPath(name), client.MergePatch, nil, body, nil)
}

// A schemaChange is a difference between two versions of a schema that
// can lose or reject data in existing objects.
type schemaChange struct {
	kind string
	// path names a field: property names, with "[]" for the items of a
	// list and "{}" for the values of a map.
	path []string
}

const (
	changeRemoved  = "removed"
	changeType     = "type"
	changeRequired = "required"
)

// diffSchemas appends to out the fields that ours removes from live,
// the fields whose type it changes, and the fields it newly requires
// without a default.
func diffSchemas(live, ours map[string]any, path []string, out *[]schemaChange) {
	if ours["x-kubernetes-preserve-unknown-fields"] == true {
		return
	}
	lt, ot := live["type"], ours["type"]
	if lt != nil && ot != nil && lt != ot || live["x-kubernetes-preserve-unknown-fields"] == true {
		*out = append(*out, schemaChange{changeType, slices.Clone(path)})
		return
	}
	lp, _ := live["properties"].(map[string]any)
	op, _ := ours["properties"].(map[string]any)
	for _, k := range slices.Sorted(maps.Keys(lp)) {
		ls, _ := lp[k].(map[string]any)
		ds, ok := op[k].(map[string]any)
		if !ok {
			*out = append(*out, schemaChange{changeRemoved, append(slices.Clone(path), k)})
			continue
		}
		diffSchemas(ls, ds, append(path, k), out)
	}
	for _, sub := range [][2]string{{"items", "[]"}, {"additionalProperties", "{}"}} {
		ls, lok := live[sub[0]].(map[string]any)
		ds, dok := ours[sub[0]].(map[string]any)
		if lok && dok {
			diffSchemas(ls, ds, append(path, sub[1]), out)
		}
	}
	lr, _ := live["required"].([]any)
	or, _ := ours["required"].([]any)
	for _, r := range or {
		k, _ := r.(string)
		if slices.Contains(lr, r) {
			continue
		}
		if s, _ := op[k].(map[string]any); s["default"] == nil {
			*out = append(*out, schemaChange{changeRequired, append(slices.Clone(path), k)})
		}
	}
}

// hasValueAt reports whether doc has a non-null value at path.
func hasValueAt(doc any, path []string) bool {
	if len(path) == 0 {
		return doc != nil
	}
	switch path[0] {
	case "[]":
		list, _ := doc.([]any)
		return slices.ContainsFunc(list, func(e any) bool { return hasValueAt(e, path[1:]) })
	case "{}":
		obj, _ := doc.(map[string]any)
		for _, v := range obj {
			if hasValueAt(v, path[1:]) {
				return true
			}
		}
		return false
	default:
		obj, _ := doc.(map[string]any)
		return hasValueAt(obj[path[0]], path[1:])
	}
}

// missingAt reports whether doc has an object at path's parent without the
// last field of path.
func missingAt(doc any, path []string) bool {
	if len(path) == 1 {
		obj, ok := doc.(map[string]any)
		return ok && obj[path[0]] == nil
	}
	switch path[0] {
	case "[]":
		list, _ := doc.([]any)
		return slices.ContainsFunc(list, func(e any) bool { return missingAt(e, path[1:]) })
	case "{}":
		obj, _ := doc.(map[string]any)
		for _, v := range obj {
			if missingAt(v, path[1:]) {
				return true
			}
		}
		return false
	default:
		obj, _ := doc.(map[string]any)
		return missingAt(obj[path[0]], path[1:])
	}
}

// schemaAt returns the schema of the field at path.
func schemaAt(s map[string]any, path []string) map[string]any {
	for _, p := range path {
		switch p {
		case "[]":
			s, _ = s["items"].(map[string]any)
		case "{}":
			s, _ = s["additionalProperties"].(map[string]any)
		default:
			props, _ := s["properties"].(map[string]any)
			s, _ = props[p].(map[string]any)
		}
	}
	return s
}

// setSchemaAt replaces the schema of the field at path. The field's parent
// must exist.
func setSchemaAt(s map[string]any, path []string, field map[string]any) {
	parent := schemaAt(s, path[:len(path)-1])
	switch last := path[len(path)-1]; last {
	case "[]":
		parent["items"] = field
	case "{}":
		parent["additionalProperties"] = field
	default:
		props, _ := parent["properties"].(map[string]any)
		if props == nil {
			props = map[string]any{}
			parent["properties"] = props
		}
		props[last] = field
	}
}

func formatPath(path []string) string {
	var b strings.Builder
	for _, p := range path {
		if p != "[]" && p != "{}" && b.Len() > 0 {
			b.WriteByte('.')
		}
		b.WriteString(p)
	}
	return b.String()
}

var kubeVersion = regexp.MustCompile(`^v([1-9][0-9]*)(?:(alpha|beta)([1-9][0-9]*))?$`)

// compareVersions orders version names the way Kubernetes does: GA
// versions before beta before alpha, higher numbers first, and names that
// don't look like Kubernetes versions last, alphabetically. It returns a
// positive number if a comes first.
func compareVersions(a, b string) int {
	ma, mb := kubeVersion.FindStringSubmatch(a), kubeVersion.FindStringSubmatch(b)
	switch {
	case ma == nil && mb == nil:
		return strings.Compare(b, a)
	case ma == nil:
		return -1
	case mb == nil:
		return 1
	}
	stability := map[string]int{"": 3, "beta": 2, "alpha": 1}
	if d := stability[ma[2]] - stability[mb[2]]; d != 0 {
		return d
	}
	num := func(s string) int { n, _ := strconv.Atoi(s); return n }
	if d := num(ma[1]) - num(mb[1]); d != 0 {
		return d
	}
	return num(ma[3]) - num(mb[3])
}
