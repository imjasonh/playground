package kube

import (
	"context"
	"fmt"
	"regexp"
	"strings"

	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/yaml"
)

// Install returns a Controller that applies the objects in a manifest when
// the program starts, as the framework installs the CustomResourceDefinitions
// of the types that controllers reconcile. Use it for objects that the
// program needs but doesn't reconcile, such as admission policies, and embed
// the manifest in the program.
//
// manifest returns YAML documents separated by "---" lines, without
// anchors, aliases, or tags. The framework calls manifest after it parses
// the program's flags, so manifest can read them, and return nil to install
// nothing. The generate command calls it with the flags after "--", and
// grants the program create and patch on each object that it returns, by
// name. For an admission policy with a paramKind and a binding with a
// paramRef, generate also grants the get permissions that the API server
// checks when it creates them, or prints a warning when it can't.
//
// After the controllers install their CustomResourceDefinitions and before
// they reconcile, the framework applies the objects in order with
// server-side apply, and labels them with the program's name. It applies
// them again each time the program starts, but doesn't watch them. Fields
// that the manifest doesn't set keep the values that others give them.
// Entries that others add to a list that merges by key or value, such as a
// binding's validationActions, also stay. If the merged object isn't valid,
// the apply fails and the program exits when it starts. An object that a
// later manifest leaves out stays in the cluster. Give each namespaced
// object its metadata.namespace, and put each admission policy before its
// bindings.
//
// Before it applies any of the objects, the framework replaces each container
// image that names a tag with the image by digest, as it does for objects
// that controllers apply. If it can't resolve a tag, the program exits when it
// starts.
func Install(manifest func() []byte) Controller {
	return &installer{manifest: manifest}
}

type installer struct {
	manifest func() []byte
	objects  []installObject
}

// installObject is an object in a manifest for Install.
type installObject struct {
	apiVersion, kind, namespace, name string
	body                              map[string]any
}

var documentSeparator = regexp.MustCompile(`(?m)^---[ \t]*(#.*)?$`)

// parseManifest parses a stream of YAML documents, each an object.
func parseManifest(b []byte) ([]installObject, error) {
	var out []installObject
	for i, doc := range documentSeparator.Split(strings.ReplaceAll(string(b), "\r\n", "\n"), -1) {
		v, err := yaml.Parse([]byte(doc))
		if err != nil {
			return nil, fmt.Errorf("document %d: %w", i+1, err)
		}
		if v == nil {
			continue
		}
		body, ok := v.(map[string]any)
		if !ok {
			return nil, fmt.Errorf("document %d isn't an object", i+1)
		}
		meta, _ := body["metadata"].(map[string]any)
		o := installObject{body: body}
		o.apiVersion, _ = body["apiVersion"].(string)
		o.kind, _ = body["kind"].(string)
		o.name, _ = meta["name"].(string)
		o.namespace, _ = meta["namespace"].(string)
		if o.apiVersion == "" || o.kind == "" || o.name == "" {
			return nil, fmt.Errorf("document %d needs apiVersion, kind, and metadata.name", i+1)
		}
		out = append(out, o)
	}
	return out, nil
}

func (in *installer) describe() (declared, error) {
	objs, err := parseManifest(in.manifest())
	if err != nil {
		return declared{}, fmt.Errorf("kube.Install: %w", err)
	}
	return declared{installs: objs}, nil
}

func (in *installer) prepare(_ context.Context, m *Manager) error {
	objs, err := parseManifest(in.manifest())
	if err != nil {
		return fmt.Errorf("kube.Install: %w", err)
	}
	for _, o := range objs {
		meta := o.body["metadata"].(map[string]any)
		labels, _ := meta["labels"].(map[string]any)
		if labels == nil {
			labels = map[string]any{}
		}
		labels[newLabelKeys().managedBy] = labelValue(m.Name)
		meta["labels"] = labels
	}
	in.objects = objs
	return nil
}

func (in *installer) setup(ctx context.Context, m *Manager) error {
	for _, o := range in.objects {
		if err := resolveImages(ctx, o.body, m.log); err != nil {
			return fmt.Errorf("installing %s %s: %w", o.kind, o.name, err)
		}
	}
	for _, o := range in.objects {
		res, err := m.client.Resource(ctx, o.apiVersion, o.kind)
		if err != nil {
			return fmt.Errorf("installing %s %s: %w", o.kind, o.name, err)
		}
		switch {
		case res.Namespaced && o.namespace == "":
			return fmt.Errorf("kube.Install: %s %s is namespaced, so it needs metadata.namespace", o.kind, o.name)
		case !res.Namespaced && o.namespace != "":
			return fmt.Errorf("kube.Install: %s %s is cluster-scoped, so it can't have metadata.namespace", o.kind, o.name)
		}
		if err := m.client.Apply(ctx, client.Path(o.apiVersion, res.Name, o.namespace, o.name), m.Name, true, o.body, nil); err != nil {
			return fmt.Errorf("installing %s %s: %w", o.kind, o.name, err)
		}
		m.log.Info("installed", "kind", o.kind, "name", o.name, "namespace", o.namespace)
	}
	return nil
}

func (in *installer) run(context.Context) error { return nil }
func (in *installer) reconciles() bool          { return false }
func (in *installer) synced() bool              { return true }
func (in *installer) controllerName() string    { return "install" }
