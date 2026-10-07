package kube

import (
	"slices"
	"time"
)

// Object is embedded, without a json tag, in every struct that represents a
// Kubernetes object. It holds the object's identity and metadata, and its
// kube struct tag names the object's type.
//
// For a type that your controller defines, give a group:
//
//	type Website struct {
//		kube.Object `kube:"group=example.dev"`
//		Spec   WebsiteSpec   `json:"spec"`
//		Status WebsiteStatus `json:"status,omitzero"`
//	}
//
// The kind defaults to the Go type name and the version to v1. When a
// controller that reconciles a type with a group tag starts, it installs a
// CustomResourceDefinition generated from the struct, or updates the one it
// installed before. If something else installed the CustomResourceDefinition,
// the controller uses it as it is. A program that owns the type without
// reconciling it creates the CustomResourceDefinition if it's missing, and
// never changes one that exists. A program that only reads the type never
// creates it.
//
// For a type that already exists, give its apiVersion and kind, and declare
// only the fields you use. The cache stores only those fields:
//
//	type Deployment struct {
//		kube.Object `kube:"apiVersion=apps/v1,kind=Deployment"`
//		Spec struct {
//			Replicas *int32 `json:"replicas,omitempty"`
//		} `json:"spec"`
//	}
//
// Other tag options are version, plural, singular, scope (Namespaced or
// Cluster), shortName, and category. Repeat shortName and category to give
// more than one.
type Object struct {
	TypeMeta
	ObjectMeta `json:"metadata"`
}

func (o *Object) object() *Object { return o }

// Meta returns an Object with a name and labels, for writing desired objects
// as composite literals:
//
//	kube.Own(ctx, &k8s.Service{Object: kube.Meta("web", labels), Spec: spec})
func Meta(name string, labels map[string]string) Object {
	return Object{ObjectMeta: ObjectMeta{Name: name, Labels: labels}}
}

// TypeMeta holds an object's apiVersion and kind. The framework fills them in
// on objects it reads and writes.
type TypeMeta struct {
	APIVersion string `json:"apiVersion,omitempty"`
	Kind       string `json:"kind,omitempty"`
}

// ObjectMeta is the metadata that every Kubernetes object has.
type ObjectMeta struct {
	Name              string            `json:"name,omitempty"`
	Namespace         string            `json:"namespace,omitempty"`
	UID               string            `json:"uid,omitempty"`
	ResourceVersion   string            `json:"resourceVersion,omitempty"`
	Generation        int64             `json:"generation,omitempty"`
	CreationTimestamp time.Time         `json:"creationTimestamp,omitzero"`
	DeletionTimestamp *time.Time        `json:"deletionTimestamp,omitempty"`
	Labels            map[string]string `json:"labels,omitempty"`
	Annotations       map[string]string `json:"annotations,omitempty"`
	OwnerReferences   []OwnerReference  `json:"ownerReferences,omitempty"`
	Finalizers        []string          `json:"finalizers,omitempty"`
}

// Deleting reports whether the object has been deleted and is waiting for
// finalizers to finish.
func (m *ObjectMeta) Deleting() bool { return m.DeletionTimestamp != nil }

// Key returns the object's namespace and name.
func (m *ObjectMeta) Key() Key { return Key{Namespace: m.Namespace, Name: m.Name} }

// OwnerReference points from an object to the object that owns it.
type OwnerReference struct {
	APIVersion         string `json:"apiVersion"`
	Kind               string `json:"kind"`
	Name               string `json:"name"`
	UID                string `json:"uid"`
	Controller         *bool  `json:"controller,omitempty"`
	BlockOwnerDeletion *bool  `json:"blockOwnerDeletion,omitempty"`
}

// Resource is satisfied by *T for every struct T that embeds Object. Generic
// functions in this package use it so that Go can infer both type
// parameters from T alone, as in Get[Deployment](ctx, ns, name).
type Resource[T any] interface {
	*T
	object() *Object
}

// Key identifies an object by namespace and name. Namespace is empty for
// cluster-scoped objects.
type Key struct {
	Namespace string
	Name      string
}

func (k Key) String() string {
	if k.Namespace == "" {
		return k.Name
	}
	return k.Namespace + "/" + k.Name
}

// Condition is one aspect of an object's observed state, in the standard
// Kubernetes form. If an object's status has a Conditions []Condition field,
// the framework keeps a condition of type Synced in it that says whether the
// last reconcile succeeded, and what failed when it didn't.
type Condition struct {
	// Type is the aspect, for example Ready or Synced.
	Type string `json:"type"`
	// Status is True, False, or Unknown.
	Status string `json:"status" kube:"enum=True|False|Unknown"`
	// ObservedGeneration is the metadata.generation this condition describes.
	ObservedGeneration int64 `json:"observedGeneration,omitempty"`
	// LastTransitionTime is when Status last changed.
	LastTransitionTime time.Time `json:"lastTransitionTime,omitzero"`
	// Reason is a CamelCase word for the condition's cause.
	Reason string `json:"reason,omitempty"`
	// Message explains the condition to a person.
	Message string `json:"message,omitempty"`
}

// ListMapKeys makes server-side apply merge condition lists by type.
func (Condition) ListMapKeys() []string { return []string{"type"} }

// Condition status values.
const (
	True    = "True"
	False   = "False"
	Unknown = "Unknown"
)

// SetCondition adds c to conds, or replaces the condition of the same type.
// LastTransitionTime is set to now when the status changes and kept
// otherwise, so a reconcile that observes the same state doesn't produce a
// status write. SetCondition can keep only a time that conds holds, so to
// apply a condition to another object, start conds from that object's copy of
// the condition, which FindCondition returns.
func SetCondition(conds *[]Condition, c Condition) {
	for i, old := range *conds {
		if old.Type != c.Type {
			continue
		}
		switch {
		case old.Status != c.Status:
			c.LastTransitionTime = now()
		case c.LastTransitionTime.IsZero():
			c.LastTransitionTime = old.LastTransitionTime
		}
		(*conds)[i] = c
		return
	}
	if c.LastTransitionTime.IsZero() {
		c.LastTransitionTime = now()
	}
	*conds = append(*conds, c)
}

// FindCondition returns the condition of the given type, or nil.
func FindCondition(conds []Condition, typ string) *Condition {
	i := slices.IndexFunc(conds, func(c Condition) bool { return c.Type == typ })
	if i < 0 {
		return nil
	}
	return &conds[i]
}

// now returns the current time at the one-second precision that Kubernetes
// stores, so a time survives a round trip through the API server unchanged.
func now() time.Time { return time.Now().UTC().Truncate(time.Second) }
