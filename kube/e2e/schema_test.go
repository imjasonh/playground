package e2e_test

import (
	"context"
	"fmt"
	"strings"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
)

// BucketRoute is an item of a list that server-side apply merges by name.
// Without maxLength and the list's maxItems, the API server estimates that
// comparing targets costs too much.
type BucketRoute struct {
	Name   string `json:"name"`
	Target string `json:"target,omitempty" kube:"immutable,maxLength=63"`
}

// Bucket has immutable fields that can be absent, an integer narrower than
// int64, and a status without omitzero.
type Bucket struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io"`
	Spec        struct {
		Zone     string `json:"zone,omitempty" kube:"immutable"`
		Note     string `json:"note,omitempty"`
		Settings *struct {
			Class string `json:"class" kube:"immutable"`
		} `json:"settings,omitempty"`
		Routes []BucketRoute `json:"routes,omitempty" kube:"listType=map,listMapKey=name,maxItems=10"`
		Size   uint8         `json:"size,omitempty"`
	} `json:"spec"`
	Status struct {
		Phase string `json:"phase"`
	} `json:"status"`
}

type buckets struct{}

func (buckets) Reconcile(_ context.Context, b *Bucket) error {
	b.Status.Phase = "Ready"
	return nil
}

// Draft has an immutable field in a spec that can be absent.
type Draft struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io"`
	Spec        struct {
		Zone string `json:"zone" kube:"immutable"`
	} `json:"spec,omitzero"`
}

type drafts struct{}

func (drafts) Reconcile(context.Context, *Draft) error { return nil }

func TestSchemaFollowsGoTypes(t *testing.T) {
	c := e2e.Client(t)
	ctx := t.Context()
	ns := e2e.Namespace(t, c)
	e2e.Run(t, &kube.Manager{Name: "schema-e2e"}, kube.For[Bucket](buckets{}), kube.For[Draft](drafts{}))
	path := func(plural, name string) string { return client.Path(group+"/v1", plural, ns, name) }
	create := func(kind, name string, spec map[string]any) {
		t.Helper()
		obj := map[string]any{"apiVersion": group + "/v1", "kind": kind, "metadata": map[string]any{"name": name}}
		if spec != nil {
			obj["spec"] = spec
		}
		e2e.Eventually(t, 30*time.Second, func() error {
			return c.Create(ctx, path(strings.ToLower(kind)+"s", ""), obj, nil)
		})
	}
	patch := func(path, body string) error {
		return c.Patch(ctx, path, client.MergePatch, nil, []byte(body), nil)
	}
	accepted := func(path, body string) {
		t.Helper()
		if err := patch(path, body); err != nil {
			t.Errorf("%s: %v", body, err)
		}
	}
	rejected := func(path, body, field, message string) {
		t.Helper()
		err := patch(path, body)
		if !client.IsInvalid(err) || !strings.Contains(err.Error(), field+": ") || !strings.Contains(err.Error(), message) {
			t.Errorf("%s: err = %v, want %s: ... %s", body, err, field, message)
		}
	}

	t.Log("A Bucket without a status is created, and the program writes its status.")
	create("Bucket", "b1", map[string]any{
		"zone": "a", "settings": map[string]any{"class": "gold"},
		"routes": []any{map[string]any{"name": "r1", "target": "t1"}, map[string]any{"name": "r2"}},
	})
	e2e.Eventually(t, 30*time.Second, func() error {
		var b Bucket
		if err := e2e.Get(ctx, c, path("buckets", "b1"), &b); err != nil {
			return err
		}
		if b.Status.Phase != "Ready" {
			return fmt.Errorf("status.phase = %q", b.Status.Phase)
		}
		return nil
	})

	t.Log("Updates can't change, remove, or add an immutable field, but they can change others.")
	b1 := path("buckets", "b1")
	rejected(b1, `{"spec":{"zone":"b"}}`, "spec.zone", "field is immutable")
	rejected(b1, `{"spec":{"zone":null}}`, "spec.zone", "field is immutable")
	rejected(b1, `{"spec":{"settings":null}}`, "spec.settings.class", "field is immutable")
	rejected(b1, `{"spec":{"routes":[{"name":"r1"},{"name":"r2"}]}}`, "spec.routes[0].target", "field is immutable")
	rejected(b1, `{"spec":{"routes":[{"name":"r1","target":"t1"},{"name":"r2","target":"t2"}]}}`, "spec.routes[1].target", "field is immutable")
	accepted(b1, `{"spec":{"note":"hello","routes":[{"name":"r1","target":"t1"},{"name":"r2"},{"name":"r3","target":"t3"}]}}`)
	create("Bucket", "b2", map[string]any{})
	rejected(path("buckets", "b2"), `{"spec":{"zone":"a"}}`, "spec.zone", "field is immutable")

	t.Log("A uint8 field accepts only the values that a uint8 can hold.")
	rejected(b1, `{"spec":{"size":-1}}`, "spec.size", "greater than or equal to 0")
	rejected(b1, `{"spec":{"size":256}}`, "spec.size", "less than or equal to 255")
	accepted(b1, `{"spec":{"size":255}}`)

	t.Log("When the spec can be absent, updates can't remove it or add it to bypass the rule.")
	create("Draft", "d1", map[string]any{"zone": "a"})
	rejected(path("drafts", "d1"), `{"spec":null}`, "spec.zone", "field is immutable")
	rejected(path("drafts", "d1"), `{"spec":{"zone":"b"}}`, "spec.zone", "field is immutable")
	create("Draft", "d2", nil)
	rejected(path("drafts", "d2"), `{"spec":{"zone":"a"}}`, "spec.zone", "field is immutable")
}
