package e2e_test

import (
	"context"
	"errors"
	"fmt"
	"maps"
	"slices"
	"strings"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
	"github.com/imjasonh/playground/kube/k8s"
)

type Bin struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io"`
	Spec        struct {
		Size int `json:"size"`
	} `json:"spec"`
}

type Crate struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io"`
	Spec        struct {
		Size int `json:"size"`
	} `json:"spec"`
}

func createObject(t *testing.T, c *client.Client, ns, kind, name string, size int) {
	t.Helper()
	e2e.Eventually(t, 30*time.Second, func() error {
		return c.Create(t.Context(), client.Path(group+"/v1", strings.ToLower(kind)+"s", ns, ""), map[string]any{
			"apiVersion": group + "/v1", "kind": kind, "metadata": map[string]any{"name": name}, "spec": map[string]any{"size": size},
		}, nil)
	})
}

// bins owns a ConfigMap named after each Bin and "-bin".
type bins struct{}

func (bins) Reconcile(ctx context.Context, b *Bin) error {
	kube.Own(ctx, &k8s.ConfigMap{Object: kube.Meta(b.Name+"-bin", nil)})
	return nil
}

// crates owns a ConfigMap named after each Crate and "-crate".
type crates struct{}

func (crates) Reconcile(ctx context.Context, c *Crate) error {
	kube.Own(ctx, &k8s.ConfigMap{Object: kube.Meta(c.Name+"-crate", nil)})
	return nil
}

// TestSameNamedControllersKeepEachOthersObjects runs two programs whose
// controllers for Bins and Crates have one name. The ConfigMaps that they own
// for a Bin and a Crate with one name carry the same controller label and
// owner annotation, so each controller's cache of owned objects holds both.
// Neither controller deletes the other's ConfigMap.
func TestSameNamedControllersKeepEachOthersObjects(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	e2e.Run(t, &kube.Manager{Name: "bins-e2e"}, kube.For[Bin](bins{}, kube.Named("storage"), kube.WatchNamespace(ns)))
	e2e.Run(t, &kube.Manager{Name: "crates-e2e"}, kube.For[Crate](crates{}, kube.Named("storage"), kube.WatchNamespace(ns)))
	createObject(t, c, ns, "Bin", "w", 1)
	createObject(t, c, ns, "Crate", "w", 1)
	uids := func() (map[string]string, error) {
		got := map[string]string{}
		for _, name := range []string{"w-bin", "w-crate"} {
			var cm k8s.ConfigMap
			if err := e2e.Get(t.Context(), c, client.Path("v1", "configmaps", ns, name), &cm); err != nil {
				return nil, err
			}
			got[name] = cm.UID
		}
		return got, nil
	}
	var first map[string]string
	e2e.Eventually(t, 30*time.Second, func() (err error) {
		first, err = uids()
		return err
	})
	e2e.Never(t, 3*time.Second, func() error {
		now, err := uids()
		if err != nil {
			return err
		}
		if !maps.Equal(now, first) {
			return fmt.Errorf("ConfigMaps were deleted and created again: UIDs %v, then %v", first, now)
		}
		return nil
	})
}

// spill owns a ConfigMap with its name in another namespace for each Bin,
// which garbage collection can't delete with the Bin. Unless always is set,
// it owns the ConfigMap only while the Bin's size is at least 1.
type spill struct {
	namespace, name string
	always          bool
}

func (r spill) Reconcile(ctx context.Context, b *Bin) error {
	if r.always || b.Spec.Size >= 1 {
		cm := &k8s.ConfigMap{Object: kube.Meta(r.name, nil)}
		cm.Namespace = r.namespace
		kube.Own(ctx, cm)
	}
	return nil
}

// TestCleanupKeepsAnotherControllersObjects runs two controllers for Bins
// that each own a ConfigMap in another namespace, so both ConfigMaps carry
// the Bin's UID. When one controller stops declaring its ConfigMap, it
// deletes that ConfigMap and removes its finalizer from the Bin, and leaves
// the other controller's ConfigMap alone.
func TestCleanupKeepsAnotherControllersObjects(t *testing.T) {
	c := e2e.Client(t)
	ns, other := e2e.Namespace(t, c), e2e.Namespace(t, c)
	e2e.Run(t, &kube.Manager{Name: "spill-e2e"},
		kube.For[Bin](spill{namespace: other, name: "from-a"}, kube.Named("spill-a"), kube.WatchNamespace(ns)),
		kube.For[Bin](spill{namespace: other, name: "from-b", always: true}, kube.Named("spill-b"), kube.WatchNamespace(ns)))
	createObject(t, c, ns, "Bin", "b", 1)
	configMap := func(name string) (*k8s.ConfigMap, error) {
		var cm k8s.ConfigMap
		return &cm, e2e.Get(t.Context(), c, client.Path("v1", "configmaps", other, name), &cm)
	}
	var fromB *k8s.ConfigMap
	e2e.Eventually(t, 30*time.Second, func() (err error) {
		if _, err := configMap("from-a"); err != nil {
			return err
		}
		fromB, err = configMap("from-b")
		return err
	})

	t.Log("The first controller stops declaring its ConfigMap.")
	if err := c.Patch(t.Context(), client.Path(group+"/v1", "bins", ns, "b"), client.MergePatch, nil, []byte(`{"spec":{"size":0}}`), nil); err != nil {
		t.Fatal(err)
	}
	finalizer := kube.FinalizerName("spill-a")
	e2e.Eventually(t, 30*time.Second, func() error {
		if err := e2e.Gone(t.Context(), c, client.Path("v1", "configmaps", other, "from-a")); err != nil {
			return err
		}
		var b Bin
		if err := e2e.Get(t.Context(), c, client.Path(group+"/v1", "bins", ns, "b"), &b); err != nil {
			return err
		}
		if slices.Contains(b.Finalizers, finalizer) {
			return fmt.Errorf("finalizers = %q, want no %s", b.Finalizers, finalizer)
		}
		return nil
	})
	e2e.Never(t, 3*time.Second, func() error {
		cm, err := configMap("from-b")
		if err != nil {
			return err
		}
		if cm.UID != fromB.UID {
			return errors.New("the first controller deleted the second controller's ConfigMap, and the second created it again")
		}
		return nil
	})
}
