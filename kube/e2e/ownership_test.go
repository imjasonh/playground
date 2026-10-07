package e2e_test

import (
	"context"
	"errors"
	"fmt"
	"maps"
	"slices"
	"strconv"
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

// synced returns a check that the Widget's Synced condition for its current
// generation has the status and a message that contains each of message.
func synced(t *testing.T, c *client.Client, ns, name, status string, message ...string) func() error {
	return func() error {
		w, err := widget(t, c, ns, name)
		if err != nil {
			return err
		}
		s := kube.FindCondition(w.Status.Conditions, "Synced")
		if s == nil || s.Status != status || s.ObservedGeneration != w.Generation {
			return fmt.Errorf("Synced = %+v at generation %d", s, w.Generation)
		}
		for _, m := range message {
			if !strings.Contains(s.Message, m) {
				return fmt.Errorf("Synced message %q doesn't contain %q", s.Message, m)
			}
		}
		return nil
	}
}

// settingsOwner owns a ConfigMap named settings for each Widget of size 1
// or more.
type settingsOwner struct{}

func (settingsOwner) Reconcile(ctx context.Context, w *Widget) error {
	if w.Spec.Size >= 1 {
		kube.Own(ctx, &k8s.ConfigMap{Object: kube.Meta("settings", nil), Data: map[string]string{"from": "controller"}})
	}
	return nil
}

// createSettings creates a ConfigMap named settings, as a person would.
func createSettings(t *testing.T, c *client.Client, ns string) {
	t.Helper()
	if err := c.Create(t.Context(), client.Path("v1", "configmaps", ns, ""), map[string]any{
		"apiVersion": "v1", "kind": "ConfigMap", "metadata": map[string]any{"name": "settings"},
		"data": map[string]string{"from": "person", "important": "yes"},
	}, nil); err != nil {
		t.Fatal(err)
	}
}

// TestOwnLeavesObjectsThatItDidntCreate declares a ConfigMap that a person
// created. The reconcile fails with an error that names the ConfigMap and
// kube.Adopts, and the ConfigMap stays as the person left it, without the
// controller's labels or an owner reference.
func TestOwnLeavesObjectsThatItDidntCreate(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	createSettings(t, c, ns)
	e2e.Run(t, &kube.Manager{Name: "settings-e2e", Namespace: ns}, kube.For[Widget](settingsOwner{}, kube.Named("settings")))
	createWidget(t, c, ns, "w", 1)
	e2e.Eventually(t, 30*time.Second, synced(t, c, ns, "w", kube.False, "ConfigMap.v1 "+ns+"/settings exists", "kube.Adopts()"))
	var cm k8s.ConfigMap
	if err := e2e.Get(t.Context(), c, client.Path("v1", "configmaps", ns, "settings"), &cm); err != nil {
		t.Fatal(err)
	}
	if cm.Data["from"] != "person" || len(cm.Labels) > 0 || len(cm.OwnerReferences) > 0 {
		t.Errorf("ConfigMap has data %v, labels %v, and owner references %v; want the person's data and no labels or owner references", cm.Data, cm.Labels, cm.OwnerReferences)
	}
}

// TestAdoptsTakesOverObjects declares a ConfigMap that a person created,
// from a controller with kube.Adopts. The controller takes the ConfigMap
// over, so it's deleted when the reconcile stops declaring it.
func TestAdoptsTakesOverObjects(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	createSettings(t, c, ns)
	e2e.Run(t, &kube.Manager{Name: "adopter-e2e", Namespace: ns}, kube.For[Widget](settingsOwner{}, kube.Named("adopter"), kube.Adopts()))
	createWidget(t, c, ns, "w", 1)
	path := client.Path("v1", "configmaps", ns, "settings")
	e2e.Eventually(t, 30*time.Second, func() error {
		w, err := widget(t, c, ns, "w")
		if err != nil {
			return err
		}
		var cm k8s.ConfigMap
		if err := e2e.Get(t.Context(), c, path, &cm); err != nil {
			return err
		}
		if cm.Data["from"] != "controller" || cm.Data["important"] != "yes" || cm.Labels[kube.ControllerLabel] != "adopter" ||
			cm.Labels[kube.OwnerUIDLabel] != w.UID || len(cm.OwnerReferences) != 1 || cm.OwnerReferences[0].UID != w.UID {
			return fmt.Errorf("ConfigMap has data %v, labels %v, and owner references %+v", cm.Data, cm.Labels, cm.OwnerReferences)
		}
		return nil
	})

	t.Log("The reconcile stops declaring the ConfigMap, so the controller deletes it.")
	if err := c.Patch(t.Context(), client.Path(group+"/v1", "widgets", ns, "w"), client.MergePatch, nil, []byte(`{"spec":{"size":0}}`), nil); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 30*time.Second, func() error { return e2e.Gone(t.Context(), c, path) })
}

// sharedOwner owns a ConfigMap named shared for each Widget, with the
// widget's name in its data.
type sharedOwner struct{}

func (sharedOwner) Reconcile(ctx context.Context, w *Widget) error {
	kube.Own(ctx, &k8s.ConfigMap{Object: kube.Meta("shared", nil), Data: map[string]string{"owner": w.Name}})
	return nil
}

// TestTwoOwnersDontShareAnObject declares one ConfigMap for two Widgets. The
// first Widget owns it, and the second one's reconcile fails with an error
// that names the first, rather than take the ConfigMap over on every
// reconcile.
func TestTwoOwnersDontShareAnObject(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	e2e.Run(t, &kube.Manager{Name: "sharing-e2e", Namespace: ns}, kube.For[Widget](sharedOwner{}, kube.Named("sharing")))
	path := client.Path("v1", "configmaps", ns, "shared")
	createWidget(t, c, ns, "a", 1)
	var first k8s.ConfigMap
	e2e.Eventually(t, 30*time.Second, func() error {
		if err := e2e.Get(t.Context(), c, path, &first); err != nil {
			return err
		}
		if first.Data["owner"] != "a" {
			return fmt.Errorf("data = %v", first.Data)
		}
		return nil
	})
	createWidget(t, c, ns, "b", 1)
	e2e.Eventually(t, 30*time.Second, synced(t, c, ns, "b", kube.False, "ConfigMap.v1 "+ns+"/shared already has another owner, "+ns+"/a"))
	e2e.Never(t, 3*time.Second, func() error {
		var cm k8s.ConfigMap
		if err := e2e.Get(t.Context(), c, path, &cm); err != nil {
			return err
		}
		if cm.ResourceVersion != first.ResourceVersion {
			return fmt.Errorf("the ConfigMap changed, to data %v and annotations %v", cm.Data, cm.Annotations)
		}
		return nil
	})
}

// targetLabeler labels the ConfigMap named target with each Widget's size.
type targetLabeler struct{}

func (targetLabeler) Reconcile(ctx context.Context, w *Widget) error {
	kube.Apply(ctx, &k8s.ConfigMap{Object: kube.Meta("target", map[string]string{"size": strconv.Itoa(w.Spec.Size)})})
	return nil
}

// TestApplyNeedsAnExistingObject applies a label to a ConfigMap that doesn't
// exist. The reconcile fails, and doesn't create the ConfigMap, which
// nothing would own. Once a person creates it, a retry labels it.
func TestApplyNeedsAnExistingObject(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	e2e.Run(t, &kube.Manager{Name: "target-labeler-e2e", Namespace: ns}, kube.For[Widget](targetLabeler{}, kube.Named("target-labeler")))
	createWidget(t, c, ns, "w", 2)
	path := client.Path("v1", "configmaps", ns, "target")
	e2e.Eventually(t, 30*time.Second, synced(t, c, ns, "w", kube.False, "ConfigMap.v1 "+ns+"/target doesn't exist"))
	if err := e2e.Gone(t.Context(), c, path); err != nil {
		t.Fatal(err)
	}

	t.Log("A person creates the ConfigMap, and a retry labels it.")
	if err := c.Create(t.Context(), client.Path("v1", "configmaps", ns, ""), map[string]any{
		"apiVersion": "v1", "kind": "ConfigMap", "metadata": map[string]any{"name": "target"},
	}, nil); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, time.Minute, func() error {
		var cm k8s.ConfigMap
		if err := e2e.Get(t.Context(), c, path, &cm); err != nil {
			return err
		}
		if cm.Labels["size"] != "2" {
			return fmt.Errorf("labels = %v", cm.Labels)
		}
		return synced(t, c, ns, "w", kube.True)()
	})
}
