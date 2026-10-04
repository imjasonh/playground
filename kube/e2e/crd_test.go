package e2e_test

import (
	"bytes"
	"context"
	"encoding/base64"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net/http"
	"slices"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
)

// release runs one release of a program until the returned function stops
// it, which returns the manager's error.
func release(t *testing.T, m *kube.Manager, controllers ...kube.Controller) func() error {
	t.Helper()
	m.Kubeconfig, m.Logger = e2e.Env(t).Kubeconfig, e2e.Logger(t)
	ctx, cancel := context.WithCancel(t.Context())
	done := make(chan error, 1)
	go func() { done <- m.Run(ctx, controllers...) }()
	var once sync.Once
	var err error
	stop := func() error {
		once.Do(func() {
			cancel()
			select {
			case err = <-done:
			case <-time.After(30 * time.Second):
				err = errors.New("manager didn't stop within 30s")
			}
		})
		return err
	}
	t.Cleanup(func() {
		if err := stop(); err != nil {
			t.Errorf("manager: %v", err)
		}
	})
	return stop
}

// failedRelease runs a release of a program that must fail to start, and
// returns its error.
func failedRelease(t *testing.T, m *kube.Manager, controllers ...kube.Controller) error {
	t.Helper()
	m.Kubeconfig, m.Logger = e2e.Env(t).Kubeconfig, e2e.Logger(t)
	ctx, cancel := context.WithTimeout(t.Context(), time.Minute)
	defer cancel()
	err := m.Run(ctx, controllers...)
	if err == nil {
		t.Fatal("the release started")
	}
	return err
}

type crdStatus struct {
	Spec struct {
		Versions []struct {
			Name    string `json:"name"`
			Served  bool   `json:"served"`
			Storage bool   `json:"storage"`
			Schema  struct {
				OpenAPIV3Schema struct {
					Properties struct {
						Spec struct {
							Properties map[string]any `json:"properties"`
						} `json:"spec"`
					} `json:"properties"`
				} `json:"openAPIV3Schema"`
			} `json:"schema"`
		} `json:"versions"`
	} `json:"spec"`
	Status struct {
		StoredVersions []string `json:"storedVersions"`
	} `json:"status"`
}

func getCRD(t *testing.T, c *client.Client, name string) crdStatus {
	t.Helper()
	var crd crdStatus
	if err := e2e.Get(t.Context(), c, "/apis/apiextensions.k8s.io/v1/customresourcedefinitions/"+name, &crd); err != nil {
		t.Fatal(err)
	}
	return crd
}

// waitEstablished waits until the API server serves the CRD at path, with n
// versions.
func waitEstablished(t *testing.T, c *client.Client, path string, n int) {
	t.Helper()
	e2e.Eventually(t, 30*time.Second, func() error {
		var got struct {
			Spec struct {
				Versions []any `json:"versions"`
			} `json:"spec"`
			Status struct {
				Conditions []kube.Condition `json:"conditions"`
			} `json:"status"`
		}
		if err := e2e.Get(t.Context(), c, path, &got); err != nil {
			return err
		}
		if c := kube.FindCondition(got.Status.Conditions, "Established"); len(got.Spec.Versions) != n || c == nil || c.Status != kube.True {
			return fmt.Errorf("the CRD isn't established with %d versions: %+v", n, got)
		}
		return nil
	})
}

// stored returns what etcd holds for a key.
func stored(t *testing.T, key string) string {
	t.Helper()
	body, _ := json.Marshal(map[string]string{"key": base64.StdEncoding.EncodeToString([]byte(key))})
	resp, err := http.Post(e2e.Env(t).EtcdURL+"/v3/kv/range", "application/json", bytes.NewReader(body))
	if err != nil {
		t.Fatal(err)
	}
	defer resp.Body.Close()
	var out struct {
		Kvs []struct {
			Value []byte `json:"value"`
		} `json:"kvs"`
	}
	b, _ := io.ReadAll(resp.Body)
	if err := json.Unmarshal(b, &out); err != nil || len(out.Kvs) == 0 {
		t.Fatalf("etcd has no %s: %s", key, b)
	}
	return string(out.Kvs[0].Value)
}

type GizmoStatus struct {
	Seen int `json:"seen,omitempty"`
}

// GizmoV1 is the first version of Gizmo.
type GizmoV1 struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io,kind=Gizmo,version=v1"`
	Spec        struct {
		Size int `json:"size"`
	} `json:"spec"`
	Status GizmoStatus `json:"status,omitzero"`
}

func (v *GizmoV1) ConvertTo(g *Gizmo) error {
	g.Spec.Replicas, g.Status = v.Spec.Size, v.Status
	return nil
}

func (v *GizmoV1) ConvertFrom(g *Gizmo) error {
	v.Spec.Size, v.Status = g.Spec.Replicas, g.Status
	return nil
}

// Gizmo is the second version, which calls size replicas.
type Gizmo struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io,version=v2"`
	Spec        struct {
		Replicas int `json:"replicas"`
	} `json:"spec"`
	Status GizmoStatus `json:"status,omitzero"`
}

// GizmoV1Unserved is GizmoV1 in the release that stops serving it.
type GizmoV1Unserved struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io,kind=Gizmo,version=v1,unserved"`
	Spec        struct {
		Size int `json:"size"`
	} `json:"spec"`
	Status GizmoStatus `json:"status,omitzero"`
}

func (v *GizmoV1Unserved) ConvertTo(g *Gizmo) error {
	g.Spec.Replicas, g.Status = v.Spec.Size, v.Status
	return nil
}

func (v *GizmoV1Unserved) ConvertFrom(g *Gizmo) error {
	v.Spec.Size, v.Status = g.Spec.Replicas, g.Status
	return nil
}

type gizmosV1 struct{}

func (gizmosV1) Reconcile(_ context.Context, g *GizmoV1) error {
	g.Status.Seen = g.Spec.Size
	return nil
}

type gizmos struct{}

func (gizmos) Reconcile(_ context.Context, g *Gizmo) error {
	g.Status.Seen = g.Spec.Replicas
	return nil
}

// TestCRDUpgrade takes a type through the releases that change its stored
// version and retire the old one.
func TestCRDUpgrade(t *testing.T) {
	c := e2e.Client(t)
	ctx := t.Context()
	ns := e2e.Namespace(t, c)
	addr := freeAddr(t)
	program := func() *kube.Manager {
		return &kube.Manager{Name: "crd-upgrade-e2e", WebhookAddr: addr, WebhookURL: "https://" + addr}
	}
	const crd = "gizmos." + group
	path := func(version, name string) string { return client.Path(group+"/"+version, "gizmos", ns, name) }
	seen := func(version, name string, want int) {
		t.Helper()
		e2e.Eventually(t, 30*time.Second, func() error {
			var g struct {
				Status GizmoStatus `json:"status"`
			}
			if err := e2e.Get(ctx, c, path(version, name), &g); err != nil {
				return err
			}
			if g.Status.Seen != want {
				return fmt.Errorf("%s status.seen = %d, want %d", name, g.Status.Seen, want)
			}
			return nil
		})
	}
	managedVersions := func(name string) []string {
		t.Helper()
		var o struct {
			Metadata struct {
				ManagedFields []struct {
					APIVersion string `json:"apiVersion"`
				} `json:"managedFields"`
			} `json:"metadata"`
		}
		if err := e2e.Get(ctx, c, path("v2", name), &o); err != nil {
			t.Fatal(err)
		}
		var vs []string
		for _, e := range o.Metadata.ManagedFields {
			vs = append(vs, strings.TrimPrefix(e.APIVersion, group+"/"))
		}
		return vs
	}

	t.Log("Release 1 stores v1. A user applies Gizmos, and the controller writes their status.")
	stop := release(t, program(), kube.For[GizmoV1](gizmosV1{}))
	for i, name := range []string{"a", "b"} {
		e2e.Eventually(t, 30*time.Second, func() error {
			return c.Apply(ctx, path("v1", name), "user", true, map[string]any{
				"apiVersion": group + "/v1", "kind": "Gizmo", "metadata": map[string]any{"name": name}, "spec": map[string]any{"size": i + 1},
			}, nil)
		})
		seen("v1", name, i+1)
	}
	if err := stop(); err != nil {
		t.Fatal(err)
	}

	t.Log("A release that drops v1 while objects are stored in it doesn't start.")
	err := failedRelease(t, program(), kube.For[Gizmo](gizmos{}))
	t.Log(err)
	if !strings.Contains(err.Error(), "objects may still be stored as v1") {
		t.Fatalf("dropping v1 too early: %v", err)
	}

	t.Log("Release 2 stores v2 and still serves v1. The framework rewrites the stored objects.")
	stop = release(t, program(), kube.For[Gizmo](gizmos{}, kube.Version[GizmoV1]()))
	e2e.Eventually(t, time.Minute, func() error {
		if got := getCRD(t, c, crd).Status.StoredVersions; !slices.Equal(got, []string{"v2"}) {
			return fmt.Errorf("status.storedVersions = %v", got)
		}
		return nil
	})
	for _, name := range []string{"a", "b"} {
		if s := stored(t, "/registry/"+group+"/gizmos/"+ns+"/"+name); !strings.Contains(s, `"apiVersion":"`+group+`/v2"`) {
			t.Errorf("etcd has %s as %.80s", name, s)
		}
	}
	if vs := managedVersions("a"); !slices.Contains(vs, "v1") {
		t.Fatalf("managedFields versions = %v, want some v1 entries", vs)
	}
	if err := stop(); err != nil {
		t.Fatal(err)
	}

	t.Log("A release that drops v1 while managedFields entries name it doesn't start.")
	err = failedRelease(t, program(), kube.For[Gizmo](gizmos{}))
	t.Log(err)
	if !strings.Contains(err.Error(), "managedFields entries") {
		t.Fatalf("dropping v1 with managedFields entries: %v", err)
	}

	t.Log("Release 3 stops serving v1, and the framework removes the managedFields entries that name it.")
	stop = release(t, program(), kube.For[Gizmo](gizmos{}, kube.Version[GizmoV1Unserved]()))
	e2e.Eventually(t, time.Minute, func() error {
		if err := c.Get(ctx, path("v1", "a"), &map[string]any{}); !client.IsNotFound(err) {
			return fmt.Errorf("reading v1: %v", err)
		}
		for _, name := range []string{"a", "b"} {
			if vs := managedVersions(name); slices.Contains(vs, "v1") {
				return fmt.Errorf("%s managedFields versions = %v", name, vs)
			}
		}
		return nil
	})
	if err := stop(); err != nil {
		t.Fatal(err)
	}

	t.Log("Release 4 removes v1, and server-side apply still works.")
	release(t, program(), kube.For[Gizmo](gizmos{}))
	e2e.Eventually(t, 30*time.Second, func() error {
		got := getCRD(t, c, crd)
		if len(got.Spec.Versions) != 1 || got.Spec.Versions[0].Name != "v2" {
			return fmt.Errorf("CRD versions = %+v", got.Spec.Versions)
		}
		return nil
	})
	if err := c.Apply(ctx, path("v2", "a"), "user", true, map[string]any{
		"apiVersion": group + "/v2", "kind": "Gizmo", "metadata": map[string]any{"name": "a"}, "spec": map[string]any{"replicas": 5},
	}, nil); err != nil {
		t.Fatalf("server-side apply after removing v1: %v", err)
	}
	seen("v2", "a", 5)
}

// Contraption is the type in a release that declares every field.
type Contraption struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io"`
	Spec        struct {
		Size  int    `json:"size"`
		Color string `json:"color,omitempty"`
		Note  string `json:"note,omitempty"`
	} `json:"spec"`
	Status struct {
		Seen int `json:"seen,omitempty"`
	} `json:"status,omitzero"`
}

// ContraptionTrimmed is the type in a release without color and note: an
// older release, or one that removed them.
type ContraptionTrimmed struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io,kind=Contraption"`
	Spec        struct {
		Size int `json:"size"`
	} `json:"spec"`
	Status struct {
		Seen int `json:"seen,omitempty"`
	} `json:"status,omitzero"`
}

type contraptions struct{}

func (contraptions) Reconcile(_ context.Context, o *Contraption) error {
	o.Status.Seen = o.Spec.Size
	return nil
}

type trimmedContraptions struct{}

func (trimmedContraptions) Reconcile(_ context.Context, o *ContraptionTrimmed) error {
	o.Status.Seen = o.Spec.Size
	return nil
}

func TestCRDKeepsFieldsThatObjectsUse(t *testing.T) {
	c := e2e.Client(t)
	ctx := t.Context()
	ns := e2e.Namespace(t, c)
	const crd = "contraptions." + group
	path := client.Path(group+"/v1", "contraptions", ns, "c")
	fields := func() map[string]any {
		return getCRD(t, c, crd).Spec.Versions[0].Schema.OpenAPIV3Schema.Properties.Spec.Properties
	}
	seen := func(want int) {
		t.Helper()
		e2e.Eventually(t, 30*time.Second, func() error {
			var o Contraption
			if err := e2e.Get(ctx, c, path, &o); err != nil {
				return err
			}
			if o.Status.Seen != want {
				return fmt.Errorf("status.seen = %d, want %d", o.Status.Seen, want)
			}
			return nil
		})
	}

	t.Log("Release 1 declares color and note. A Contraption sets color.")
	stop := release(t, &kube.Manager{Name: "crd-fields-e2e"}, kube.For[Contraption](contraptions{}))
	e2e.Eventually(t, 30*time.Second, func() error {
		return c.Create(ctx, client.Path(group+"/v1", "contraptions", ns, ""), map[string]any{
			"apiVersion": group + "/v1", "kind": "Contraption", "metadata": map[string]any{"name": "c"}, "spec": map[string]any{"size": 1, "color": "red"},
		}, nil)
	})
	seen(1)
	if err := stop(); err != nil {
		t.Fatal(err)
	}

	t.Log("Release 2 declares neither. The CRD keeps color, which an object sets, and drops note.")
	stop = release(t, &kube.Manager{Name: "crd-fields-e2e"}, kube.For[ContraptionTrimmed](trimmedContraptions{}))
	e2e.Eventually(t, 30*time.Second, func() error {
		f := fields()
		if _, ok := f["note"]; ok {
			return errors.New("the CRD still has note")
		}
		if _, ok := f["color"]; !ok {
			return errors.New("the CRD lost color")
		}
		return nil
	})
	if err := c.Patch(ctx, path, client.MergePatch, nil, []byte(`{"spec":{"size":2}}`), nil); err != nil {
		t.Fatal(err)
	}
	seen(2)
	var o Contraption
	if err := e2e.Get(ctx, c, path, &o); err != nil {
		t.Fatal(err)
	}
	if o.Spec.Color != "red" {
		t.Errorf("after writes in release 2, spec.color = %q, want red", o.Spec.Color)
	}
	if err := stop(); err != nil {
		t.Fatal(err)
	}

	t.Log("Release 3 declares note again.")
	release(t, &kube.Manager{Name: "crd-fields-e2e"}, kube.For[Contraption](contraptions{}))
	e2e.Eventually(t, 30*time.Second, func() error {
		if _, ok := fields()["note"]; !ok {
			return errors.New("the CRD doesn't have note")
		}
		return nil
	})
}

// Sprocket is the newer version of a type.
type Sprocket struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io,version=v2"`
	Spec        struct {
		Size int `json:"size"`
	} `json:"spec"`
}

// SprocketV1 is the older version, which the older release reconciles.
type SprocketV1 struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io,kind=Sprocket,version=v1"`
	Spec        struct {
		Size int `json:"size"`
	} `json:"spec"`
}

type sprockets struct{}

func (sprockets) Reconcile(context.Context, *Sprocket) error { return nil }

type oldSprockets struct{ seen chan int }

func (s oldSprockets) Reconcile(_ context.Context, o *SprocketV1) error {
	select {
	case s.seen <- o.Spec.Size:
	default:
	}
	return nil
}

func TestCRDFromNewerRelease(t *testing.T) {
	c := e2e.Client(t)
	ctx := t.Context()
	ns := e2e.Namespace(t, c)
	const crd = "sprockets." + group

	t.Log("The newer release stores v2.")
	stop := release(t, &kube.Manager{Name: "crd-rollback-e2e"}, kube.For[Sprocket](sprockets{}, kube.Version[SprocketV1]()))
	e2e.Eventually(t, 30*time.Second, func() error {
		return c.Create(ctx, client.Path(group+"/v2", "sprockets", ns, ""), map[string]any{
			"apiVersion": group + "/v2", "kind": "Sprocket", "metadata": map[string]any{"name": "s"}, "spec": map[string]any{"size": 3},
		}, nil)
	})
	if err := stop(); err != nil {
		t.Fatal(err)
	}

	t.Log("Rolling back to a release that only knows v1 leaves the CRD alone and still reconciles.")
	r := oldSprockets{seen: make(chan int, 10)}
	release(t, &kube.Manager{Name: "crd-rollback-e2e"}, kube.For[SprocketV1](r))
	select {
	case size := <-r.seen:
		if size != 3 {
			t.Errorf("reconciled size %d, want 3", size)
		}
	case <-time.After(30 * time.Second):
		t.Fatal("the older release didn't reconcile")
	}
	got := getCRD(t, c, crd)
	if len(got.Spec.Versions) != 2 || got.Spec.Versions[0].Name != "v2" || !got.Spec.Versions[0].Storage {
		t.Errorf("CRD versions after the rollback = %+v", got.Spec.Versions)
	}
}

// crdMeta is the metadata of a CustomResourceDefinition.
type crdMeta struct {
	Metadata struct {
		ResourceVersion string            `json:"resourceVersion"`
		Labels          map[string]string `json:"labels"`
		ManagedFields   []struct {
			Manager string `json:"manager"`
		} `json:"managedFields"`
	} `json:"metadata"`
}

func (m crdMeta) managedBy() string { return m.Metadata.Labels["kube.imjasonh.github.io/managed-by"] }

// Receipt is a type that programs own without reconciling it.
type Receipt struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io"`
	Spec        struct {
		ConfigMap string `json:"configMap"`
	} `json:"spec"`
}

// CheckedReceipt is Receipt in a program that reconciles it.
type CheckedReceipt struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io,kind=Receipt"`
	Spec        struct {
		ConfigMap string `json:"configMap"`
	} `json:"spec"`
	Status struct {
		Checked bool `json:"checked,omitempty"`
	} `json:"status,omitzero"`
}

type receipts struct{}

func (receipts) Reconcile(ctx context.Context, cm *ConfigMapMeta) error {
	r := &Receipt{Object: kube.Meta(cm.Name, nil)}
	r.Spec.ConfigMap = cm.Name
	kube.Own(ctx, r)
	return nil
}

type receiptChecker struct{}

func (receiptChecker) Reconcile(_ context.Context, r *CheckedReceipt) error {
	r.Status.Checked = true
	return nil
}

func TestCRDForOwnedType(t *testing.T) {
	c := e2e.Client(t)
	ctx := t.Context()
	crdPath := "/apis/apiextensions.k8s.io/v1/customresourcedefinitions/receipts." + group
	if err := e2e.Gone(ctx, c, crdPath); err != nil {
		t.Fatal(err)
	}

	t.Log("Two programs that own Receipts without reconciling them start at once, each in its own namespace. One creates the CRD, and both write Receipts.")
	owners := map[string]string{}
	for _, name := range []string{"receipts-a-e2e", "receipts-b-e2e"} {
		ns := e2e.Namespace(t, c)
		owners[name] = ns
		e2e.Run(t, &kube.Manager{Name: name, Namespace: ns}, kube.For[ConfigMapMeta](receipts{}, kube.Named("receipts"), kube.Owns[Receipt]()))
	}
	for _, ns := range owners {
		cm := map[string]any{"apiVersion": "v1", "kind": "ConfigMap", "metadata": map[string]any{"name": "cm"}}
		if err := c.Create(ctx, client.Path("v1", "configmaps", ns, ""), cm, nil); err != nil {
			t.Fatal(err)
		}
	}
	e2e.Eventually(t, 30*time.Second, func() error {
		for _, ns := range owners {
			var r Receipt
			if err := e2e.Get(ctx, c, client.Path(group+"/v1", "receipts", ns, "cm"), &r); err != nil {
				return err
			}
		}
		return nil
	})
	var meta crdMeta
	if err := e2e.Get(ctx, c, crdPath, &meta); err != nil {
		t.Fatal(err)
	}
	if _, ok := owners[meta.managedBy()]; !ok {
		t.Errorf("the CRD is managed by %q, want one of the programs that own Receipts", meta.managedBy())
	}
	if got := getCRD(t, c, "receipts."+group); len(got.Spec.Versions) != 1 || got.Spec.Versions[0].Name != "v1" || !got.Spec.Versions[0].Storage {
		t.Errorf("CRD versions = %+v, want v1 alone", got.Spec.Versions)
	}

	t.Log("A program that reconciles Receipts installs its own CRD over the created one, and reconciles the Receipts that exist.")
	e2e.Run(t, &kube.Manager{Name: "receipt-checker-e2e"}, kube.For[CheckedReceipt](receiptChecker{}))
	e2e.Eventually(t, 30*time.Second, func() error {
		if err := e2e.Get(ctx, c, crdPath, &meta); err != nil {
			return err
		}
		if meta.managedBy() != "receipt-checker-e2e" {
			return fmt.Errorf("the CRD is managed by %q", meta.managedBy())
		}
		for _, ns := range owners {
			var r CheckedReceipt
			if err := e2e.Get(ctx, c, client.Path(group+"/v1", "receipts", ns, "cm"), &r); err != nil {
				return err
			}
			if !r.Status.Checked {
				return fmt.Errorf("the Receipt in %s isn't checked", ns)
			}
		}
		return nil
	})
}

// Ledger and LedgerV1 have the same fields, so the API server converts
// between them without a webhook.
type Ledger struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io,version=v2"`
	Spec        struct {
		ConfigMap string `json:"configMap"`
	} `json:"spec"`
}

type LedgerV1 struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io,kind=Ledger,version=v1"`
	Spec        struct {
		ConfigMap string `json:"configMap"`
	} `json:"spec"`
}

type ledgers struct{}

func (ledgers) Reconcile(context.Context, *Ledger) error { return nil }

// ledgerKeeper owns a v1 Ledger for each ConfigMap, and counts the Ledgers
// in the ConfigMap's namespace.
type ledgerKeeper struct{ seen atomic.Int64 }

func (k *ledgerKeeper) Reconcile(ctx context.Context, cm *ConfigMapMeta) error {
	k.seen.Store(int64(len(kube.List[LedgerV1](ctx, kube.InNamespace(cm.Namespace)))))
	l := &LedgerV1{Object: kube.Meta(cm.Name, nil)}
	l.Spec.ConfigMap = cm.Name
	kube.Own(ctx, l)
	return nil
}

func TestCRDForOwnedTypeLeavesExistingCRD(t *testing.T) {
	c := e2e.Client(t)
	ctx := t.Context()
	ns := e2e.Namespace(t, c)
	const crd = "ledgers." + group
	crdPath := "/apis/apiextensions.k8s.io/v1/customresourcedefinitions/" + crd

	t.Log("A program that reconciles Ledgers installs their CRD, with v2 and v1, and stops.")
	stop := release(t, &kube.Manager{Name: "ledgers-e2e"}, kube.For[Ledger](ledgers{}, kube.Version[LedgerV1]()))
	waitEstablished(t, c, crdPath, 2)
	if err := stop(); err != nil {
		t.Fatal(err)
	}
	var before crdMeta
	if err := e2e.Get(ctx, c, crdPath, &before); err != nil {
		t.Fatal(err)
	}

	t.Log("A program that knows only v1, and owns and lists Ledgers without reconciling them, uses the CRD as it is.")
	k := &ledgerKeeper{}
	e2e.Run(t, &kube.Manager{Name: "ledger-keeper-e2e", Namespace: ns}, kube.For[ConfigMapMeta](k, kube.Named("ledger-keeper")))
	cm := map[string]any{"apiVersion": "v1", "kind": "ConfigMap", "metadata": map[string]any{"name": "cm"}}
	if err := c.Create(ctx, client.Path("v1", "configmaps", ns, ""), cm, nil); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 30*time.Second, func() error {
		var l LedgerV1
		if err := e2e.Get(ctx, c, client.Path(group+"/v1", "ledgers", ns, "cm"), &l); err != nil {
			return err
		}
		if n := k.seen.Load(); n != 1 {
			return fmt.Errorf("the program listed %d Ledgers, want 1", n)
		}
		return nil
	})
	var after crdMeta
	if err := e2e.Get(ctx, c, crdPath, &after); err != nil {
		t.Fatal(err)
	}
	if after.Metadata.ResourceVersion != before.Metadata.ResourceVersion {
		t.Errorf("the CRD changed: managed by %q, managers %+v", after.managedBy(), after.Metadata.ManagedFields)
	}
	if got := getCRD(t, c, crd); len(got.Spec.Versions) != 2 || got.Spec.Versions[0].Name != "v2" || !got.Spec.Versions[0].Storage {
		t.Errorf("CRD versions = %+v, want v2, stored, and v1", got.Spec.Versions)
	}
}

// Memo is a type that one program reconciles and another reads.
type Memo struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io"`
	Spec        struct {
		Title string `json:"title"`
		Body  string `json:"body,omitempty"`
	} `json:"spec"`
	Status struct {
		Read bool `json:"read,omitempty"`
	} `json:"status,omitzero"`
}

// MemoTitle declares only the title of a Memo.
type MemoTitle struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io,kind=Memo"`
	Spec        struct {
		Title string `json:"title"`
	} `json:"spec"`
}

type memos struct{}

func (memos) Reconcile(_ context.Context, m *Memo) error {
	m.Status.Read = true
	return nil
}

// memoReader counts the Memos in each ConfigMap's namespace, and reads the
// one with the ConfigMap's name, without owning or reconciling Memos.
type memoReader struct{ runs, seen atomic.Int64 }

func (r *memoReader) Reconcile(ctx context.Context, cm *ConfigMapMeta) error {
	r.runs.Add(1)
	if _, err := kube.Fetch[MemoTitle](ctx, cm.Namespace, cm.Name); err != nil {
		return err
	}
	r.seen.Store(int64(len(kube.List[MemoTitle](ctx, kube.InNamespace(cm.Namespace)))))
	return nil
}

func TestCRDNotCreatedByReader(t *testing.T) {
	c := e2e.Client(t)
	ctx := t.Context()
	ns := e2e.Namespace(t, c)
	crdPath := "/apis/apiextensions.k8s.io/v1/customresourcedefinitions/memos." + group
	if err := e2e.Gone(ctx, c, crdPath); err != nil {
		t.Fatal(err)
	}

	t.Log("A program that reads only the titles of Memos starts first. Its reconciles fail and retry, and it doesn't create the CRD.")
	r := &memoReader{}
	e2e.Run(t, &kube.Manager{Name: "memo-reader-e2e", Namespace: ns}, kube.For[ConfigMapMeta](r, kube.Named("memo-reader")))
	cm := map[string]any{"apiVersion": "v1", "kind": "ConfigMap", "metadata": map[string]any{"name": "cm"}}
	if err := c.Create(ctx, client.Path("v1", "configmaps", ns, ""), cm, nil); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 30*time.Second, func() error {
		if err := e2e.Gone(ctx, c, crdPath); err != nil {
			t.Fatalf("after %d reconciles of the reader: %v", r.runs.Load(), err)
		}
		if n := r.runs.Load(); n < 3 {
			return fmt.Errorf("the reader reconciled %d times", n)
		}
		return nil
	})

	t.Log("A program that reconciles Memos installs their CRD. A Memo keeps its body, the program reconciles it, and the reader lists it.")
	e2e.Run(t, &kube.Manager{Name: "memos-e2e"}, kube.For[Memo](memos{}))
	e2e.Eventually(t, 30*time.Second, func() error {
		return c.Create(ctx, client.Path(group+"/v1", "memos", ns, ""), map[string]any{
			"apiVersion": group + "/v1", "kind": "Memo", "metadata": map[string]any{"name": "cm"}, "spec": map[string]any{"title": "Lunch", "body": "Noon"},
		}, nil)
	})
	e2e.Eventually(t, time.Minute, func() error {
		var m Memo
		if err := e2e.Get(ctx, c, client.Path(group+"/v1", "memos", ns, "cm"), &m); err != nil {
			return err
		}
		if m.Spec.Body != "Noon" || !m.Status.Read {
			return fmt.Errorf("the Memo has body %q and status.read %v", m.Spec.Body, m.Status.Read)
		}
		if n := r.seen.Load(); n != 1 {
			return fmt.Errorf("the reader listed %d Memos, want 1", n)
		}
		return nil
	})
	var meta crdMeta
	if err := e2e.Get(ctx, c, crdPath, &meta); err != nil {
		t.Fatal(err)
	}
	if meta.managedBy() != "memos-e2e" {
		t.Errorf("the CRD is managed by %q, want memos-e2e", meta.managedBy())
	}
}

// Voucher is a type that a program owns without reconciling it.
type Voucher struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io"`
	Spec        struct {
		ConfigMap string `json:"configMap"`
	} `json:"spec"`
}

// VoucherV2 is Voucher in a program that reconciles only v2 of it.
type VoucherV2 struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io,kind=Voucher,version=v2"`
	Spec        struct {
		ConfigMap string `json:"configMap"`
	} `json:"spec"`
}

type vouchersV2 struct{}

func (vouchersV2) Reconcile(context.Context, *VoucherV2) error { return nil }

// voucherIssuer owns a Voucher for each ConfigMap.
type voucherIssuer struct{ runs atomic.Int64 }

func (i *voucherIssuer) Reconcile(ctx context.Context, cm *ConfigMapMeta) error {
	i.runs.Add(1)
	v := &Voucher{Object: kube.Meta(cm.Name, nil)}
	v.Spec.ConfigMap = cm.Name
	kube.Own(ctx, v)
	return nil
}

func TestCRDForOwnedTypeDoesntBlockStartup(t *testing.T) {
	c := e2e.Client(t)
	ctx := t.Context()
	ns := e2e.Namespace(t, c)
	const crd = "vouchers." + group
	crdPath := "/apis/apiextensions.k8s.io/v1/customresourcedefinitions/" + crd

	t.Log("A program that reconciles only v2 of Vouchers installs their CRD, and stops.")
	stop := release(t, &kube.Manager{Name: "vouchers-e2e"}, kube.For[VoucherV2](vouchersV2{}))
	waitEstablished(t, c, crdPath, 1)
	if err := stop(); err != nil {
		t.Fatal(err)
	}

	t.Log("A program that owns v1 Vouchers with kube.Owns can't create their CRD, because it exists without v1. The program starts anyway, and its reconciles fail and retry.")
	issuer := &voucherIssuer{}
	e2e.Run(t, &kube.Manager{Name: "voucher-issuer-e2e", Namespace: ns}, kube.For[ConfigMapMeta](issuer, kube.Named("voucher-issuer"), kube.Owns[Voucher]()))
	cm := map[string]any{"apiVersion": "v1", "kind": "ConfigMap", "metadata": map[string]any{"name": "cm"}}
	if err := c.Create(ctx, client.Path("v1", "configmaps", ns, ""), cm, nil); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 30*time.Second, func() error {
		if n := issuer.runs.Load(); n < 2 {
			return fmt.Errorf("the issuer reconciled %d times", n)
		}
		return nil
	})

	t.Log("Once the CRD is deleted, the next Own creates it with v1, and the program writes the Voucher.")
	if err := c.Delete(ctx, crdPath, client.DeleteOptions{}); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, time.Minute, func() error {
		var v Voucher
		return e2e.Get(ctx, c, client.Path(group+"/v1", "vouchers", ns, "cm"), &v)
	})
	var meta crdMeta
	if err := e2e.Get(ctx, c, crdPath, &meta); err != nil {
		t.Fatal(err)
	}
	if meta.managedBy() != "voucher-issuer-e2e" {
		t.Errorf("the CRD is managed by %q, want voucher-issuer-e2e", meta.managedBy())
	}
	if got := getCRD(t, c, crd); len(got.Spec.Versions) != 1 || got.Spec.Versions[0].Name != "v1" {
		t.Errorf("CRD versions = %+v, want v1 alone", got.Spec.Versions)
	}
}
