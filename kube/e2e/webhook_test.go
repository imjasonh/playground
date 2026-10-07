package e2e_test

import (
	"context"
	"errors"
	"fmt"
	"net"
	"strings"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
	"github.com/imjasonh/playground/kube/k8s"
)

type Gadget struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io"`
	Spec        struct {
		Size  int    `json:"size"`
		Color string `json:"color,omitempty"`
	} `json:"spec"`
}

// gadgets validates and defaults Gadgets, and reconciles them into nothing.
type gadgets struct{}

func (gadgets) Reconcile(context.Context, *Gadget) error { return nil }

func (gadgets) Validate(_ context.Context, g, old *Gadget) error {
	if g.Spec.Size > 10 {
		return fmt.Errorf("size must be at most 10, not %d", g.Spec.Size)
	}
	if old != nil && g.Spec.Size < old.Spec.Size {
		return fmt.Errorf("size can't shrink from %d to %d", old.Spec.Size, g.Spec.Size)
	}
	return nil
}

func (gadgets) Default(_ context.Context, g, _ *Gadget) error {
	if g.Spec.Color == "" {
		g.Spec.Color = "blue"
	}
	return nil
}

// ConfigMapMeta is a ConfigMap without its data.
type ConfigMapMeta struct {
	kube.Object `kube:"apiVersion=v1,kind=ConfigMap"`
}

type stamper struct{}

func (stamper) Default(_ context.Context, cm, _ *ConfigMapMeta) error {
	if cm.Labels == nil {
		cm.Labels = map[string]string{}
	}
	cm.Labels["stamped"] = "true"
	return nil
}

// webhookManager returns a manager whose webhooks the test's API server
// reaches on the loopback interface.
func webhookManager(t *testing.T, name, namespace string) *kube.Manager {
	addr := freeAddr(t)
	t.Cleanup(func() {
		// t.Context is canceled before cleanups run.
		ctx := context.WithoutCancel(t.Context())
		c := e2e.Client(t)
		for _, r := range []string{"validatingwebhookconfigurations", "mutatingwebhookconfigurations"} {
			_ = c.Delete(ctx, client.Path("admissionregistration.k8s.io/v1", r, "", configurationName(name)), client.DeleteOptions{})
		}
	})
	return &kube.Manager{Name: name, Namespace: namespace, WebhookAddr: addr, WebhookURL: "https://" + addr}
}

// configurationName is the name of the webhook configurations of a manager
// called name. The test's kubeconfig puts the manager in the namespace
// default.
func configurationName(name string) string { return name + ".default" }

func TestAdmissionWebhooks(t *testing.T) {
	c := e2e.Client(t)
	ns, other := e2e.Namespace(t, c), e2e.Namespace(t, c)
	e2e.Run(t, webhookManager(t, "admission-e2e", ns), kube.For[Gadget](gadgets{}), kube.Webhooks[ConfigMapMeta](stamper{}))
	gadgetPath := func(name string) string { return client.Path(group+"/v1", "gadgets", ns, name) }
	create := func(name string, size int) error {
		return c.Create(t.Context(), gadgetPath(""), map[string]any{
			"apiVersion": group + "/v1", "kind": "Gadget", "metadata": map[string]any{"name": name}, "spec": map[string]any{"size": size},
		}, nil)
	}

	t.Log("The mutating webhook fills in the color.")
	// The API server enforces each webhook configuration a moment after it's
	// written, and watches validating and mutating ones separately.
	e2e.Eventually(t, 30*time.Second, func() error {
		if err := create("small", 3); err != nil {
			return err
		}
		var g Gadget
		if err := e2e.Get(t.Context(), c, gadgetPath("small"), &g); err != nil {
			return err
		}
		if g.Spec.Color != "blue" {
			_ = c.Delete(t.Context(), gadgetPath("small"), client.DeleteOptions{})
			return fmt.Errorf("color = %q: the mutating webhook isn't enforced yet", g.Spec.Color)
		}
		return nil
	})

	t.Log("The validating webhook rejects a Gadget that's too big, and one that shrinks.")
	var err error
	e2e.Eventually(t, 10*time.Second, func() error {
		if err = create("huge", 11); err == nil {
			_ = c.Delete(t.Context(), gadgetPath("huge"), client.DeleteOptions{})
			return errors.New("the validating webhook isn't enforced yet")
		}
		return nil
	})
	if !strings.Contains(err.Error(), "size must be at most 10, not 11") || !client.IsForbidden(err) {
		t.Errorf("creating a huge Gadget: %v", err)
	}
	patch := func(size int) error {
		return c.Patch(t.Context(), gadgetPath("small"), client.MergePatch, nil, fmt.Appendf(nil, `{"spec":{"size":%d}}`, size), nil)
	}
	if err := patch(2); err == nil || !strings.Contains(err.Error(), "size can't shrink from 3 to 2") {
		t.Errorf("shrinking a Gadget: %v", err)
	}
	if err := patch(5); err != nil {
		t.Errorf("growing a Gadget: %v", err)
	}

	t.Log("The ConfigMap webhook sees only metadata, so its patch keeps the data.")
	for _, n := range []string{ns, other} {
		if err := c.Create(t.Context(), client.Path("v1", "configmaps", n, ""), map[string]any{
			"apiVersion": "v1", "kind": "ConfigMap", "metadata": map[string]any{"name": "settings"}, "data": map[string]string{"color": "green"},
		}, nil); err != nil {
			t.Fatal(err)
		}
	}
	var cm k8s.ConfigMap
	if err := e2e.Get(t.Context(), c, client.Path("v1", "configmaps", ns, "settings"), &cm); err != nil {
		t.Fatal(err)
	}
	if cm.Labels["stamped"] != "true" || cm.Data["color"] != "green" {
		t.Errorf("ConfigMap in the manager's namespace: labels %v, data %v", cm.Labels, cm.Data)
	}
	if err := e2e.Get(t.Context(), c, client.Path("v1", "configmaps", other, "settings"), &cm); err != nil {
		t.Fatal(err)
	}
	if cm.Labels["stamped"] != "" {
		t.Errorf("the webhook changed a ConfigMap outside the manager's namespace: %v", cm.Labels)
	}
}

func TestRemovesWebhooksThatTheProgramDropped(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	path := client.Path("admissionregistration.k8s.io/v1", "validatingwebhookconfigurations", "", configurationName("dropped-e2e"))
	m := webhookManager(t, "dropped-e2e", ns)
	m.Kubeconfig, m.Logger = e2e.Env(t).Kubeconfig, e2e.Logger(t)
	ctx, cancel := context.WithCancel(t.Context())
	done := make(chan error, 1)
	go func() { done <- m.Run(ctx, kube.For[Gadget](gadgets{})) }()
	e2e.Eventually(t, 30*time.Second, func() error {
		select {
		case err := <-done:
			t.Fatalf("the first manager stopped: %v", err)
		default:
		}
		return e2e.Get(t.Context(), c, path, &struct{}{})
	})
	cancel()
	if err := <-done; err != nil {
		t.Fatal(err)
	}

	t.Log("The next version of the program has no webhooks, and deletes the configuration.")
	e2e.Run(t, &kube.Manager{Name: "dropped-e2e", Namespace: ns}, kube.For[Gadget](noWebhooks{}))
	e2e.Eventually(t, 30*time.Second, func() error { return e2e.Gone(t.Context(), c, path) })
}

type noWebhooks struct{}

func (noWebhooks) Reconcile(context.Context, *Gadget) error { return nil }

// slowGadgets is gadgets, except that validating a Gadget named slow waits
// until release is closed.
type slowGadgets struct {
	gadgets
	validating, release chan struct{}
}

func (s slowGadgets) Validate(ctx context.Context, g, old *Gadget) error {
	if g.Name == "slow" {
		select {
		case s.validating <- struct{}{}:
		default:
		}
		<-s.release
	}
	return s.gadgets.Validate(ctx, g, old)
}

func TestWebhooksFinishRequestsWhenTheProgramStops(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	m := webhookManager(t, "draining-e2e", ns)
	m.Kubeconfig, m.Logger = e2e.Env(t).Kubeconfig, e2e.Logger(t)
	r := slowGadgets{validating: make(chan struct{}, 1), release: make(chan struct{})}
	ctx, cancel := context.WithCancel(t.Context())
	defer cancel()
	done := make(chan error, 1)
	go func() { done <- m.Run(ctx, kube.For[Gadget](r)) }()
	gadgetPath := func(name string) string { return client.Path(group+"/v1", "gadgets", ns, name) }
	create := func(name string, size int) error {
		return c.Create(t.Context(), gadgetPath(""), map[string]any{
			"apiVersion": group + "/v1", "kind": "Gadget", "metadata": map[string]any{"name": name}, "spec": map[string]any{"size": size},
		}, nil)
	}
	e2e.Eventually(t, 30*time.Second, func() error {
		err := create("huge", 11)
		switch {
		case err == nil:
			_ = c.Delete(t.Context(), gadgetPath("huge"), client.DeleteOptions{})
			return errors.New("the validating webhook isn't enforced yet")
		case !strings.Contains(err.Error(), "size must be at most 10"):
			return err
		}
		return nil
	})

	t.Log("The program stops while its webhook validates a create, and the create succeeds.")
	created := make(chan error, 1)
	go func() { created <- create("slow", 1) }()
	select {
	case <-r.validating:
	case <-time.After(30 * time.Second):
		t.Fatal("the webhook didn't get the create")
	}
	cancel()
	e2e.Eventually(t, 30*time.Second, func() error {
		conn, err := net.Dial("tcp", m.WebhookAddr)
		if err != nil {
			return nil
		}
		conn.Close()
		return errors.New("the webhook server still accepts connections")
	})
	close(r.release)
	if err := <-created; err != nil {
		t.Errorf("creating a Gadget that the webhook was validating when the program stopped: %v", err)
	}
	if err := <-done; err != nil {
		t.Fatal(err)
	}
}

type Thing struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io,version=v2"`
	Spec        struct {
		Replicas int `json:"replicas"`
	} `json:"spec"`
	Status struct {
		Seen int `json:"seen,omitempty"`
	} `json:"status,omitzero"`
}

// ThingV1 is the first version of Thing, which called replicas size.
type ThingV1 struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io,kind=Thing,version=v1,deprecated"`
	Spec        struct {
		Size int `json:"size"`
	} `json:"spec"`
	Status struct {
		Seen int `json:"seen,omitempty"`
	} `json:"status,omitzero"`
}

func (v *ThingV1) ConvertTo(t *Thing) error {
	if v.Spec.Size < 0 {
		return errors.New("size can't be negative")
	}
	t.Spec.Replicas, t.Status.Seen = v.Spec.Size, v.Status.Seen
	return nil
}

func (v *ThingV1) ConvertFrom(t *Thing) error {
	v.Spec.Size, v.Status.Seen = t.Spec.Replicas, t.Status.Seen
	return nil
}

type things struct{}

func (things) Reconcile(_ context.Context, t *Thing) error {
	t.Status.Seen = t.Spec.Replicas
	return nil
}

func TestConversionWebhook(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	e2e.Run(t, webhookManager(t, "conversion-e2e", ""), kube.For[Thing](things{}, kube.Version[ThingV1]()))
	path := func(version, name string) string { return client.Path(group+"/"+version, "things", ns, name) }

	t.Log("A client creates a Thing with the old version; the controller reconciles the new one.")
	e2e.Eventually(t, 30*time.Second, func() error {
		return c.Create(t.Context(), path("v1", ""), map[string]any{
			"apiVersion": group + "/v1", "kind": "Thing", "metadata": map[string]any{"name": "old"}, "spec": map[string]any{"size": 4},
		}, nil)
	})
	e2e.Eventually(t, 10*time.Second, func() error {
		var v2 Thing
		if err := e2e.Get(t.Context(), c, path("v2", "old"), &v2); err != nil {
			return err
		}
		if v2.Spec.Replicas != 4 || v2.Status.Seen != 4 {
			return fmt.Errorf("v2 spec.replicas = %d, status.seen = %d", v2.Spec.Replicas, v2.Status.Seen)
		}
		return nil
	})
	var v1 ThingV1
	if err := e2e.Get(t.Context(), c, path("v1", "old"), &v1); err != nil {
		t.Fatal(err)
	}
	if v1.Spec.Size != 4 || v1.Status.Seen != 4 {
		t.Errorf("v1 spec.size = %d, status.seen = %d", v1.Spec.Size, v1.Status.Seen)
	}

	t.Log("Objects created with the new version read back with the old one.")
	if err := c.Create(t.Context(), path("v2", ""), map[string]any{
		"apiVersion": group + "/v2", "kind": "Thing", "metadata": map[string]any{"name": "new"}, "spec": map[string]any{"replicas": 7},
	}, nil); err != nil {
		t.Fatal(err)
	}
	if err := e2e.Get(t.Context(), c, path("v1", "new"), &v1); err != nil {
		t.Fatal(err)
	}
	if v1.Spec.Size != 7 {
		t.Errorf("v1 spec.size = %d, want 7", v1.Spec.Size)
	}

	t.Log("A conversion error reaches the client.")
	err := c.Create(t.Context(), path("v1", ""), map[string]any{
		"apiVersion": group + "/v1", "kind": "Thing", "metadata": map[string]any{"name": "bad"}, "spec": map[string]any{"size": -1},
	}, nil)
	if err == nil || !strings.Contains(err.Error(), "size can't be negative") {
		t.Errorf("creating a Thing that can't convert: %v", err)
	}

	var crd struct {
		Spec struct {
			Conversion struct {
				Strategy string `json:"strategy"`
			} `json:"conversion"`
			Versions []struct {
				Name       string `json:"name"`
				Storage    bool   `json:"storage"`
				Deprecated bool   `json:"deprecated"`
			} `json:"versions"`
		} `json:"spec"`
	}
	if err := e2e.Get(t.Context(), c, "/apis/apiextensions.k8s.io/v1/customresourcedefinitions/things."+group, &crd); err != nil {
		t.Fatal(err)
	}
	if crd.Spec.Conversion.Strategy != "Webhook" || len(crd.Spec.Versions) != 2 ||
		crd.Spec.Versions[0].Name != "v2" || !crd.Spec.Versions[0].Storage ||
		crd.Spec.Versions[1].Name != "v1" || crd.Spec.Versions[1].Storage || !crd.Spec.Versions[1].Deprecated {
		t.Errorf("CRD spec = %+v", crd.Spec)
	}
}

type Doohickey struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io"`
	Spec        struct {
		Size int `json:"size"`
	} `json:"spec"`
}

// DoohickeyV1beta1 has the same fields as Doohickey, so the API server
// converts it without a webhook.
type DoohickeyV1beta1 struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io,kind=Doohickey,version=v1beta1"`
	Spec        struct {
		Size int `json:"size"`
	} `json:"spec"`
}

type doohickeys struct{ seen chan int }

func (d doohickeys) Reconcile(_ context.Context, o *Doohickey) error {
	select {
	case d.seen <- o.Spec.Size:
	default:
	}
	return nil
}

func TestVersionsWithoutWebhook(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	r := doohickeys{seen: make(chan int, 10)}
	e2e.Run(t, &kube.Manager{Name: "versions-e2e"}, kube.For[Doohickey](r, kube.Version[DoohickeyV1beta1]()))
	e2e.Eventually(t, 30*time.Second, func() error {
		return c.Create(t.Context(), client.Path(group+"/v1beta1", "doohickeys", ns, ""), map[string]any{
			"apiVersion": group + "/v1beta1", "kind": "Doohickey", "metadata": map[string]any{"name": "d"}, "spec": map[string]any{"size": 9},
		}, nil)
	})
	select {
	case size := <-r.seen:
		if size != 9 {
			t.Errorf("reconciled size %d, want 9", size)
		}
	case <-time.After(10 * time.Second):
		t.Fatal("the Doohickey created as v1beta1 wasn't reconciled")
	}
}
