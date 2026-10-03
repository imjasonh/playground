package main

import (
	"crypto/rand"
	"encoding/base64"
	"encoding/hex"
	"fmt"
	"slices"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
	"github.com/imjasonh/playground/kube/k8s"
)

func TestMain(m *testing.M) { e2e.Main(m) }

func namespace(name string, labels map[string]string) *k8s.Namespace {
	return &k8s.Namespace{Object: kube.Meta(name, labels)}
}

func TestReplicatesToMatchingNamespaces(t *testing.T) {
	src := &SecretMeta{Object: kube.Meta("creds", nil)}
	src.Namespace = "infra"
	src.Annotations = map[string]string{annotation: "team=web"}
	full := &k8s.Secret{Object: kube.Meta("creds", nil), Type: "Opaque", Data: map[string][]byte{"token": []byte("s3cret")}}
	full.Namespace = "infra"

	ctx, rec := kube.Fake(t.Context(), src, full,
		namespace("infra", map[string]string{"team": "web"}),
		namespace("web-a", map[string]string{"team": "web"}),
		namespace("web-b", map[string]string{"team": "web"}),
		namespace("db", map[string]string{"team": "db"}))
	if err := (replicator{}).Reconcile(ctx, src); err != nil {
		t.Fatal(err)
	}
	var got []string
	for _, s := range kube.Owned[k8s.Secret](rec) {
		got = append(got, s.Namespace+"/"+s.Name+"="+string(s.Data["token"]))
	}
	if want := []string{"web-a/creds=s3cret", "web-b/creds=s3cret"}; !slices.Equal(got, want) {
		t.Errorf("copies = %v, want %v", got, want)
	}
}

func TestIgnoresSecretsWithoutAnnotation(t *testing.T) {
	src := &SecretMeta{Object: kube.Meta("plain", nil)}
	src.Namespace = "infra"
	ctx, rec := kube.Fake(t.Context(), src, namespace("web-a", nil))
	if err := (replicator{}).Reconcile(ctx, src); err != nil {
		t.Fatal(err)
	}
	if copies := kube.Owned[k8s.Secret](rec); len(copies) != 0 {
		t.Errorf("copies = %+v, want none", copies)
	}
}

func TestEndToEnd(t *testing.T) {
	c := e2e.Client(t)
	e2e.Run(t, &kube.Manager{Name: "replicator-e2e"}, kube.For[SecretMeta](replicator{}, kube.Named("replicator")))
	ctx := t.Context()
	b := make([]byte, 3)
	_, _ = rand.Read(b)
	suffix := hex.EncodeToString(b)
	team := "web-" + suffix

	mkns := func(name, label string) string {
		name += "-" + suffix
		ns := map[string]any{"apiVersion": "v1", "kind": "Namespace", "metadata": map[string]any{"name": name, "labels": map[string]string{"team": label}}}
		if err := c.Create(ctx, "/api/v1/namespaces", ns, nil); err != nil {
			t.Fatal(err)
		}
		return name
	}
	src := mkns("src", "infra")
	nsA, nsB, other := mkns("a", team), mkns("b", team), mkns("other", "db")

	srcPath := client.Path("v1", "secrets", src, "creds")
	copyPath := func(ns string) string { return client.Path("v1", "secrets", ns, "creds") }
	if err := c.Create(ctx, client.Path("v1", "secrets", src, ""), map[string]any{
		"apiVersion": "v1", "kind": "Secret",
		"metadata": map[string]any{"name": "creds", "annotations": map[string]string{annotation: "team=" + team}},
		"data":     map[string]string{"token": base64.StdEncoding.EncodeToString([]byte("v1"))},
	}, nil); err != nil {
		t.Fatal(err)
	}

	hasCopy := func(ns, want string) error {
		var s k8s.Secret
		if err := e2e.Get(ctx, c, copyPath(ns), &s); err != nil {
			return err
		}
		if got := string(s.Data["token"]); got != want {
			return fmt.Errorf("%s: token = %q, want %q", ns, got, want)
		}
		return nil
	}
	finalizer := "kube.imjasonh.github.io/replicator"
	hasFinalizer := func(want bool) error {
		var s k8s.Secret
		if err := e2e.Get(ctx, c, srcPath, &s); err != nil {
			return err
		}
		if got := slices.Contains(s.Finalizers, finalizer); got != want {
			return fmt.Errorf("source finalizers = %v, want finalizer %v", s.Finalizers, want)
		}
		return nil
	}

	t.Log("Copies appear in matching namespaces only, and the source gets a finalizer.")
	e2e.Eventually(t, 10*time.Second, func() error {
		for _, ns := range []string{nsA, nsB} {
			if err := hasCopy(ns, "v1"); err != nil {
				return err
			}
		}
		if err := e2e.Gone(ctx, c, copyPath(other)); err != nil {
			return err
		}
		return hasFinalizer(true)
	})

	t.Log("Copies follow changes to the source's data.")
	patch := fmt.Sprintf(`{"data":{"token":%q}}`, base64.StdEncoding.EncodeToString([]byte("v2")))
	if err := c.Patch(ctx, srcPath, client.MergePatch, nil, []byte(patch), nil); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 10*time.Second, func() error {
		if err := hasCopy(nsA, "v2"); err != nil {
			return err
		}
		return hasCopy(nsB, "v2")
	})

	t.Log("A new matching namespace gets a copy; a namespace that stops matching loses its copy.")
	nsC := mkns("c", team)
	if err := c.Patch(ctx, client.Path("v1", "namespaces", "", nsB), client.MergePatch, nil, []byte(`{"metadata":{"labels":{"team":"moved"}}}`), nil); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 10*time.Second, func() error {
		if err := hasCopy(nsC, "v2"); err != nil {
			return err
		}
		return e2e.Gone(ctx, c, copyPath(nsB))
	})

	t.Log("Removing the annotation deletes the copies and the finalizer.")
	if err := c.Patch(ctx, srcPath, client.MergePatch, nil, []byte(fmt.Sprintf(`{"metadata":{"annotations":{%q:null}}}`, annotation)), nil); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 10*time.Second, func() error {
		for _, ns := range []string{nsA, nsC} {
			if err := e2e.Gone(ctx, c, copyPath(ns)); err != nil {
				return err
			}
		}
		return hasFinalizer(false)
	})

	t.Log("Deleting an annotated source deletes its copies before the source goes away.")
	if err := c.Patch(ctx, srcPath, client.MergePatch, nil, []byte(fmt.Sprintf(`{"metadata":{"annotations":{%q:%q}}}`, annotation, "team="+team)), nil); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 10*time.Second, func() error { return hasCopy(nsA, "v2") })
	if err := c.Delete(ctx, srcPath, client.DeleteOptions{}); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 10*time.Second, func() error {
		for _, ns := range []string{nsA, nsC} {
			if err := e2e.Gone(ctx, c, copyPath(ns)); err != nil {
				return err
			}
		}
		return e2e.Gone(ctx, c, srcPath)
	})
	// A reconcile that runs from a cache that hasn't seen the deletion yet
	// must not recreate the Secret while removing its finalizer.
	e2e.Never(t, 2*time.Second, func() error { return e2e.Gone(ctx, c, srcPath) })
}
