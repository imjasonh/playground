package kube

import (
	"context"
	"fmt"
	"net/http"
	"net/http/httptest"
	"slices"
	"strings"
	"sync"
	"testing"

	"github.com/imjasonh/playground/kube/internal/queue"
)

func TestTrigger(t *testing.T) {
	w1, w2 := &widget{}, &widget{}
	w1.Namespace, w1.Name = "shop", "w1"
	w2.Namespace, w2.Name = "shop", "w2"
	p := &policy{Object: Meta("p", nil)}
	ctx, rec := Fake(t.Context(), w1, w2, p)
	if !Trigger[widget](ctx, "shop", "w2") {
		t.Error("Trigger of a widget in the world returned false")
	}
	if Trigger[widget](ctx, "shop", "missing") {
		t.Error("Trigger of a missing widget returned true")
	}
	if !Trigger[policy](ctx, "", "p") {
		t.Error("Trigger of a cluster-scoped object returned false")
	}
	if got, want := Triggered[widget](rec), []Key{{Namespace: "shop", Name: "w2"}}; !slices.Equal(got, want) {
		t.Errorf("Triggered[widget] = %v, want %v", got, want)
	}
	if got, want := Triggered[policy](rec), []Key{{Name: "p"}}; !slices.Equal(got, want) {
		t.Errorf("Triggered[policy] = %v, want %v", got, want)
	}
}

func TestFakeRequest(t *testing.T) {
	w := &widget{}
	w.Namespace, w.Name = "shop", "w1"
	user := UserInfo{Username: "system:serviceaccount:shop:client"}
	ctx, rec := FakeRequest(t.Context(), w, FakeToken{Token: "t", User: user, Audiences: []string{"shop"}})
	if got := Get[widget](ctx, "shop", "w1"); got == nil || got.Name != "w1" {
		t.Errorf("Get = %+v", got)
	}
	if r, err := ReviewToken(ctx, "t", "shop"); err != nil || !r.Authenticated || r.User.Username != user.Username {
		t.Errorf("ReviewToken = %+v, %v", r, err)
	}
	if !Trigger[widget](ctx, "shop", "w1") {
		t.Error("Trigger of a widget in the world returned false")
	}
	if got, want := Triggered[widget](rec), []Key{{Namespace: "shop", Name: "w1"}}; !slices.Equal(got, want) {
		t.Errorf("Triggered = %v, want %v", got, want)
	}
	if err := rec.Err(); err != nil {
		t.Fatalf("Err after reads and a trigger = %v", err)
	}
	Apply(ctx, w)
	if err := rec.Err(); err == nil || !strings.Contains(err.Error(), "kube.Apply can't be called") || context.Cause(ctx) != err {
		t.Errorf("Err after Apply = %v, and the context's cause = %v; want the error that a handler gets in a cluster", err, context.Cause(ctx))
	}
	if got := Applied[widget](rec); len(got) != 0 {
		t.Errorf("Applied = %v, want nothing from a handler", got)
	}

	for _, standby := range []any{FakeStandby{}, &FakeStandby{}} {
		ctx, rec := FakeRequest(t.Context(), w, standby)
		if Trigger[widget](ctx, "shop", "w1") || len(Triggered[widget](rec)) != 0 {
			t.Errorf("Trigger with %T queued a reconcile", standby)
		}
		if Get[widget](ctx, "shop", "w1") == nil {
			t.Errorf("Get with %T found nothing", standby)
		}
	}
	ctx, rec = Fake(t.Context(), w, FakeStandby{})
	if Trigger[widget](ctx, "shop", "w1") || len(Triggered[widget](rec)) != 0 {
		t.Error("Trigger in a Fake context with FakeStandby queued a reconcile")
	}
}

func TestFakeRequestConcurrent(t *testing.T) {
	w := &widget{}
	w.Namespace, w.Name = "shop", "w1"
	d := &deploymentFull{Object: Meta("d", nil)}
	d.Namespace = "shop"
	user := UserInfo{Username: "system:serviceaccount:shop:client"}
	ctx, rec := FakeRequest(t.Context(), w, d, FakeToken{Token: "t", User: user, Audiences: []string{"shop"}})
	h := http.HandlerFunc(func(rw http.ResponseWriter, r *http.Request) {
		ctx := r.Context()
		if Get[deploymentProjection](ctx, "shop", "d") == nil || len(List[widget](ctx)) != 1 {
			http.Error(rw, "a read missed an object", http.StatusInternalServerError)
			return
		}
		if review, _ := ReviewToken(ctx, "t", "shop"); !review.Authenticated {
			http.Error(rw, review.Error, http.StatusUnauthorized)
			return
		}
		token, _, err := RequestToken(ctx, "shop")
		if err != nil || !Trigger[widget](ctx, "shop", "w1") {
			http.Error(rw, fmt.Sprintf("RequestToken: %v, or Trigger returned false", err), http.StatusServiceUnavailable)
			return
		}
		fmt.Fprint(rw, token)
	})
	const n = 8
	tokens := make([]string, n)
	var wg sync.WaitGroup
	for i := range n {
		wg.Go(func() {
			resp := httptest.NewRecorder()
			h.ServeHTTP(resp, httptest.NewRequest(http.MethodPost, "/", nil).WithContext(ctx))
			if resp.Code != http.StatusOK {
				t.Errorf("request %d = %d %q", i, resp.Code, resp.Body)
			}
			tokens[i] = resp.Body.String()
		})
	}
	wg.Wait()
	slices.Sort(tokens)
	if got := slices.Compact(slices.Clone(tokens)); len(got) != n {
		t.Errorf("tokens = %q, want %d different ones", tokens, n)
	}
	if got := Triggered[widget](rec); len(got) != n {
		t.Errorf("Triggered = %v, want %d keys", got, n)
	}
	if err := rec.Err(); err != nil {
		t.Error(err)
	}
}

// widgetView is another type for widgets, such as another program's.
type widgetView struct {
	Object `kube:"group=example.dev,kind=widget"`
}

// triggerable returns a controller for T, set up as if the manager had
// started it, with objs in its cache.
func triggerable[T any, P Resource[T]](t *testing.T, m *Manager, res resolved, objs ...P) *controller[T, P] {
	t.Helper()
	c := For[T, P](nop[T]{}).(*controller[T, P])
	if err := c.prepare(t.Context(), m); err != nil {
		t.Fatal(err)
	}
	c.res = res
	c.q = queue.New[Key](queue.Options{})
	t.Cleanup(c.q.ShutDown)
	c.primary = newInformer[T, P](1, c.ti, res, nil, informerConfig{}, m.log, m.metrics)
	for _, o := range objs {
		c.primary.store.put(o)
	}
	return c
}

func TestManagerTrigger(t *testing.T) {
	m := testManager()
	var stop context.CancelFunc
	m.runCtx, stop = context.WithCancel(t.Context())
	defer stop()
	w := &widget{}
	w.Namespace, w.Name = "shop", "w1"
	widgets := triggerable(t, m, resolved{apiVersion: "example.dev/v1", plural: "widgets", namespaced: true}, w)
	policies := triggerable(t, m, resolved{apiVersion: "example.dev/v1", plural: "networkpolicies"}, &policy{Object: Meta("p", nil)})
	m.controllers = []Controller{widgets, policies, Serve(http.NotFoundHandler())}
	ctx, sc := newWebhookScope(t.Context(), m)
	defer sc.cancel(nil)

	if Trigger[widget](ctx, "shop", "w1") {
		t.Error("Trigger before the controllers started returned true")
	}
	m.started.Store(true)
	if Trigger[widget](ctx, "shop", "missing") {
		t.Error("Trigger of an object that isn't in the cache returned true")
	}
	if Trigger[gizmo](ctx, "shop", "w1") {
		t.Error("Trigger of a kind that no controller reconciles returned true")
	}
	if !Trigger[widget](ctx, "shop", "w1") {
		t.Error("Trigger of a cached object returned false")
	}
	if high, low := widgets.q.Len(); high != 1 || low != 0 {
		t.Errorf("queue = %d high, %d low; want 1 high", high, low)
	}
	if !Trigger[widgetView](ctx, "shop", "w1") {
		t.Error("Trigger through another type of the kind returned false")
	}
	if !Trigger[policy](ctx, "", "p") {
		t.Error("Trigger of a cluster-scoped object returned false")
	}
	if high, _ := policies.q.Len(); high != 1 {
		t.Errorf("policy queue = %d high, want 1", high)
	}

	sh := &shard{}
	m.sharder = &sharder{n: 1, shards: []*shard{sh}}
	widgets.sh = m.sharder
	if Trigger[widget](ctx, "shop", "w1") {
		t.Error("Trigger on a replica that doesn't hold the shard returned true")
	}
	sh.held = true
	if !Trigger[widget](ctx, "shop", "w1") {
		t.Error("Trigger on the replica that holds the shard returned false")
	}
	sh.draining = true
	if Trigger[widget](ctx, "shop", "w1") {
		t.Error("Trigger on a replica that's releasing the shard returned true")
	}
	sh.draining = false
	stop()
	if Trigger[widget](ctx, "shop", "w1") {
		t.Error("Trigger after the manager stopped returned true")
	}
	if high, low := widgets.q.Len(); high != 1 || low != 0 {
		t.Errorf("queue = %d high, %d low; want 1 high", high, low)
	}
	if k, _ := widgets.q.Get(); k != (Key{Namespace: "shop", Name: "w1"}) {
		t.Errorf("queued %v", k)
	}
	if sc.err != nil {
		t.Errorf("a Serve scope can't call Trigger: %v", sc.err)
	}
}
