package e2e_test

import (
	"context"
	"fmt"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
	"github.com/imjasonh/playground/kube/k8s"
)

// labeler reconciles each Widget into a ConfigMap whose label value is as
// long as the widget's size, so the API server rejects the ConfigMap when the
// size is over 63, and records what kube.LastError returns in each
// reconcile.
type labeler struct {
	mu   sync.Mutex
	seen map[string][]lastError
}

type lastError struct {
	size int
	err  error
}

func (l *labeler) Reconcile(ctx context.Context, w *Widget) error {
	l.mu.Lock()
	if l.seen == nil {
		l.seen = map[string][]lastError{}
	}
	key := w.Namespace + "/" + w.Name
	l.seen[key] = append(l.seen[key], lastError{w.Spec.Size, kube.LastError(ctx)})
	l.mu.Unlock()
	kube.Own(ctx, &k8s.ConfigMap{Object: kube.Meta(w.Name, map[string]string{"size": strings.Repeat("x", w.Spec.Size)})})
	return nil
}

// first returns the first reconcile of key at size, or false if there was
// none.
func (l *labeler) first(key string, size int) (lastError, bool) {
	l.mu.Lock()
	defer l.mu.Unlock()
	for _, s := range l.seen[key] {
		if s.size == size {
			return s, true
		}
	}
	return lastError{}, false
}

func TestRetrySeesLastError(t *testing.T) {
	c := e2e.Client(t)
	l := &labeler{}
	e2e.Run(t, &kube.Manager{Name: "lasterror-e2e", DisableStreamingLists: true}, kube.For[Widget](l, kube.Named("lasterror")))
	ns := e2e.Namespace(t, c)
	key := ns + "/w"
	tooLong := "must be no more than 63"
	createWidget(t, c, ns, "w", 64)

	e2e.Eventually(t, 10*time.Second, func() error {
		l.mu.Lock()
		defer l.mu.Unlock()
		seen := l.seen[key]
		if len(seen) < 2 {
			return fmt.Errorf("reconciled %d times, want a retry", len(seen))
		}
		if seen[0].err != nil {
			t.Fatalf("the first reconcile's LastError = %v, want nil", seen[0].err)
		}
		if err := seen[1].err; err == nil || !strings.Contains(err.Error(), tooLong) {
			t.Fatalf("the retry's LastError = %v, want the API server's rejection of the ConfigMap", err)
		}
		return nil
	})

	t.Log("The reconcile after the failed one sees its error, even after a change.")
	patchSize := func(size int) {
		t.Helper()
		if err := c.Patch(t.Context(), client.Path(group+"/v1", "widgets", ns, "w"), client.MergePatch, nil, fmt.Appendf(nil, `{"spec":{"size":%d}}`, size), nil); err != nil {
			t.Fatal(err)
		}
	}
	patchSize(3)
	e2e.Eventually(t, 10*time.Second, func() error {
		var cm k8s.ConfigMap
		if err := e2e.Get(t.Context(), c, client.Path("v1", "configmaps", ns, "w"), &cm); err != nil {
			return err
		}
		if cm.Labels["size"] != "xxx" {
			return fmt.Errorf("ConfigMap labels = %v", cm.Labels)
		}
		return nil
	})
	if s, _ := l.first(key, 3); s.err == nil || !strings.Contains(s.err.Error(), tooLong) {
		t.Errorf("LastError after the change = %v, want the last rejection", s.err)
	}

	t.Log("A reconcile after one that succeeded sees no error.")
	patchSize(4)
	e2e.Eventually(t, 10*time.Second, func() error {
		s, ok := l.first(key, 4)
		if !ok {
			return fmt.Errorf("no reconcile at size 4 yet")
		}
		if s.err != nil {
			t.Fatalf("LastError after a successful reconcile = %v, want nil", s.err)
		}
		return nil
	})
}
