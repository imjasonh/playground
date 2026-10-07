package e2e_test

import (
	"context"
	"fmt"
	"strings"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/e2e"
	"github.com/imjasonh/playground/kube/k8s"
)

// leaker owns a ConfigMap with a label value that the API server rejects and
// quotes in its error, as it would quote a value copied from a Secret. It
// sends the first error that kube.LastError returns to lastErr.
type leaker struct{ lastErr chan error }

func (l leaker) Reconcile(ctx context.Context, w *Widget) error {
	if err := kube.LastError(ctx); err != nil {
		select {
		case l.lastErr <- err:
		default:
		}
	}
	kube.Own(ctx, &k8s.ConfigMap{Object: kube.Meta(w.Name+"-token", map[string]string{"token": "sk-live-1234!"})})
	return nil
}

func TestSyncedLeavesOutRejectedValues(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	l := leaker{lastErr: make(chan error, 1)}
	e2e.Run(t, &kube.Manager{Name: "leaker-e2e", Namespace: ns}, kube.For[Widget](l, kube.Named("leaker")))
	createWidget(t, c, ns, "w", 1)

	t.Log("Synced names the failed apply and its status code, but not the value that the API server quotes.")
	want := "applying ConfigMap.v1 " + ns + "/w-token failed (422 Invalid); see the program's log"
	e2e.Eventually(t, 30*time.Second, func() error {
		w, err := widget(t, c, ns, "w")
		if err != nil {
			return err
		}
		if s := kube.FindCondition(w.Status.Conditions, "Synced"); s == nil || s.Status != kube.False || s.Message != want {
			return fmt.Errorf("Synced = %+v, want message %q", s, want)
		}
		return nil
	})

	t.Log("kube.LastError returns the whole error to the next reconcile.")
	select {
	case err := <-l.lastErr:
		if !strings.Contains(err.Error(), `Invalid value: "sk-live-1234!"`) {
			t.Errorf("LastError = %v, want the API server's message", err)
		}
	case <-time.After(30 * time.Second):
		t.Error("no reconcile got an error from kube.LastError")
	}
}
