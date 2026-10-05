package kube

import (
	"strings"
	"testing"
)

func TestVolume(t *testing.T) {
	m := testManager()
	a, b := Volume("/var/lib/app"), Volume("/var/lib/other")
	m.controllers = []Controller{a, b}
	if err := a.prepare(t.Context(), m); err == nil || !strings.Contains(err.Error(), "more than one volume") {
		t.Errorf("two Volumes: err = %v", err)
	}
	m.controllers = []Controller{a}
	if err := a.prepare(t.Context(), m); err != nil {
		t.Error(err)
	}
	if d, err := a.describe(); err != nil || d.volume != "/var/lib/app" || d.reconciles || d.serves || d.webhooks || d.ti != nil {
		t.Errorf("describe = %+v, %v", d, err)
	}
	if a.reconciles() || !a.synced() || a.run(t.Context()) != nil {
		t.Error("a Volume reconciles, isn't ready, or fails to run")
	}
	for dir, want := range map[string]string{
		"":                             "isn't a clean absolute path",
		"var/lib/app":                  "isn't a clean absolute path",
		"/var/lib/app/":                "isn't a clean absolute path",
		"/var/../app":                  "isn't a clean absolute path",
		"/":                            "uses / for something else",
		"/app":                         "uses /app for something else",
		"/tmp":                         "uses /tmp for something else",
		"/var/run/secrets/tokens":      "overlaps /var/run/secrets/tokens, where the Pod's tokens are mounted",
		"/var/run/secrets/tokens/data": "overlaps /var/run/secrets/tokens,",
		"/var/run/secrets/kubernetes.io/serviceaccount":      "overlaps /var/run/secrets/kubernetes.io/serviceaccount,",
		"/var/run/secrets/kubernetes.io/serviceaccount/data": "overlaps /var/run/secrets/kubernetes.io/serviceaccount,",
		"/var/run/secrets/kubernetes.io":                     "overlaps /var/run/secrets/kubernetes.io/serviceaccount,",
		"/var/run/secrets":                                   "overlaps /var/run/secrets/kubernetes.io/serviceaccount,",
		"/var":                                               "overlaps /var/run/secrets/kubernetes.io/serviceaccount,",
		"/run/secrets/tokens":                                "overlaps /run/secrets/tokens,",
		"/run/secrets/kubernetes.io/serviceaccount/x":        "overlaps /run/secrets/kubernetes.io/serviceaccount,",
		"/run/secrets":                                       "overlaps /run/secrets/kubernetes.io/serviceaccount,",
		"/run":                                               "overlaps /run/secrets/kubernetes.io/serviceaccount,",
	} {
		v := Volume(dir)
		m.controllers = []Controller{v}
		if err := v.prepare(t.Context(), m); err == nil || !strings.Contains(err.Error(), want) {
			t.Errorf("prepare Volume(%q): err = %v, want %q", dir, err, want)
		}
		if _, err := v.describe(); err == nil || !strings.Contains(err.Error(), want) {
			t.Errorf("describe Volume(%q): err = %v, want %q", dir, err, want)
		}
	}
	for _, dir := range []string{"/var/lib/app", "/var/run/secrets/tokens-cache", "/var/run/secrets/app", "/srv/tmp", "/run/app", "/run/secrets/app"} {
		if _, err := Volume(dir).describe(); err != nil {
			t.Errorf("describe Volume(%q): %v", dir, err)
		}
	}
}
