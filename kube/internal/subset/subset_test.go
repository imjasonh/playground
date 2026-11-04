package subset

import (
	"testing"

	"github.com/imjasonh/playground/kube/internal/jsonnum"
)

func decode(t *testing.T, s string) any {
	t.Helper()
	var v any
	if err := jsonnum.Unmarshal([]byte(s), &v); err != nil {
		t.Fatal(err)
	}
	return v
}

func TestContains(t *testing.T) {
	observed := `{
		"metadata": {"name": "web", "labels": {"app": "web", "pod-template-hash": "abc"}, "resourceVersion": "9"},
		"spec": {"replicas": 3, "template": {"spec": {"containers": [{"name": "app", "image": "nginx:1.27", "imagePullPolicy": "IfNotPresent"}]}}},
		"status": {"readyReplicas": 3}
	}`
	for _, tc := range []struct {
		want string
		ok   bool
	}{
		{`{"metadata": {"name": "web", "labels": {"app": "web"}}}`, true},
		{`{"spec": {"replicas": 3}}`, true},
		{`{"spec": {"replicas": 3.0}}`, true},
		{`{"spec": {"replicas": 4}}`, false},
		{`{"spec": {"template": {"spec": {"containers": [{"name": "app", "image": "nginx:1.27"}]}}}}`, true},
		{`{"spec": {"template": {"spec": {"containers": [{"name": "app", "image": "nginx:1.28"}]}}}}`, false},
		{`{"spec": {"template": {"spec": {"containers": []}}}}`, false},
		{`{"spec": {"paused": true}}`, false},
		{`{"spec": {"paused": null}}`, true},
		{`{"metadata": {"labels": {"tier": "frontend"}}}`, false},
		{`{"metadata": "web"}`, false},
		{`{}`, true},
	} {
		if got := Contains(decode(t, observed), decode(t, tc.want)); got != tc.ok {
			t.Errorf("Contains(observed, %s) = %v, want %v", tc.want, got, tc.ok)
		}
	}
}
