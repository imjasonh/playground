package testpath

import "testing"

func TestIs(t *testing.T) {
	for _, tc := range []struct {
		path string
		want bool
	}{
		{"kube/internal/client/config_test.go", true},
		{"pasta/cmd/pasta/install_test.go", true},
		{"pkg/tests/helpers.py", true},
		{"pkg/test_util.py", true},
		{"web/src/app.spec.ts", true},
		{"web/src/__tests__/app.js", true},
		{"e2e/kind/main.go", true},
		{"apko-frontend/helper.go", false},
		{"pkg/latest.go", false},
		{"pkg/contest.py", false},
		{"src/testing.rs", false},
	} {
		if got := Is(tc.path); got != tc.want {
			t.Errorf("Is(%q) = %v, want %v", tc.path, got, tc.want)
		}
	}
}
