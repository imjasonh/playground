package publish_test

import (
	"testing"

	"github.com/imjasonh/playground/node-image/internal/publish"
)

func TestLocalRepository(t *testing.T) {
	cases := []struct {
		in   string
		want string
	}{
		{"", "node-image.local/app"},
		{"app", "node-image.local/app"},
		{"my/app", "node-image.local/my/app"},
		{"example.com/pure-js-fixture", "node-image.local/pure-js-fixture"},
		{"registry.example.com/me/myapp", "node-image.local/me/myapp"},
		{"localhost:5000/demo", "node-image.local/demo"},
	}
	for _, tc := range cases {
		got, err := publish.LocalRepoName(tc.in)
		if err != nil {
			t.Fatalf("%q: %v", tc.in, err)
		}
		if got != tc.want {
			t.Fatalf("%q: got %q want %q", tc.in, got, tc.want)
		}
	}
}
