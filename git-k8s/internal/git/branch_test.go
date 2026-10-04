package git_test

import (
	"testing"

	"github.com/imjasonh/playground/git-k8s/internal/git"
)

func TestValidBranch(t *testing.T) {
	for name, want := range map[string]bool{
		"deps/go/example.com/greet@v1":   true,
		"deps/go/gopkg.in/yaml.v3@v3":    true,
		"deps/go/github.com/A/B_c-d~@v1": false,
		"":                               false,
		"@":                              false,
		"-x":                             false,
		"deps/":                          false,
		"deps//go":                       false,
		"deps/.go":                       false,
		"deps/go.lock":                   false,
		"deps/go.":                       false,
		"deps/go..x":                     false,
		"deps/go@{1}":                    false,
		"deps/go x":                      false,
		"deps/go:x":                      false,
		"deps/go\x7f":                    false,
	} {
		if got := git.ValidBranch(name); got != want {
			t.Errorf("ValidBranch(%q) = %v, want %v", name, got, want)
		}
	}
}
