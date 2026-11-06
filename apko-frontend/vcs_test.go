package main

import (
	"testing"
	"time"

	"chainguard.dev/apko/pkg/build/types"
)

func TestDetectVCSURL(t *testing.T) {
	for _, tc := range []struct {
		name string
		opts map[string]string
		want string
	}{
		{"https", map[string]string{"vcs:source": "https://github.com/imjasonh/playground.git", "vcs:revision": "abc123"}, "https://github.com/imjasonh/playground.git@abc123"},
		{"credentials", map[string]string{"vcs:source": "https://user:token@github.com/org/repo", "vcs:revision": "abc123"}, "https://github.com/org/repo@abc123"},
		{"scp style", map[string]string{"vcs:source": "git@github.com:org/repo.git", "vcs:revision": "abc123"}, "git+ssh://github.com/org/repo.git@abc123"},
		{"no revision", map[string]string{"vcs:source": "https://github.com/org/repo"}, "https://github.com/org/repo"},
		{"no source", map[string]string{"vcs:revision": "abc123"}, ""},
	} {
		t.Run(tc.name, func(t *testing.T) {
			if got := detectVCSURL(tc.opts); got != tc.want {
				t.Errorf("detectVCSURL(%v) = %q, want %q", tc.opts, got, tc.want)
			}
		})
	}
}

func TestImageConfigVCSAnnotations(t *testing.T) {
	ic := types.ImageConfiguration{VCSUrl: "https://github.com/org/repo@abc123"}
	img, anns, err := imageConfig(t.Context(), ic, types.ParseArchitecture("amd64"), time.Unix(0, 0), 1)
	if err != nil {
		t.Fatal(err)
	}
	for k, want := range map[string]string{
		"org.opencontainers.image.source":   "https://github.com/org/repo",
		"org.opencontainers.image.revision": "abc123",
	} {
		if anns[k] != want {
			t.Errorf("annotation %s = %q, want %q", k, anns[k], want)
		}
		if got := img.Config.Labels[k]; got != want {
			t.Errorf("label %s = %q, want %q", k, got, want)
		}
	}
}
