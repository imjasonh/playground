package images

import (
	"regexp"
	"testing"
)

func TestDefaultsArePinned(t *testing.T) {
	pinned := regexp.MustCompile(`^cgr\.dev/chainguard/[a-z]+@sha256:[0-9a-f]{64}$`)
	for _, image := range []string{Git, Go} {
		if !pinned.MatchString(image) {
			t.Errorf("default image %s isn't one of Chainguard's images named by digest", image)
		}
		if got := PullPolicy(image); got != "IfNotPresent" {
			t.Errorf("PullPolicy(%s) = %s, want IfNotPresent", image, got)
		}
	}
}

func TestPullPolicy(t *testing.T) {
	digest := "@sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
	for image, want := range map[string]string{
		"cgr.dev/chainguard/git" + digest:             "IfNotPresent",
		"registry.example.com/git:2.47" + digest:      "IfNotPresent",
		"localhost:5000/git" + digest:                 "IfNotPresent",
		"cgr.dev/chainguard/git:latest":               "Always",
		"cgr.dev/chainguard/git":                      "Always",
		"registry.example.com/git:2.47":               "Always",
		"localhost:5000/chainguard/git:latest":        "Always",
		"localhost:5000/chainguard/git":               "Always",
		"registry.example.com/agent-runner:sha256abc": "Always",
	} {
		if got := PullPolicy(image); got != want {
			t.Errorf("PullPolicy(%s) = %s, want %s", image, got, want)
		}
	}
}
