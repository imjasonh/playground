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
	}
}
