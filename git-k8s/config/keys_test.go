package config

import (
	"regexp"
	"testing"

	"github.com/imjasonh/playground/kube"
)

// policy.yaml can't import kube's label key, so it repeats it. Each key in it
// that ends in /controller must be kube.ControllerLabel.
func TestPolicyCopiesKubeControllerLabel(t *testing.T) {
	re := regexp.MustCompile(`([a-z0-9]([-a-z0-9.]*[a-z0-9])?/controller)(?:[^-A-Za-z0-9_.]|$)`)
	found := re.FindAllStringSubmatch(string(Policy), -1)
	if len(found) == 0 {
		t.Fatalf("policy.yaml has no label key that ends in /controller, want %s", kube.ControllerLabel)
	}
	for _, m := range found {
		if m[1] != kube.ControllerLabel {
			t.Errorf("policy.yaml has the label key %s, want kube.ControllerLabel, %s", m[1], kube.ControllerLabel)
		}
	}
}
