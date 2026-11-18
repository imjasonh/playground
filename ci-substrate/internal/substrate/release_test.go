package substrate_test

import (
	"os"
	"regexp"
	"strings"
	"testing"
)

// The workers must run the Substrate release this package's client is built
// against. scripts/update-deps.sh moves both together.
func TestWorkerImageMatchesModule(t *testing.T) {
	gomod, err := os.ReadFile("../../go.mod")
	if err != nil {
		t.Fatal(err)
	}
	var version string
	for _, line := range strings.Split(string(gomod), "\n") {
		f := strings.Fields(strings.TrimPrefix(strings.TrimSpace(line), "require "))
		if len(f) >= 2 && f[0] == "go.ate.dev/substrate" {
			version = f[1]
		}
	}
	if version == "" {
		t.Fatal("go.mod does not require go.ate.dev/substrate")
	}

	manifest, err := os.ReadFile("../../deploy/substrate/workerpool.yaml")
	if err != nil {
		t.Fatal(err)
	}
	images := regexp.MustCompile(`(?m)^\s*workerImage:\s*(\S+)`).FindAllStringSubmatch(string(manifest), -1)
	if len(images) == 0 {
		t.Fatal("workerpool.yaml has no workerImage")
	}
	want := "ghcr.io/agent-substrate/substrate/ateworker-gvisor:" + version
	for _, m := range images {
		if m[1] != want {
			t.Errorf("workerImage %s, want %s to match go.mod", m[1], want)
		}
	}
}
