package runner

import "testing"

func TestDefaultSkipDirs_coversEcosystemVendors(t *testing.T) {
	want := []string{
		"vendor",
		"node_modules",
		"Pods",
		"venv",
		".venv",
		"Godeps",
		"third_party",
		".git",
		".pasta",
	}
	for _, name := range want {
		if !DefaultSkipDirs[name] {
			t.Errorf("DefaultSkipDirs missing %q", name)
		}
	}
}
