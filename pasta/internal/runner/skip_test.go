package runner

import "testing"

func TestIsGeneratedLockfile(t *testing.T) {
	if !IsGeneratedLockfile("package-lock.json") {
		t.Fatal("expected package-lock.json to be treated as generated")
	}
	if !IsGeneratedLockfile("npm-shrinkwrap.json") {
		t.Fatal("expected npm-shrinkwrap.json to be treated as generated")
	}
	if IsGeneratedLockfile("package.json") {
		t.Fatal("package.json is hand-written; must not be skipped")
	}
	if IsGeneratedLockfile("lock.json") {
		t.Fatal("unrelated *.json must not be skipped")
	}
}

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
		".terraform",
		"testdata",
		"target",
		"DerivedData",
	}
	for _, name := range want {
		if !DefaultSkipDirs[name] {
			t.Errorf("DefaultSkipDirs missing %q", name)
		}
	}
}
