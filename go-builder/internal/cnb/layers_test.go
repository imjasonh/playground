package cnb

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestWriteLayerTOML(t *testing.T) {
	dir := t.TempDir()
	layer, err := CreateLayer(dir, "go")
	if err != nil {
		t.Fatal(err)
	}
	if err := WriteLayerTOML(layer, LayerTypes{Build: true, Cache: true}, map[string]string{
		"version": "1.25.0",
		"url":     "https://example.com/go.tgz",
	}); err != nil {
		t.Fatal(err)
	}
	b, err := os.ReadFile(layer.Toml)
	if err != nil {
		t.Fatal(err)
	}
	s := string(b)
	if !strings.Contains(s, "build = true") || !strings.Contains(s, `version = "1.25.0"`) {
		t.Fatalf("toml: %s", s)
	}
	meta, err := ReadLayerMetadata(layer.Toml)
	if err != nil {
		t.Fatal(err)
	}
	if meta["version"] != "1.25.0" {
		t.Fatalf("meta: %#v", meta)
	}
}

func TestWriteLaunchTOML(t *testing.T) {
	dir := t.TempDir()
	if err := WriteLaunchTOML(dir, []Process{{
		Type:    "web",
		Command: []string{"/layers/x/ko-app"},
		Default: true,
	}}, nil); err != nil {
		t.Fatal(err)
	}
	b, err := os.ReadFile(filepath.Join(dir, "launch.toml"))
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(b), `command = ["/layers/x/ko-app"]`) {
		t.Fatalf("launch: %s", b)
	}
}
