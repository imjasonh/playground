package config_test

import (
	"testing"

	"github.com/imjasonh/playground/node-image/internal/config"
)

func TestApplyCommand(t *testing.T) {
	dir := t.TempDir()
	writePJ(t, dir, `{
		"name":"x","main":"build/index.js",
		"node-image":{
			"commands":{
				"api":["build/index.js"],
				"worker":["build/worker.js"]
			}
		}
	}`)
	cfg, _, err := config.Load(dir)
	if err != nil {
		t.Fatal(err)
	}
	if err := cfg.ApplyCommand("worker"); err != nil {
		t.Fatal(err)
	}
	cmd := cfg.Cmd()
	if len(cmd) != 1 || cmd[0] != "/app/build/worker.js" {
		t.Fatalf("cmd=%v", cmd)
	}
}

func TestAllowScripts(t *testing.T) {
	cfg := &config.Config{AllowScripts: []string{"sqlite3", "@scope/native@1.0.0"}}
	if !cfg.AllowsScript("sqlite3") {
		t.Fatal("sqlite3")
	}
	if !cfg.AllowsScript("@scope/native") {
		t.Fatal("@scope/native")
	}
	if cfg.AllowsScript("other") {
		t.Fatal("other")
	}
}

func TestSkipBuildFromConfig(t *testing.T) {
	dir := t.TempDir()
	writePJ(t, dir, `{"name":"x","main":"index.js","node-image":{"skipBuild":true}}`)
	cfg, _, err := config.Load(dir)
	if err != nil {
		t.Fatal(err)
	}
	if !cfg.SkipBuild {
		t.Fatal("expected skipBuild")
	}
}
