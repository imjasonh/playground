package base_test

import (
	"strings"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/base"
)

func TestDetectLibcFromRef(t *testing.T) {
	cases := map[string]string{
		"gcr.io/distroless/nodejs22-debian12": "glibc",
		"node:22-alpine":                     "musl",
		"cgr.dev/chainguard/node:latest":     "musl",
		"mirror.gcr.io/library/node:22":      "",
	}
	for ref, want := range cases {
		got := base.DetectLibc(ref, nil)
		if got != want {
			t.Fatalf("%s: got %q want %q", ref, got, want)
		}
	}
}

func TestRequireGlibcMusl(t *testing.T) {
	err := base.RequireGlibc(&base.Info{Ref: "node:22-alpine", Libc: "musl"})
	if err == nil || !strings.Contains(err.Error(), "musl") {
		t.Fatalf("got %v", err)
	}
	if err := base.RequireGlibc(&base.Info{Ref: "distroless", Libc: "glibc"}); err != nil {
		t.Fatal(err)
	}
	info := &base.Info{Ref: "mystery", Libc: ""}
	if err := base.RequireGlibc(info); err != nil {
		t.Fatal(err)
	}
	if len(info.Warnings) == 0 {
		t.Fatal("expected unknown-libc warning")
	}
}

func TestCheckEngines(t *testing.T) {
	info := &base.Info{NodeMajor: 18}
	if err := base.CheckEngines(">=20", info); err == nil {
		t.Fatal("expected engines error")
	}
	info.NodeMajor = 22
	if err := base.CheckEngines(">=20", info); err != nil {
		t.Fatal(err)
	}
}

func TestCheckMuslDeps(t *testing.T) {
	if err := base.CheckMuslDeps("glibc", []string{"foo@1.0.0"}); err == nil {
		t.Fatal("expected error")
	}
	if err := base.CheckMuslDeps("glibc", nil); err != nil {
		t.Fatal(err)
	}
}

func TestScratchInfo(t *testing.T) {
	info := base.ScratchInfo()
	if info.LayerCount != 0 || info.Libc != "glibc" {
		t.Fatalf("%+v", info)
	}
}
