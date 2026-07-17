package main

import "testing"

func TestVFSTagRequired(t *testing.T) {
	// Real benches live in files with //go:build vfs. CI invokes
	// `go test -tags vfs` for this module; this stub keeps an untagged
	// `go test ./...` green when the vfs tag is omitted.
	t.Log("ok — run with -tags vfs for Litestream benches")
}
