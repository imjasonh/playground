package main

import (
	"testing"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"google.golang.org/protobuf/proto"

	"github.com/imjasonh/playground/ci-substrate/internal/digest"
)

func rootDigest(t *testing.T, inputs ...*repb.Digest) string {
	t.Helper()
	b, err := proto.MarshalOptions{Deterministic: true}.Marshal(inputRoot(inputs))
	if err != nil {
		t.Fatal(err)
	}
	return digest.Key(digest.FromBytes(b))
}

func TestInputRootIsCanonical(t *testing.T) {
	a := digest.FromBytes([]byte("a"))
	b := digest.FromBytes([]byte("b"))
	if rootDigest(t, a, b) != rootDigest(t, b, a, b) {
		t.Error("input order or duplicates changed the input root digest")
	}
	if rootDigest(t, a) == rootDigest(t, b) {
		t.Error("different inputs produced the same input root digest")
	}
}
