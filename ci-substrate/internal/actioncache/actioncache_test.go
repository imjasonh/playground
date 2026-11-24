package actioncache

import (
	"errors"
	"testing"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"

	"github.com/imjasonh/playground/ci-substrate/internal/digest"
)

func TestSurvivesReopen(t *testing.T) {
	dir := t.TempDir()
	s, err := NewStore(dir)
	if err != nil {
		t.Fatal(err)
	}
	action := digest.FromBytes([]byte("action"))
	want := &repb.ActionResult{ExitCode: 3, StdoutDigest: digest.FromBytes([]byte("out"))}
	if err := s.Put("tenant-a/sub", action, want); err != nil {
		t.Fatal(err)
	}

	reopened, err := NewStore(dir)
	if err != nil {
		t.Fatal(err)
	}
	got, err := reopened.Get("tenant-a/sub", action)
	if err != nil {
		t.Fatal(err)
	}
	if got.GetExitCode() != 3 || got.GetStdoutDigest().GetHash() != want.GetStdoutDigest().GetHash() {
		t.Fatalf("got %v, want %v", got, want)
	}
}

func TestInstancesAreSeparate(t *testing.T) {
	s, err := NewStore(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	action := digest.FromBytes([]byte("action"))
	if err := s.Put("tenant-a", action, &repb.ActionResult{ExitCode: 1}); err != nil {
		t.Fatal(err)
	}
	if _, err := s.Get("tenant-b", action); !errors.Is(err, ErrNotFound) {
		t.Fatalf("tenant-b lookup: got %v, want ErrNotFound", err)
	}
}

func TestRejectsMalformedDigest(t *testing.T) {
	s, err := NewStore(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	bad := &repb.Digest{Hash: "../../escape", SizeBytes: 1}
	if err := s.Put("tenant-a", bad, &repb.ActionResult{}); err == nil {
		t.Fatal("Put accepted a malformed digest")
	}
	if _, err := s.Get("tenant-a", bad); err == nil || errors.Is(err, ErrNotFound) {
		t.Fatalf("Get: got %v, want a validation error", err)
	}
}
