package asset

import (
	"context"
	"testing"
	"time"

	assetpb "github.com/bazelbuild/remote-apis/build/bazel/remote/asset/v1"
	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/types/known/timestamppb"

	"github.com/imjasonh/playground/ci-substrate/internal/blob"
	"github.com/imjasonh/playground/ci-substrate/internal/digest"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
)

func incomingCtx(t *testing.T, tok string) context.Context {
	t.Helper()
	return metadata.NewIncomingContext(t.Context(), metadata.Pairs(tenant.MetadataKey, tok))
}

func TestPushFetchBlobAndIsolation(t *testing.T) {
	blobs, err := blob.NewStore(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	reg := tenant.NewRegistry()
	reg.Allow("tok-a", "tenant-a")
	reg.AllowReadOnlyAC("tok-a-ro", "tenant-a")
	reg.Allow("tok-b", "tenant-b")

	srv, err := New(t.TempDir(), blobs, reg)
	if err != nil {
		t.Fatal(err)
	}
	now := time.Date(2026, 11, 24, 12, 0, 0, 0, time.UTC)
	srv.now = func() time.Time { return now }

	data := []byte("module tarball contents")
	d := digest.FromBytes(data)
	ctxA := incomingCtx(t, "tok-a")
	ctxARO := incomingCtx(t, "tok-a-ro")
	ctxB := incomingCtx(t, "tok-b")

	// Push before blob is in CAS fails with FailedPrecondition.
	_, err = srv.PushBlob(ctxA, &assetpb.PushBlobRequest{
		InstanceName: "tenant-a",
		Uris:         []string{"https://example.com/mod.tar.gz"},
		BlobDigest:   d,
	})
	if status.Code(err) != codes.FailedPrecondition {
		t.Fatalf("PushBlob missing CAS = %v, want FailedPrecondition", err)
	}

	if err := blobs.Put(d, data); err != nil {
		t.Fatal(err)
	}

	// Read-only token cannot push assets.
	_, err = srv.PushBlob(ctxARO, &assetpb.PushBlobRequest{
		InstanceName: "tenant-a",
		Uris:         []string{"https://example.com/mod.tar.gz"},
		BlobDigest:   d,
	})
	if status.Code(err) != codes.PermissionDenied {
		t.Fatalf("read-only PushBlob = %v, want PermissionDenied", err)
	}

	// Push with two URIs and qualifiers.
	exp := now.Add(time.Hour)
	_, err = srv.PushBlob(ctxA, &assetpb.PushBlobRequest{
		InstanceName: "tenant-a",
		Uris:         []string{"https://example.com/mod.tar.gz", "https://mirror.example.com/mod.tar.gz"},
		Qualifiers: []*assetpb.Qualifier{
			{Name: "checksum.sri", Value: "sha256-abc"},
			{Name: "bazel.canonical_id", Value: "v1"},
		},
		BlobDigest: d,
		ExpireAt:   timestamppb.New(exp),
	})
	if err != nil {
		t.Fatalf("PushBlob: %v", err)
	}

	// Fetch via mirror URI with qualifiers in reverse order succeeds.
	resp, err := srv.FetchBlob(ctxARO, &assetpb.FetchBlobRequest{
		InstanceName: "tenant-a",
		Uris:         []string{"https://mirror.example.com/mod.tar.gz"},
		Qualifiers: []*assetpb.Qualifier{
			{Name: "bazel.canonical_id", Value: "v1"},
			{Name: "checksum.sri", Value: "sha256-abc"},
		},
	})
	if err != nil {
		t.Fatalf("FetchBlob: %v", err)
	}
	if resp.GetBlobDigest().GetHash() != d.GetHash() {
		t.Errorf("digest = %s, want %s", resp.GetBlobDigest().GetHash(), d.GetHash())
	}

	// Tenant B cannot see tenant A's pushed asset in tenant B's instance, nor access tenant A.
	if _, err := srv.FetchBlob(ctxB, &assetpb.FetchBlobRequest{
		InstanceName: "tenant-b",
		Uris:         []string{"https://example.com/mod.tar.gz"},
	}); status.Code(err) != codes.NotFound {
		t.Errorf("tenant B FetchBlob = %v, want NotFound", err)
	}
	if _, err := srv.FetchBlob(ctxB, &assetpb.FetchBlobRequest{
		InstanceName: "tenant-a",
		Uris:         []string{"https://example.com/mod.tar.gz"},
	}); status.Code(err) != codes.PermissionDenied {
		t.Errorf("cross-tenant FetchBlob = %v, want PermissionDenied", err)
	}

	// Expiry hides the asset.
	now = now.Add(2 * time.Hour)
	if _, err := srv.FetchBlob(ctxA, &assetpb.FetchBlobRequest{
		InstanceName: "tenant-a",
		Uris:         []string{"https://example.com/mod.tar.gz"},
		Qualifiers: []*assetpb.Qualifier{
			{Name: "checksum.sri", Value: "sha256-abc"},
			{Name: "bazel.canonical_id", Value: "v1"},
		},
	}); status.Code(err) != codes.NotFound {
		t.Errorf("expired FetchBlob = %v, want NotFound", err)
	}
}

func TestPushFetchDirectoryAndEvictedCAS(t *testing.T) {
	blobs, err := blob.NewStore(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	reg := tenant.NewRegistry()
	reg.Allow("tok-a", "tenant-a")
	srv, err := New(t.TempDir(), blobs, reg)
	if err != nil {
		t.Fatal(err)
	}
	ctxA := incomingCtx(t, "tok-a")

	dirBytes := []byte("serialized directory")
	d := digest.FromBytes(dirBytes)
	if err := blobs.Put(d, dirBytes); err != nil {
		t.Fatal(err)
	}
	if _, err := srv.PushDirectory(ctxA, &assetpb.PushDirectoryRequest{
		InstanceName:        "tenant-a",
		Uris:                []string{"git://example.com/repo"},
		RootDirectoryDigest: d,
		DigestFunction:      repb.DigestFunction_SHA256,
	}); err != nil {
		t.Fatalf("PushDirectory: %v", err)
	}

	resp, err := srv.FetchDirectory(ctxA, &assetpb.FetchDirectoryRequest{
		InstanceName: "tenant-a",
		Uris:         []string{"git://example.com/repo"},
	})
	if err != nil {
		t.Fatalf("FetchDirectory: %v", err)
	}
	if resp.GetRootDirectoryDigest().GetHash() != d.GetHash() {
		t.Errorf("RootDirectoryDigest = %s, want %s", resp.GetRootDirectoryDigest().GetHash(), d.GetHash())
	}

	// If the underlying CAS blob is evicted, FetchDirectory returns NotFound.
	if err := blobs.Delete(d); err != nil {
		t.Fatal(err)
	}
	if _, err := srv.FetchDirectory(ctxA, &assetpb.FetchDirectoryRequest{
		InstanceName: "tenant-a",
		Uris:         []string{"git://example.com/repo"},
	}); status.Code(err) != codes.NotFound {
		t.Errorf("FetchDirectory after CAS eviction = %v, want NotFound", err)
	}
}
