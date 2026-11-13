package remote_test

import (
	"bytes"
	"context"
	"net"
	"os"
	"path/filepath"
	"testing"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"google.golang.org/genproto/googleapis/bytestream"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/status"

	"github.com/imjasonh/playground/ci-substrate/internal/actioncache"
	"github.com/imjasonh/playground/ci-substrate/internal/blob"
	"github.com/imjasonh/playground/ci-substrate/internal/cache"
	"github.com/imjasonh/playground/ci-substrate/internal/digest"
	"github.com/imjasonh/playground/ci-substrate/internal/remote"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
)

// harness wires an origin and a node-local cache server over real loopback
// gRPC, the same shape the cas and cascache binaries deploy.
type harness struct {
	originAddr  string
	origin      *remote.Client
	cacheClient *remote.Client
	cache       *cache.Cache
	cacheDir    string
}

func newHarness(t *testing.T) *harness {
	t.Helper()
	tenants := tenant.NewRegistry()
	tenants.Allow("tok-a", "tenant-a", "shared")
	tenants.Allow("tok-b", "tenant-b", "shared")

	originStore, err := blob.NewStore(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	actions, err := actioncache.NewStore(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	origin := remote.NewOrigin(originStore, actions, tenants)
	originAddr := serve(t, func(s *grpc.Server) {
		repb.RegisterContentAddressableStorageServer(s, origin)
		repb.RegisterActionCacheServer(s, origin)
		repb.RegisterCapabilitiesServer(s, origin)
		bytestream.RegisterByteStreamServer(s, origin)
	})
	originClient := remote.NewClient(dial(t, originAddr))

	cacheDir := t.TempDir()
	cacheStore, err := blob.NewStore(cacheDir)
	if err != nil {
		t.Fatal(err)
	}
	rtc := cache.New(cacheStore, originClient)
	cs := remote.NewCacheServer(rtc, originClient, tenants)
	cacheAddr := serve(t, func(s *grpc.Server) {
		repb.RegisterContentAddressableStorageServer(s, cs)
		bytestream.RegisterByteStreamServer(s, cs)
	})
	cacheClient := remote.NewClient(dial(t, cacheAddr))

	return &harness{originAddr: originAddr, origin: originClient, cacheClient: cacheClient, cache: rtc, cacheDir: cacheDir}
}

func serve(t *testing.T, register func(*grpc.Server)) string {
	t.Helper()
	lis, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	s := grpc.NewServer()
	register(s)
	go s.Serve(lis)
	t.Cleanup(s.Stop)
	return lis.Addr().String()
}

func dial(t *testing.T, addr string) *grpc.ClientConn {
	t.Helper()
	conn, err := grpc.NewClient(addr, grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { conn.Close() })
	return conn
}

func ctxTok(t *testing.T, token string) context.Context {
	t.Helper()
	return tenant.Outgoing(t.Context(), token)
}

func TestCrossTenantCacheReuse(t *testing.T) {
	h := newHarness(t)
	content := []byte("shared base layer bytes")
	d, err := h.origin.Upload(ctxTok(t, "tok-a"), "shared", content)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := h.cacheClient.Fetch(ctxTok(t, "tok-a"), "shared", d); err != nil {
		t.Fatalf("tenant A cold read: %v", err)
	}
	got, err := h.cacheClient.Fetch(ctxTok(t, "tok-b"), "shared", d)
	if err != nil {
		t.Fatalf("tenant B warm read: %v", err)
	}
	if !bytes.Equal(got, content) {
		t.Errorf("tenant B read %q, want %q", got, content)
	}
	if s := h.cache.Stats(); s.OriginFetches != 1 {
		t.Errorf("origin fetches = %d, want 1 (second tenant should hit the node-local cache)", s.OriginFetches)
	}
}

func TestTenantIsolation(t *testing.T) {
	h := newHarness(t)
	content := []byte("tenant A private output")
	d, err := h.origin.Upload(ctxTok(t, "tok-a"), "tenant-a", content)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := h.cacheClient.Fetch(ctxTok(t, "tok-b"), "tenant-a", d); status.Code(err) != codes.PermissionDenied {
		t.Errorf("cache read across tenants: code %v, want PermissionDenied", status.Code(err))
	}
	if _, err := h.origin.Fetch(ctxTok(t, "tok-b"), "tenant-a", d); status.Code(err) != codes.PermissionDenied {
		t.Errorf("origin read across tenants: code %v, want PermissionDenied", status.Code(err))
	}
	if _, err := h.cacheClient.Fetch(ctxTok(t, "tok-a"), "tenant-a", d); err != nil {
		t.Errorf("tenant A reading own instance: %v", err)
	}
}

func TestPoisonedCacheFallsBack(t *testing.T) {
	h := newHarness(t)
	content := []byte("trusted toolchain blob")
	d, err := h.origin.Upload(ctxTok(t, "tok-a"), "shared", content)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := h.cacheClient.Fetch(ctxTok(t, "tok-a"), "shared", d); err != nil {
		t.Fatal(err)
	}
	poisonOneFile(t, h.cacheDir, content)

	got, err := h.cacheClient.Fetch(ctxTok(t, "tok-a"), "shared", d)
	if err != nil {
		t.Fatalf("read after poison: %v", err)
	}
	if !bytes.Equal(got, content) {
		t.Errorf("read poisoned bytes %q, want %q", got, content)
	}
	if s := h.cache.Stats(); s.PoisonRejected < 1 {
		t.Errorf("poison rejected = %d, want >= 1", s.PoisonRejected)
	}
}

// TestByteStreamLargeBlob exercises the large-blob path: upload over the batch
// limit goes through ByteStream.Write, and the read is served through the
// cache's ByteStream.Read.
func TestByteStreamLargeBlob(t *testing.T) {
	h := newHarness(t)
	big := bytes.Repeat([]byte("ci-substrate "), (remote.MaxBatchBytes/13)+1024)
	if len(big) <= remote.MaxBatchBytes {
		t.Fatalf("test blob %d not larger than batch limit", len(big))
	}
	d, err := h.origin.Upload(ctxTok(t, "tok-a"), "shared", big)
	if err != nil {
		t.Fatal(err)
	}
	if want := digest.FromBytes(big); want.GetHash() != d.GetHash() {
		t.Fatalf("upload digest mismatch")
	}
	got, err := h.cacheClient.Fetch(ctxTok(t, "tok-b"), "shared", d)
	if err != nil {
		t.Fatalf("large blob read: %v", err)
	}
	if !bytes.Equal(got, big) {
		t.Errorf("large blob round trip mismatch (%d vs %d bytes)", len(got), len(big))
	}
}

// TestActionCacheIsolation checks that action results are per tenant.
func TestActionCacheIsolation(t *testing.T) {
	h := newHarness(t)
	action := digest.FromBytes([]byte("an action"))
	ar := &repb.ActionResult{ExitCode: 0}
	if err := h.origin.UpdateActionResult(ctxTok(t, "tok-a"), "tenant-a", action, ar); err != nil {
		t.Fatal(err)
	}
	if _, _, err := h.origin.GetActionResult(ctxTok(t, "tok-b"), "tenant-a", action); status.Code(err) != codes.PermissionDenied {
		t.Errorf("tenant B reading tenant A action cache: code %v, want PermissionDenied", status.Code(err))
	}
	_, ok, err := h.origin.GetActionResult(ctxTok(t, "tok-a"), "tenant-a", action)
	if err != nil {
		t.Fatal(err)
	}
	if !ok {
		t.Error("tenant A could not read its own action result")
	}
}

// TestRejectsMalformedDigests checks that a client-supplied hash never reaches
// the file system as a path: a traversal hash is InvalidArgument at the origin
// and at the cache, not a read of some other file.
func TestRejectsMalformedDigests(t *testing.T) {
	h := newHarness(t)
	bad := &repb.Digest{Hash: "../../../../etc/passwd", SizeBytes: 10}
	if _, err := h.origin.Fetch(ctxTok(t, "tok-a"), "shared", bad); status.Code(err) != codes.InvalidArgument {
		t.Errorf("origin read of traversal hash: code %v, want InvalidArgument", status.Code(err))
	}
	if _, err := h.cacheClient.Fetch(ctxTok(t, "tok-a"), "shared", bad); status.Code(err) != codes.InvalidArgument {
		t.Errorf("cache read of traversal hash: code %v, want InvalidArgument", status.Code(err))
	}
	if _, err := h.origin.FindMissing(ctxTok(t, "tok-a"), "shared", []*repb.Digest{bad}); status.Code(err) != codes.InvalidArgument {
		t.Errorf("FindMissing of traversal hash: code %v, want InvalidArgument", status.Code(err))
	}
}

// TestBatchBoundary round-trips a blob of exactly MaxBatchBytes, the largest
// blob the client sends through the batch API, so the batch limit and gRPC's
// message limit stay consistent.
func TestBatchBoundary(t *testing.T) {
	h := newHarness(t)
	b := bytes.Repeat([]byte{'x'}, remote.MaxBatchBytes)
	d, err := h.origin.Upload(ctxTok(t, "tok-a"), "shared", b)
	if err != nil {
		t.Fatalf("upload at the batch limit: %v", err)
	}
	got, err := h.cacheClient.Fetch(ctxTok(t, "tok-b"), "shared", d)
	if err != nil {
		t.Fatalf("read at the batch limit: %v", err)
	}
	if !bytes.Equal(got, b) {
		t.Error("round trip at the batch limit returned different bytes")
	}
}

// TestByteStreamWriteBounds checks that a write cannot exceed the size its
// resource name declares, cannot skip offsets, and must finish.
func TestByteStreamWriteBounds(t *testing.T) {
	h := newHarness(t)
	conn := dial(t, h.originAddr)
	bs := bytestream.NewByteStreamClient(conn)
	content := []byte("bounded upload")
	d := digest.FromBytes(content)
	name := remote.WriteResourceName("shared", "u1", d)

	for _, tc := range []struct {
		name string
		reqs []*bytestream.WriteRequest
	}{{
		name: "oversized",
		reqs: []*bytestream.WriteRequest{{ResourceName: name, Data: append(content, 'x'), FinishWrite: true}},
	}, {
		name: "offset gap",
		reqs: []*bytestream.WriteRequest{
			{ResourceName: name, Data: content[:4]},
			{ResourceName: name, WriteOffset: 5, Data: content[5:], FinishWrite: true},
		},
	}, {
		name: "unfinished",
		reqs: []*bytestream.WriteRequest{{ResourceName: name, Data: content}},
	}} {
		t.Run(tc.name, func(t *testing.T) {
			stream, err := bs.Write(ctxTok(t, "tok-a"))
			if err != nil {
				t.Fatal(err)
			}
			for _, r := range tc.reqs {
				if err := stream.Send(r); err != nil {
					break
				}
			}
			if _, err := stream.CloseAndRecv(); status.Code(err) != codes.InvalidArgument {
				t.Errorf("code %v, want InvalidArgument", status.Code(err))
			}
		})
	}
}

// TestDigestIsReadCapability pins down the CAS sharing model: blobs are not
// private to an instance. A tenant that knows a digest can read those bytes
// through any instance it holds, which is what lets the cache serve one copy
// to every tenant. What instances keep private is the action cache, the map
// from an action to its output digests, so a tenant cannot learn the digests
// of another tenant's outputs.
func TestDigestIsReadCapability(t *testing.T) {
	h := newHarness(t)
	content := []byte("private to tenant A")
	d, err := h.origin.Upload(ctxTok(t, "tok-a"), "tenant-a", content)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := h.cacheClient.Fetch(ctxTok(t, "tok-b"), "tenant-b", d); err != nil {
		t.Fatalf("tenant B reading content it names by digest: %v", err)
	}
}

func TestBatchRoundTrip(t *testing.T) {
	h := newHarness(t)
	ctx := ctxTok(t, "tok-a")
	blobs := map[string][]byte{}
	var digests []*repb.Digest
	for _, b := range [][]byte{[]byte("one"), []byte("two"), []byte("three")} {
		d := digest.FromBytes(b)
		blobs[digest.Key(d)] = b
		digests = append(digests, d)
	}
	missing, sent, err := h.origin.PutBatch(ctx, "tenant-a", blobs)
	if err != nil {
		t.Fatal(err)
	}
	if missing != 3 || sent != int64(len("one")+len("two")+len("three")) {
		t.Fatalf("put missing=%d sent=%d", missing, sent)
	}
	missing, sent, err = h.origin.PutBatch(ctx, "tenant-a", blobs)
	if err != nil || missing != 0 || sent != 0 {
		t.Fatalf("second put missing=%d sent=%d err=%v", missing, sent, err)
	}
	for _, d := range digests {
		got, err := h.cacheClient.Fetch(ctx, "tenant-a", d)
		if err != nil || string(got) != string(blobs[digest.Key(d)]) {
			t.Fatalf("read %s = %q, %v", digest.Key(d), got, err)
		}
	}
}

func poisonOneFile(t *testing.T, root string, orig []byte) {
	t.Helper()
	poisoned := append([]byte(nil), orig...)
	poisoned[0] ^= 0xff
	var target string
	err := filepath.WalkDir(root, func(path string, de os.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if !de.IsDir() {
			target = path
		}
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
	if target == "" {
		t.Fatal("no cached file to poison")
	}
	if err := os.WriteFile(target, poisoned, 0o644); err != nil {
		t.Fatal(err)
	}
}
