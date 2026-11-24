package remote_test

import (
	"bytes"
	"compress/flate"
	"io"
	"testing"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	logstreampb "github.com/bazelbuild/remote-apis/build/bazel/remote/logstream/v1"
	"github.com/klauspost/compress/zstd"
	"google.golang.org/genproto/googleapis/bytestream"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/proto"

	"github.com/imjasonh/playground/ci-substrate/internal/actioncache"
	"github.com/imjasonh/playground/ci-substrate/internal/blob"
	"github.com/imjasonh/playground/ci-substrate/internal/digest"
	"github.com/imjasonh/playground/ci-substrate/internal/logstream"
	"github.com/imjasonh/playground/ci-substrate/internal/remote"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
)

func zstdCompress(t *testing.T, data []byte) []byte {
	t.Helper()
	var buf bytes.Buffer
	w, err := zstd.NewWriter(&buf)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := w.Write(data); err != nil {
		t.Fatal(err)
	}
	if err := w.Close(); err != nil {
		t.Fatal(err)
	}
	return buf.Bytes()
}

func zstdDecompress(t *testing.T, data []byte) []byte {
	t.Helper()
	r, err := zstd.NewReader(bytes.NewReader(data))
	if err != nil {
		t.Fatal(err)
	}
	defer r.Close()
	out, err := io.ReadAll(r)
	if err != nil {
		t.Fatal(err)
	}
	return out
}

func deflateCompress(t *testing.T, data []byte) []byte {
	t.Helper()
	var buf bytes.Buffer
	w, err := flate.NewWriter(&buf, flate.DefaultCompression)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := w.Write(data); err != nil {
		t.Fatal(err)
	}
	if err := w.Close(); err != nil {
		t.Fatal(err)
	}
	return buf.Bytes()
}

func deflateDecompress(t *testing.T, data []byte) []byte {
	t.Helper()
	r := flate.NewReader(bytes.NewReader(data))
	defer r.Close()
	out, err := io.ReadAll(r)
	if err != nil {
		t.Fatal(err)
	}
	return out
}

func TestByteStreamAndBatchCompression(t *testing.T) {
	h := newHarness(t)
	conn := dial(t, h.originAddr)
	bs := bytestream.NewByteStreamClient(conn)
	cas := repb.NewContentAddressableStorageClient(conn)
	caps := repb.NewCapabilitiesClient(conn)
	ctx := ctxTok(t, "tok-a")

	capResp, err := caps.GetCapabilities(ctx, &repb.GetCapabilitiesRequest{InstanceName: "tenant-a"})
	if err != nil {
		t.Fatal(err)
	}
	if len(capResp.GetCacheCapabilities().GetSupportedCompressors()) < 2 {
		t.Errorf("SupportedCompressors = %v, want zstd and deflate", capResp.GetCacheCapabilities().GetSupportedCompressors())
	}

	// Upload a blob compressed with zstd over ByteStream, read it back compressed
	// with deflate (and with an uncompressed read_offset).
	plain := bytes.Repeat([]byte("compressible build output line\n"), 2000)
	d := digest.FromBytes(plain)
	compressed := zstdCompress(t, plain)
	wname := remote.CompressedWriteResourceName("tenant-a", "u-zstd", repb.Compressor_ZSTD, d)

	ws, err := bs.Write(ctx)
	if err != nil {
		t.Fatal(err)
	}
	mid := len(compressed) / 2
	if err := ws.Send(&bytestream.WriteRequest{ResourceName: wname, WriteOffset: 0, Data: compressed[:mid]}); err != nil {
		t.Fatal(err)
	}
	if err := ws.Send(&bytestream.WriteRequest{ResourceName: wname, WriteOffset: int64(mid), Data: compressed[mid:], FinishWrite: true}); err != nil {
		t.Fatal(err)
	}
	wresp, err := ws.CloseAndRecv()
	if err != nil {
		t.Fatalf("compressed Write: %v", err)
	}
	if wresp.GetCommittedSize() != -1 {
		t.Errorf("compressed CommittedSize = %d, want -1", wresp.GetCommittedSize())
	}

	// Read back as deflate with uncompressed offset 100.
	rname := remote.CompressedReadResourceName("tenant-a", repb.Compressor_DEFLATE, d)
	rs, err := bs.Read(ctx, &bytestream.ReadRequest{ResourceName: rname, ReadOffset: 100})
	if err != nil {
		t.Fatal(err)
	}
	var gotComp []byte
	for {
		resp, err := rs.Recv()
		if err == io.EOF {
			break
		}
		if err != nil {
			t.Fatalf("compressed Read: %v", err)
		}
		gotComp = append(gotComp, resp.GetData()...)
	}
	gotPlain := deflateDecompress(t, gotComp)
	if !bytes.Equal(gotPlain, plain[100:]) {
		t.Errorf("deflate Read mismatch: got %d bytes, want %d", len(gotPlain), len(plain[100:]))
	}

	// Compressed Read with non-zero read_limit must fail with InvalidArgument.
	badRS, err := bs.Read(ctx, &bytestream.ReadRequest{ResourceName: rname, ReadLimit: 10})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := badRS.Recv(); status.Code(err) != codes.InvalidArgument {
		t.Errorf("compressed Read with read_limit = %v, want InvalidArgument", err)
	}

	// BatchUpdateBlobs with deflate + BatchReadBlobs with zstd.
	small := bytes.Repeat([]byte("batch compressed payload "), 40)
	sd := digest.FromBytes(small)
	upResp, err := cas.BatchUpdateBlobs(ctx, &repb.BatchUpdateBlobsRequest{
		InstanceName: "tenant-a",
		Requests: []*repb.BatchUpdateBlobsRequest_Request{{
			Digest:     sd,
			Data:       deflateCompress(t, small),
			Compressor: repb.Compressor_DEFLATE,
		}},
	})
	if err != nil {
		t.Fatalf("BatchUpdateBlobs compressed: %v", err)
	}
	if upResp.GetResponses()[0].GetStatus().GetCode() != 0 {
		t.Fatalf("BatchUpdateBlobs status: %v", upResp.GetResponses()[0].GetStatus())
	}
	rdResp, err := cas.BatchReadBlobs(ctx, &repb.BatchReadBlobsRequest{
		InstanceName:          "tenant-a",
		Digests:               []*repb.Digest{sd},
		AcceptableCompressors: []repb.Compressor_Value{repb.Compressor_ZSTD},
	})
	if err != nil {
		t.Fatalf("BatchReadBlobs compressed: %v", err)
	}
	r0 := rdResp.GetResponses()[0]
	if r0.GetCompressor() != repb.Compressor_ZSTD {
		t.Errorf("BatchReadBlobs compressor = %v, want ZSTD", r0.GetCompressor())
	}
	if !bytes.Equal(zstdDecompress(t, r0.GetData()), small) {
		t.Errorf("BatchReadBlobs decompressed mismatch")
	}
}

func TestGetTreePagination(t *testing.T) {
	h := newHarness(t)
	conn := dial(t, h.originAddr)
	cas := repb.NewContentAddressableStorageClient(conn)
	ctx := ctxTok(t, "tok-a")

	leaf := &repb.Directory{Files: []*repb.FileNode{{Name: "a.txt", Digest: digest.FromBytes([]byte("a"))}}}
	leafBytes, _ := proto.Marshal(leaf)
	leafDigest, err := h.origin.Upload(ctx, "tenant-a", leafBytes)
	if err != nil {
		t.Fatal(err)
	}
	sub := &repb.Directory{Directories: []*repb.DirectoryNode{{Name: "leaf", Digest: leafDigest}}}
	subBytes, _ := proto.Marshal(sub)
	subDigest, err := h.origin.Upload(ctx, "tenant-a", subBytes)
	if err != nil {
		t.Fatal(err)
	}
	root := &repb.Directory{Directories: []*repb.DirectoryNode{{Name: "sub", Digest: subDigest}}}
	rootBytes, _ := proto.Marshal(root)
	rootDigest, err := h.origin.Upload(ctx, "tenant-a", rootBytes)
	if err != nil {
		t.Fatal(err)
	}

	stream, err := cas.GetTree(ctx, &repb.GetTreeRequest{
		InstanceName: "tenant-a",
		RootDigest:   rootDigest,
		PageSize:     2,
	})
	if err != nil {
		t.Fatal(err)
	}
	var all []*repb.Directory
	var pages int
	for {
		resp, err := stream.Recv()
		if err == io.EOF {
			break
		}
		if err != nil {
			t.Fatalf("GetTree Recv: %v", err)
		}
		pages++
		all = append(all, resp.GetDirectories()...)
	}
	if pages != 2 || len(all) != 3 {
		t.Errorf("GetTree got %d pages and %d dirs, want 2 pages and 3 dirs", pages, len(all))
	}
}

func TestActionCacheCompletenessInliningReadOnlyAndLogStream(t *testing.T) {
	tenants := tenant.NewRegistry()
	tenants.Allow("tok-ci", "tenant-a")
	tenants.AllowReadOnlyAC("tok-dev", "tenant-a")

	store, err := blob.NewStore(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	actions, err := actioncache.NewStore(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	ls := logstream.New(tenants)
	origin := remote.NewOrigin(store, actions, tenants, nil)
	origin.SetLogStream(ls)
	origin.SetMaxBlobBytes(1024)

	addr := serve(t, func(s *grpc.Server) {
		repb.RegisterContentAddressableStorageServer(s, origin)
		repb.RegisterActionCacheServer(s, origin)
		repb.RegisterCapabilitiesServer(s, origin)
		bytestream.RegisterByteStreamServer(s, origin)
		logstreampb.RegisterLogStreamServiceServer(s, ls)
	})
	conn := dial(t, addr)
	ac := repb.NewActionCacheClient(conn)
	bs := bytestream.NewByteStreamClient(conn)
	lsc := logstreampb.NewLogStreamServiceClient(conn)
	client := remote.NewClient(conn)

	ciCtx := ctxTok(t, "tok-ci")
	devCtx := ctxTok(t, "tok-dev")

	// Upload blobs referenced by ActionResult.
	stdoutD, err := client.Upload(ciCtx, "tenant-a", []byte("hello stdout"))
	if err != nil {
		t.Fatal(err)
	}
	outD, err := client.Upload(ciCtx, "tenant-a", []byte("artifact bytes"))
	if err != nil {
		t.Fatal(err)
	}
	actionD := digest.FromBytes([]byte("action-1"))
	ar := &repb.ActionResult{
		StdoutDigest: stdoutD,
		OutputFiles:  []*repb.OutputFile{{Path: "out.txt", Digest: outD}},
	}

	// Read-only dev token cannot update AC.
	if _, err := ac.UpdateActionResult(devCtx, &repb.UpdateActionResultRequest{
		InstanceName: "tenant-a",
		ActionDigest: actionD,
		ActionResult: ar,
	}); status.Code(err) != codes.PermissionDenied {
		t.Fatalf("read-only UpdateActionResult = %v, want PermissionDenied", err)
	}

	// CI token writes AC; dev token reads with inlining.
	if _, err := ac.UpdateActionResult(ciCtx, &repb.UpdateActionResultRequest{
		InstanceName: "tenant-a",
		ActionDigest: actionD,
		ActionResult: ar,
	}); err != nil {
		t.Fatal(err)
	}
	got, err := ac.GetActionResult(devCtx, &repb.GetActionResultRequest{
		InstanceName:      "tenant-a",
		ActionDigest:      actionD,
		InlineStdout:      true,
		InlineOutputFiles: []string{"out.txt"},
	})
	if err != nil {
		t.Fatalf("GetActionResult: %v", err)
	}
	if string(got.GetStdoutRaw()) != "hello stdout" {
		t.Errorf("StdoutRaw = %q, want %q", got.GetStdoutRaw(), "hello stdout")
	}
	if string(got.GetOutputFiles()[0].GetContents()) != "artifact bytes" {
		t.Errorf("OutputFile.Contents = %q, want %q", got.GetOutputFiles()[0].GetContents(), "artifact bytes")
	}

	// Deleting the output blob from CAS turns GetActionResult into a miss.
	if err := store.Delete(outD); err != nil {
		t.Fatal(err)
	}
	if _, err := ac.GetActionResult(devCtx, &repb.GetActionResultRequest{
		InstanceName: "tenant-a",
		ActionDigest: actionD,
	}); status.Code(err) != codes.NotFound {
		t.Errorf("GetActionResult with missing CAS blob = %v, want NotFound", err)
	}

	// Uploading a blob larger than MaxBlobBytes (1024) fails with InvalidArgument.
	tooBig := bytes.Repeat([]byte("x"), 2048)
	if _, err := client.Upload(ciCtx, "tenant-a", tooBig); status.Code(err) != codes.InvalidArgument {
		t.Errorf("oversized Upload = %v, want InvalidArgument", err)
	}

	// LogStream routed through Origin's ByteStream server works end-to-end.
	lsInfo, err := lsc.CreateLogStream(ciCtx, &logstreampb.CreateLogStreamRequest{Parent: "tenant-a"})
	if err != nil {
		t.Fatal(err)
	}
	ws, err := bs.Write(ciCtx)
	if err != nil {
		t.Fatal(err)
	}
	if err := ws.Send(&bytestream.WriteRequest{
		ResourceName: lsInfo.GetWriteResourceName(),
		Data:         []byte("live log"),
		FinishWrite:  true,
	}); err != nil {
		t.Fatal(err)
	}
	if _, err := ws.CloseAndRecv(); err != nil {
		t.Fatal(err)
	}
	rs, err := bs.Read(devCtx, &bytestream.ReadRequest{ResourceName: lsInfo.GetName()})
	if err != nil {
		t.Fatal(err)
	}
	resp, err := rs.Recv()
	if err != nil {
		t.Fatal(err)
	}
	if string(resp.GetData()) != "live log" {
		t.Errorf("LogStream Read = %q, want %q", resp.GetData(), "live log")
	}

	// GetCapabilities reflects read-only AC for devCtx vs writable for ciCtx.
	caps := repb.NewCapabilitiesClient(conn)
	devCaps, err := caps.GetCapabilities(devCtx, &repb.GetCapabilitiesRequest{InstanceName: "tenant-a"})
	if err != nil {
		t.Fatal(err)
	}
	if devCaps.GetCacheCapabilities().GetActionCacheUpdateCapabilities().GetUpdateEnabled() {
		t.Error("GetCapabilities reported UpdateEnabled=true for read-only AC token")
	}
	ciCaps, err := caps.GetCapabilities(ciCtx, &repb.GetCapabilitiesRequest{InstanceName: "tenant-a"})
	if err != nil {
		t.Fatal(err)
	}
	if !ciCaps.GetCacheCapabilities().GetActionCacheUpdateCapabilities().GetUpdateEnabled() {
		t.Error("GetCapabilities reported UpdateEnabled=false for writable AC token")
	}

	// ByteStream.Read with negative read_limit returns InvalidArgument, and
	// requesting a stored hash with the wrong declared size returns NotFound.
	negStream, err := bs.Read(devCtx, &bytestream.ReadRequest{
		ResourceName: remote.ReadResourceName("tenant-a", stdoutD),
		ReadLimit:    -1,
	})
	if err == nil {
		_, err = negStream.Recv()
	}
	if status.Code(err) != codes.InvalidArgument {
		t.Errorf("negative read_limit code = %v, want InvalidArgument", status.Code(err))
	}
	wrongSizeD := &repb.Digest{Hash: stdoutD.GetHash(), SizeBytes: stdoutD.GetSizeBytes() + 99}
	wrongStream, err := bs.Read(devCtx, &bytestream.ReadRequest{
		ResourceName: remote.ReadResourceName("tenant-a", wrongSizeD),
	})
	if err == nil {
		_, err = wrongStream.Recv()
	}
	if status.Code(err) != codes.NotFound {
		t.Errorf("wrong declared size Read code = %v, want NotFound", status.Code(err))
	}
}
