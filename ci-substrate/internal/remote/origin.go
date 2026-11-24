// Package remote implements the Bazel Remote Execution API surface that the
// control plane speaks: the authoritative CAS and action cache (the Origin),
// a read-only node-local cache server, and a client the runner and cache use.
package remote

import (
	"context"
	"errors"
	"io"
	"slices"
	"strconv"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"github.com/bazelbuild/remote-apis/build/bazel/semver"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/trace"
	"google.golang.org/genproto/googleapis/bytestream"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/proto"

	"github.com/imjasonh/playground/ci-substrate/internal/actioncache"
	"github.com/imjasonh/playground/ci-substrate/internal/blob"
	"github.com/imjasonh/playground/ci-substrate/internal/digest"
	"github.com/imjasonh/playground/ci-substrate/internal/invocation"
	"github.com/imjasonh/playground/ci-substrate/internal/logstream"
	"github.com/imjasonh/playground/ci-substrate/internal/telemetry"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
)

const (
	// maxInlineBytes caps how large a single stdout, stderr, or output file
	// GetActionResult will inline into an ActionResult response.
	maxInlineBytes = 1 << 20
	// defaultTreePageSize is the default Directory count per GetTree response.
	defaultTreePageSize = 1000
	// maxTreeDirectories bounds a single GetTree traversal.
	maxTreeDirectories = 100_000
)

var emptyBlobHash = digest.FromBytes(nil).GetHash()

// Origin is the authoritative CAS and action cache. Blobs are content
// addressed and shared across tenants; action results are namespaced by
// instance name and isolated by tenant authorization, which is where one
// tenant's build results stay invisible to another.
type Origin struct {
	repb.UnimplementedContentAddressableStorageServer
	repb.UnimplementedActionCacheServer
	repb.UnimplementedCapabilitiesServer
	bytestream.UnimplementedByteStreamServer

	store        *blob.Store
	actions      *actioncache.Store
	tenants      *tenant.Registry
	invocations  *invocation.Tracker
	logs         *logstream.Server
	maxBlobBytes int64
	metrics      originMetrics
}

// NewOrigin returns an Origin that keeps blobs in store and action results in
// actions, authorized by tenants, and accounts each call to its Bazel
// invocation in invocations, which may be nil.
func NewOrigin(store *blob.Store, actions *actioncache.Store, tenants *tenant.Registry, invocations *invocation.Tracker) *Origin {
	return &Origin{store: store, actions: actions, tenants: tenants, invocations: invocations, metrics: newOriginMetrics()}
}

// SetLogStream attaches a Remote Logstream server so ByteStream Read, Write,
// and QueryWriteStatus route logstream resources to it.
func (o *Origin) SetLogStream(ls *logstream.Server) {
	o.logs = ls
}

// SetMaxBlobBytes sets the maximum single blob size accepted for CAS uploads
// and advertised via CacheCapabilities.max_cas_blob_size_bytes. Zero means
// unlimited.
func (o *Origin) SetMaxBlobBytes(n int64) {
	o.maxBlobBytes = n
}

// FindMissingBlobs reports which of the requested digests the CAS lacks.
func (o *Origin) FindMissingBlobs(ctx context.Context, req *repb.FindMissingBlobsRequest) (*repb.FindMissingBlobsResponse, error) {
	if err := o.tenants.Authorize(ctx, req.GetInstanceName()); err != nil {
		return nil, err
	}
	if err := checkDigestFunction(req.GetDigestFunction()); err != nil {
		return nil, err
	}
	var missing []*repb.Digest
	for _, d := range req.GetBlobDigests() {
		if err := digest.Validate(d); err != nil {
			return nil, status.Error(codes.InvalidArgument, err.Error())
		}
		if !o.store.Has(d) {
			missing = append(missing, d)
		}
	}
	checked, nmissing := int64(len(req.GetBlobDigests())), int64(len(missing))
	instance := telemetry.AttrInstance.String(req.GetInstanceName())
	peer := telemetry.AttrPeer.String(telemetry.Peer(telemetry.RequestMetadata(ctx)))
	o.metrics.findMissing.Add(ctx, checked-nmissing, metric.WithAttributes(instance, peer, telemetry.AttrResult.String("present")))
	o.metrics.findMissing.Add(ctx, nmissing, metric.WithAttributes(instance, peer, telemetry.AttrResult.String("missing")))
	trace.SpanFromContext(ctx).SetAttributes(
		attribute.Int64("ci_substrate.digests", checked),
		attribute.Int64("ci_substrate.digests_missing", nmissing),
	)
	o.invocations.Add(ctx, req.GetInstanceName(), invocation.Counts{DigestsChecked: checked, DigestsMissing: nmissing})
	return &repb.FindMissingBlobsResponse{MissingBlobDigests: missing}, nil
}

// BatchUpdateBlobs stores many small blobs at once. Each blob is optionally
// decompressed and verified against its digest before it is stored, so the
// client cannot write bytes under a name they do not match.
func (o *Origin) BatchUpdateBlobs(ctx context.Context, req *repb.BatchUpdateBlobsRequest) (*repb.BatchUpdateBlobsResponse, error) {
	if err := o.tenants.Authorize(ctx, req.GetInstanceName()); err != nil {
		return nil, err
	}
	if err := checkDigestFunction(req.GetDigestFunction()); err != nil {
		return nil, err
	}
	var total int64
	for _, r := range req.GetRequests() {
		total += int64(len(r.GetData()))
	}
	if total > MaxBatchBytes {
		return nil, status.Errorf(codes.InvalidArgument, "batch of %d bytes exceeds %d; use ByteStream", total, MaxBatchBytes)
	}
	resp := &repb.BatchUpdateBlobsResponse{}
	var stored []int64
	defer func() { o.moved(ctx, req.GetInstanceName(), "write", "batch", stored...) }()
	for _, r := range req.GetRequests() {
		d := r.GetDigest()
		st := status.New(codes.OK, "")
		if err := digest.Validate(d); err != nil {
			st = status.New(codes.InvalidArgument, err.Error())
		} else if o.maxBlobBytes > 0 && d.GetSizeBytes() > o.maxBlobBytes {
			st = status.Newf(codes.InvalidArgument, "blob size %d exceeds max_cas_blob_size_bytes %d", d.GetSizeBytes(), o.maxBlobBytes)
		} else if data, err := decompressBytes(r.GetCompressor(), r.GetData(), d.GetSizeBytes()); err != nil {
			st = status.New(codes.InvalidArgument, err.Error())
		} else if err := o.store.Put(d, data); err != nil {
			st = status.New(codes.InvalidArgument, err.Error())
		} else {
			stored = append(stored, int64(len(data)))
		}
		resp.Responses = append(resp.Responses, &repb.BatchUpdateBlobsResponse_Response{
			Digest: d,
			Status: st.Proto(),
		})
	}
	return resp, nil
}

// BatchReadBlobs returns many small blobs at once, compressing responses when
// the client advertises acceptable compressors.
func (o *Origin) BatchReadBlobs(ctx context.Context, req *repb.BatchReadBlobsRequest) (*repb.BatchReadBlobsResponse, error) {
	if err := o.tenants.Authorize(ctx, req.GetInstanceName()); err != nil {
		return nil, err
	}
	if err := checkDigestFunction(req.GetDigestFunction()); err != nil {
		return nil, err
	}
	var total int64
	for _, d := range req.GetDigests() {
		sz := d.GetSizeBytes()
		if sz <= 0 {
			continue
		}
		if sz > MaxBatchBytes || total > MaxBatchBytes-sz {
			return nil, status.Errorf(codes.InvalidArgument, "batch exceeds %d bytes; use ByteStream", MaxBatchBytes)
		}
		total += sz
	}
	comp := selectCompressor(req.GetAcceptableCompressors())
	resp := &repb.BatchReadBlobsResponse{}
	var served []int64
	defer func() { o.moved(ctx, req.GetInstanceName(), "read", "batch", served...) }()
	for _, d := range req.GetDigests() {
		r := &repb.BatchReadBlobsResponse_Response{Digest: d}
		if err := digest.Validate(d); err != nil {
			r.Status = status.New(codes.InvalidArgument, err.Error()).Proto()
			resp.Responses = append(resp.Responses, r)
			continue
		}
		b, err := o.store.Get(d)
		switch {
		case err == blob.ErrNotFound || (err == nil && int64(len(b)) != d.GetSizeBytes()):
			r.Status = status.New(codes.NotFound, "blob not found").Proto()
		case err != nil:
			r.Status = status.New(codes.Internal, err.Error()).Proto()
		default:
			if payload, cerr := compressBytes(comp, b); cerr != nil {
				r.Status = status.New(codes.Internal, cerr.Error()).Proto()
			} else {
				r.Data = payload
				r.Compressor = comp
				r.Status = status.New(codes.OK, "").Proto()
				served = append(served, int64(len(b)))
			}
		}
		resp.Responses = append(resp.Responses, r)
	}
	return resp, nil
}

// GetTree streams the Directory protos reachable from root_digest in BFS order,
// supporting pagination via page_size and page_token.
func (o *Origin) GetTree(req *repb.GetTreeRequest, stream repb.ContentAddressableStorage_GetTreeServer) error {
	ctx := stream.Context()
	if err := o.tenants.Authorize(ctx, req.GetInstanceName()); err != nil {
		return err
	}
	if err := checkDigestFunction(req.GetDigestFunction()); err != nil {
		return err
	}
	root := req.GetRootDigest()
	if err := digest.Validate(root); err != nil {
		return status.Error(codes.InvalidArgument, err.Error())
	}
	pageSize := int(req.GetPageSize())
	if pageSize <= 0 || pageSize > defaultTreePageSize {
		pageSize = defaultTreePageSize
	}
	startIdx := 0
	if tok := req.GetPageToken(); tok != "" {
		n, err := strconv.Atoi(tok)
		if err != nil || n < 0 {
			return status.Errorf(codes.InvalidArgument, "invalid page_token %q", tok)
		}
		startIdx = n
	}

	dirs, err := o.walkTree(root)
	if err != nil {
		return err
	}
	if startIdx >= len(dirs) {
		return stream.Send(&repb.GetTreeResponse{})
	}
	for i := startIdx; i < len(dirs); i += pageSize {
		end := min(i+pageSize, len(dirs))
		nextTok := ""
		if end < len(dirs) {
			nextTok = strconv.Itoa(end)
		}
		if err := stream.Send(&repb.GetTreeResponse{
			Directories:   dirs[i:end],
			NextPageToken: nextTok,
		}); err != nil {
			return err
		}
	}
	return nil
}

func (o *Origin) walkTree(root *repb.Digest) ([]*repb.Directory, error) {
	queue := []*repb.Digest{root}
	seen := map[string]bool{digest.Key(root): true}
	var dirs []*repb.Directory
	for len(queue) > 0 {
		d := queue[0]
		queue = queue[1:]
		if len(dirs) >= maxTreeDirectories {
			return nil, status.Errorf(codes.ResourceExhausted, "tree exceeds %d directories", maxTreeDirectories)
		}
		dir := &repb.Directory{}
		if d.GetSizeBytes() == 0 && d.GetHash() == emptyBlobHash {
			dirs = append(dirs, dir)
			continue
		}
		b, err := o.store.Get(d)
		if errors.Is(err, blob.ErrNotFound) {
			if len(dirs) == 0 {
				return nil, status.Error(codes.NotFound, "root directory not found")
			}
			// Missing non-root directories are skipped per REAPI GetTree spec.
			continue
		}
		if err != nil {
			return nil, status.Error(codes.Internal, err.Error())
		}
		if err := proto.Unmarshal(b, dir); err != nil {
			return nil, status.Errorf(codes.InvalidArgument, "directory %s: %v", digest.Key(d), err)
		}
		dirs = append(dirs, dir)
		for _, sub := range dir.GetDirectories() {
			sd := sub.GetDigest()
			if err := digest.Validate(sd); err != nil {
				continue
			}
			k := digest.Key(sd)
			if !seen[k] {
				seen[k] = true
				queue = append(queue, sd)
			}
		}
	}
	return dirs, nil
}

// GetActionResult returns a cached action result for the tenant's instance if
// all blobs it references are still present in CAS, honoring inline output
// requests.
func (o *Origin) GetActionResult(ctx context.Context, req *repb.GetActionResultRequest) (*repb.ActionResult, error) {
	if err := o.tenants.Authorize(ctx, req.GetInstanceName()); err != nil {
		return nil, err
	}
	if err := checkDigestFunction(req.GetDigestFunction()); err != nil {
		return nil, err
	}
	if err := digest.Validate(req.GetActionDigest()); err != nil {
		return nil, status.Error(codes.InvalidArgument, err.Error())
	}
	ar, err := o.actions.Get(req.GetInstanceName(), req.GetActionDigest())
	if errors.Is(err, actioncache.ErrNotFound) {
		o.actionCacheLookup(ctx, req.GetInstanceName(), false)
		return nil, status.Error(codes.NotFound, "action result not found")
	}
	if err != nil {
		return nil, status.Error(codes.Internal, err.Error())
	}
	if !o.actionResultComplete(ar) {
		o.actionCacheLookup(ctx, req.GetInstanceName(), false)
		return nil, status.Error(codes.NotFound, "action result references missing CAS blobs")
	}
	ar = o.inlineOutputs(ar, req)
	o.actionCacheLookup(ctx, req.GetInstanceName(), true)
	return ar, nil
}

// actionResultComplete verifies that every blob referenced by ar is still in
// the CAS, so cache eviction never causes a stale ActionResult hit.
func (o *Origin) actionResultComplete(ar *repb.ActionResult) bool {
	has := func(d *repb.Digest) bool {
		if d == nil {
			return true
		}
		if d.GetSizeBytes() == 0 && d.GetHash() == emptyBlobHash {
			return true
		}
		return o.store.Has(d)
	}
	if !has(ar.GetStdoutDigest()) || !has(ar.GetStderrDigest()) {
		return false
	}
	for _, f := range ar.GetOutputFiles() {
		if !has(f.GetDigest()) {
			return false
		}
	}
	for _, dir := range ar.GetOutputDirectories() {
		if !has(dir.GetTreeDigest()) || !has(dir.GetRootDirectoryDigest()) {
			return false
		}
	}
	return true
}

func (o *Origin) inlineOutputs(ar *repb.ActionResult, req *repb.GetActionResultRequest) *repb.ActionResult {
	wantFiles := req.GetInlineOutputFiles()
	if !req.GetInlineStdout() && !req.GetInlineStderr() && len(wantFiles) == 0 {
		return ar
	}
	out := proto.Clone(ar).(*repb.ActionResult)
	if req.GetInlineStdout() && len(out.GetStdoutRaw()) == 0 {
		if d := out.GetStdoutDigest(); d != nil && d.GetSizeBytes() <= maxInlineBytes {
			if b, err := o.store.Get(d); err == nil {
				out.StdoutRaw = b
			}
		}
	}
	if req.GetInlineStderr() && len(out.GetStderrRaw()) == 0 {
		if d := out.GetStderrDigest(); d != nil && d.GetSizeBytes() <= maxInlineBytes {
			if b, err := o.store.Get(d); err == nil {
				out.StderrRaw = b
			}
		}
	}
	if len(wantFiles) > 0 {
		for _, f := range out.GetOutputFiles() {
			if len(f.GetContents()) > 0 || !slices.Contains(wantFiles, f.GetPath()) {
				continue
			}
			if d := f.GetDigest(); d != nil && d.GetSizeBytes() <= maxInlineBytes {
				if b, err := o.store.Get(d); err == nil {
					f.Contents = b
				}
			}
		}
	}
	return out
}

func (o *Origin) actionCacheLookup(ctx context.Context, instance string, hit bool) {
	result, c := "miss", invocation.Counts{ActionCacheMisses: 1}
	if hit {
		result, c = "hit", invocation.Counts{ActionCacheHits: 1}
	}
	trace.SpanFromContext(ctx).SetAttributes(attribute.String("ci_substrate.action_cache", result))
	o.metrics.actionCache.Add(ctx, 1, metric.WithAttributes(
		telemetry.AttrInstance.String(instance),
		telemetry.AttrPeer.String(telemetry.Peer(telemetry.RequestMetadata(ctx))),
		attribute.String("op", "get"),
		telemetry.AttrResult.String(result)))
	o.invocations.Add(ctx, instance, c)
}

// UpdateActionResult records an action result in the tenant's instance.
func (o *Origin) UpdateActionResult(ctx context.Context, req *repb.UpdateActionResultRequest) (*repb.ActionResult, error) {
	if err := o.tenants.AuthorizeActionCacheWrite(ctx, req.GetInstanceName()); err != nil {
		return nil, err
	}
	if err := checkDigestFunction(req.GetDigestFunction()); err != nil {
		return nil, err
	}
	if err := digest.Validate(req.GetActionDigest()); err != nil {
		return nil, status.Error(codes.InvalidArgument, err.Error())
	}
	if req.GetActionResult() == nil {
		return nil, status.Error(codes.InvalidArgument, "missing action result")
	}
	ar := proto.Clone(req.GetActionResult()).(*repb.ActionResult)
	if err := o.actions.Put(req.GetInstanceName(), req.GetActionDigest(), ar); err != nil {
		return nil, status.Error(codes.Internal, err.Error())
	}
	o.metrics.actionCache.Add(ctx, 1, metric.WithAttributes(
		telemetry.AttrInstance.String(req.GetInstanceName()),
		telemetry.AttrPeer.String(telemetry.Peer(telemetry.RequestMetadata(ctx))),
		attribute.String("op", "update"),
		telemetry.AttrResult.String("ok")))
	o.invocations.Add(ctx, req.GetInstanceName(), invocation.Counts{ActionCacheWrites: 1})
	return ar, nil
}

// GetCapabilities advertises SHA-256 CAS with Zstd/Deflate compression, a
// writable action cache, execution priorities, and remote execution.
func (o *Origin) GetCapabilities(ctx context.Context, req *repb.GetCapabilitiesRequest) (*repb.ServerCapabilities, error) {
	updateEnabled := true
	if o.tenants.Authorize(ctx, req.GetInstanceName()) == nil {
		updateEnabled = o.tenants.AuthorizeActionCacheWrite(ctx, req.GetInstanceName()) == nil
	}
	return &repb.ServerCapabilities{
		ExecutionCapabilities: &repb.ExecutionCapabilities{
			DigestFunction:  repb.DigestFunction_SHA256,
			DigestFunctions: []repb.DigestFunction_Value{repb.DigestFunction_SHA256},
			ExecEnabled:     true,
			ExecutionPriorityCapabilities: &repb.PriorityCapabilities{
				Priorities: []*repb.PriorityCapabilities_PriorityRange{{MinPriority: -1000, MaxPriority: 1000}},
			},
		},
		CacheCapabilities: &repb.CacheCapabilities{
			DigestFunctions:               []repb.DigestFunction_Value{repb.DigestFunction_SHA256},
			ActionCacheUpdateCapabilities: &repb.ActionCacheUpdateCapabilities{UpdateEnabled: updateEnabled},
			MaxBatchTotalSizeBytes:        MaxBatchBytes,
			MaxCasBlobSizeBytes:           o.maxBlobBytes,
			SymlinkAbsolutePathStrategy:   repb.SymlinkAbsolutePathStrategy_DISALLOWED,
			SupportedCompressors: []repb.Compressor_Value{
				repb.Compressor_ZSTD,
				repb.Compressor_DEFLATE,
			},
			SupportedBatchUpdateCompressors: []repb.Compressor_Value{
				repb.Compressor_IDENTITY,
				repb.Compressor_ZSTD,
				repb.Compressor_DEFLATE,
			},
		},
		LowApiVersion:  &semver.SemVer{Major: 2, Minor: 0},
		HighApiVersion: &semver.SemVer{Major: 2, Minor: 4},
	}, nil
}

// Read streams a blob (optionally compressed) or a logstream to the client.
func (o *Origin) Read(req *bytestream.ReadRequest, stream bytestream.ByteStream_ReadServer) error {
	if o.logs != nil && logstream.IsResource(req.GetResourceName()) {
		return o.logs.Read(req, stream)
	}
	instance, d, comp, err := ParseReadResourceCompressed(req.GetResourceName())
	if err != nil {
		return status.Error(codes.InvalidArgument, err.Error())
	}
	if err := o.tenants.Authorize(stream.Context(), instance); err != nil {
		return err
	}
	if comp != repb.Compressor_IDENTITY && req.GetReadLimit() != 0 {
		return status.Error(codes.InvalidArgument, "read_limit must be 0 for compressed-blobs reads")
	}
	f, size, err := o.store.Open(d)
	if errors.Is(err, blob.ErrNotFound) {
		return status.Error(codes.NotFound, "blob not found")
	}
	if err != nil {
		return status.Error(codes.Internal, err.Error())
	}
	defer f.Close()

	n, err := streamReader(f, size, req.GetReadOffset(), req.GetReadLimit(), comp, stream)
	if err == nil {
		o.moved(stream.Context(), instance, "read", "bytestream", n)
	}
	return err
}

// Write streams a blob (optionally compressed) to disk without buffering the
// entire payload in memory, or delegates to the LogStream server.
func (o *Origin) Write(stream bytestream.ByteStream_WriteServer) error {
	first, err := stream.Recv()
	if err == io.EOF {
		return status.Error(codes.InvalidArgument, "empty write stream")
	}
	if err != nil {
		return err
	}
	if o.logs != nil && logstream.IsResource(first.GetResourceName()) {
		return o.logs.Write(&firstReqWriteServer{ByteStream_WriteServer: stream, first: first})
	}
	instance, d, comp, err := ParseWriteResourceCompressed(first.GetResourceName())
	if err != nil {
		return status.Error(codes.InvalidArgument, err.Error())
	}
	if err := o.tenants.Authorize(stream.Context(), instance); err != nil {
		return err
	}
	if o.maxBlobBytes > 0 && d.GetSizeBytes() > o.maxBlobBytes {
		return status.Errorf(codes.InvalidArgument, "blob size %d exceeds max_cas_blob_size_bytes %d", d.GetSizeBytes(), o.maxBlobBytes)
	}
	committedSize := d.GetSizeBytes()
	if comp != repb.Compressor_IDENTITY {
		committedSize = -1
	}
	// If the blob is already stored, short-circuit per the REAPI spec.
	if o.store.Has(d) {
		return stream.SendAndClose(&bytestream.WriteResponse{CommittedSize: committedSize})
	}
	if first.GetWriteOffset() != 0 {
		return status.Errorf(codes.InvalidArgument, "write offset %d, want 0", first.GetWriteOffset())
	}

	pr, pw := io.Pipe()
	putDone := make(chan error, 1)
	go func() {
		defer pr.Close()
		var r io.Reader = pr
		if comp != repb.Compressor_IDENTITY {
			dec, derr := newDecompressReader(comp, pr)
			if derr != nil {
				putDone <- derr
				return
			}
			defer dec.Close()
			r = dec
		}
		putDone <- o.store.PutReader(d, r)
	}()

	var wireOffset int64
	finished := false
	pipeClosed := false
	req := first
	var streamErr error
	for {
		if req.GetWriteOffset() != wireOffset {
			streamErr = status.Errorf(codes.InvalidArgument, "write offset %d, want %d", req.GetWriteOffset(), wireOffset)
			break
		}
		data := req.GetData()
		if comp == repb.Compressor_IDENTITY && wireOffset+int64(len(data)) > d.GetSizeBytes() {
			streamErr = status.Errorf(codes.InvalidArgument, "write exceeds declared size %d", d.GetSizeBytes())
			break
		}
		if len(data) > 0 {
			if _, werr := pw.Write(data); werr != nil {
				// The consumer side (decompressor or PutReader) closed early;
				// wait for its concrete error below.
				pipeClosed = true
				break
			}
			wireOffset += int64(len(data))
		}
		if req.GetFinishWrite() {
			finished = true
			break
		}
		next, rerr := stream.Recv()
		if rerr == io.EOF {
			break
		}
		if rerr != nil {
			streamErr = rerr
			break
		}
		req = next
	}

	if streamErr != nil {
		pw.CloseWithError(streamErr)
		<-putDone
		return streamErr
	}
	if pipeClosed {
		pw.Close()
		if err := <-putDone; err != nil {
			return status.Error(codes.InvalidArgument, err.Error())
		}
		return status.Error(codes.InvalidArgument, "write aborted")
	}
	if !finished {
		err := status.Error(codes.InvalidArgument, "write stream closed before finish_write")
		pw.CloseWithError(err)
		<-putDone
		return err
	}
	pw.Close()
	if err := <-putDone; err != nil {
		return status.Error(codes.InvalidArgument, err.Error())
	}
	o.moved(stream.Context(), instance, "write", "bytestream", d.GetSizeBytes())
	return stream.SendAndClose(&bytestream.WriteResponse{CommittedSize: committedSize})
}

// QueryWriteStatus reports how much of a blob (or logstream) is committed.
func (o *Origin) QueryWriteStatus(ctx context.Context, req *bytestream.QueryWriteStatusRequest) (*bytestream.QueryWriteStatusResponse, error) {
	if o.logs != nil && logstream.IsResource(req.GetResourceName()) {
		return o.logs.QueryWriteStatus(ctx, req)
	}
	instance, d, comp, err := ParseWriteResourceCompressed(req.GetResourceName())
	if err != nil {
		return nil, status.Error(codes.InvalidArgument, err.Error())
	}
	if err := o.tenants.Authorize(ctx, instance); err != nil {
		return nil, err
	}
	if !o.store.Has(d) {
		return nil, status.Error(codes.NotFound, "no such upload")
	}
	committed := d.GetSizeBytes()
	if comp != repb.Compressor_IDENTITY {
		committed = -1
	}
	return &bytestream.QueryWriteStatusResponse{CommittedSize: committed, Complete: true}, nil
}

func checkDigestFunction(fn repb.DigestFunction_Value) error {
	if fn != repb.DigestFunction_UNKNOWN && fn != repb.DigestFunction_SHA256 {
		return status.Errorf(codes.Unimplemented, "digest function %v not supported", fn)
	}
	return nil
}

type firstReqWriteServer struct {
	bytestream.ByteStream_WriteServer
	first *bytestream.WriteRequest
}

func (f *firstReqWriteServer) Recv() (*bytestream.WriteRequest, error) {
	if f.first != nil {
		req := f.first
		f.first = nil
		return req, nil
	}
	return f.ByteStream_WriteServer.Recv()
}

// streamReader streams from r (with known total size) honoring uncompressed
// offset, limit, and optional compression, returning how many bytes were sent
// over the stream.
func streamReader(r io.ReadSeeker, size, offset, limit int64, comp repb.Compressor_Value, stream bytestream.ByteStream_ReadServer) (int64, error) {
	if limit < 0 {
		return 0, status.Errorf(codes.InvalidArgument, "negative read_limit %d", limit)
	}
	if offset < 0 || offset > size {
		return 0, status.Errorf(codes.OutOfRange, "offset %d out of range for %d bytes", offset, size)
	}
	if offset > 0 {
		if _, err := r.Seek(offset, io.SeekStart); err != nil {
			return 0, status.Error(codes.Internal, err.Error())
		}
	}
	var src io.Reader = r
	if comp == repb.Compressor_IDENTITY {
		if limit > 0 {
			src = io.LimitReader(r, limit)
		}
		buf := make([]byte, 1<<20)
		var sent int64
		for {
			n, err := src.Read(buf)
			if n > 0 {
				if serr := stream.Send(&bytestream.ReadResponse{Data: buf[:n]}); serr != nil {
					return sent, serr
				}
				sent += int64(n)
			}
			if err == io.EOF {
				return sent, nil
			}
			if err != nil {
				return sent, status.Error(codes.Internal, err.Error())
			}
		}
	}

	sw := &chunkStreamWriter{stream: stream}
	cw, err := newCompressWriter(comp, sw)
	if err != nil {
		return 0, status.Error(codes.InvalidArgument, err.Error())
	}
	if _, err := io.Copy(cw, src); err != nil {
		cw.Close()
		return sw.sent, err
	}
	if err := cw.Close(); err != nil {
		return sw.sent, err
	}
	if err := sw.flush(); err != nil {
		return sw.sent, err
	}
	return sw.sent, nil
}

// chunkStreamWriter buffers compressed output into 1 MiB ByteStream chunks so
// gRPC never receives tiny writes or oversized frames.
type chunkStreamWriter struct {
	stream bytestream.ByteStream_ReadServer
	buf    []byte
	sent   int64
}

func (w *chunkStreamWriter) Write(p []byte) (int, error) {
	const chunk = 1 << 20
	w.buf = append(w.buf, p...)
	for len(w.buf) >= chunk {
		if err := w.stream.Send(&bytestream.ReadResponse{Data: w.buf[:chunk]}); err != nil {
			return 0, err
		}
		w.sent += chunk
		w.buf = append(w.buf[:0], w.buf[chunk:]...)
	}
	return len(p), nil
}

func (w *chunkStreamWriter) flush() error {
	if len(w.buf) == 0 {
		return nil
	}
	if err := w.stream.Send(&bytestream.ReadResponse{Data: w.buf}); err != nil {
		return err
	}
	w.sent += int64(len(w.buf))
	w.buf = nil
	return nil
}

// streamBytes writes b to the stream honoring offset, limit, and optional
// compression, returning how many bytes were sent.
func streamBytes(b []byte, offset, limit int64, comp repb.Compressor_Value, stream bytestream.ByteStream_ReadServer) (int64, error) {
	if limit < 0 {
		return 0, status.Errorf(codes.InvalidArgument, "negative read_limit %d", limit)
	}
	if offset < 0 || offset > int64(len(b)) {
		return 0, status.Errorf(codes.OutOfRange, "offset %d out of range for %d bytes", offset, len(b))
	}
	b = b[offset:]
	if comp != repb.Compressor_IDENTITY {
		if limit != 0 {
			return 0, status.Error(codes.InvalidArgument, "read_limit must be 0 for compressed-blobs reads")
		}
		var err error
		b, err = compressBytes(comp, b)
		if err != nil {
			return 0, status.Error(codes.Internal, err.Error())
		}
	} else if limit > 0 && limit < int64(len(b)) {
		b = b[:limit]
	}
	const chunk = 1 << 20
	var sent int64
	for len(b) > 0 {
		n := min(chunk, len(b))
		if err := stream.Send(&bytestream.ReadResponse{Data: b[:n]}); err != nil {
			return sent, err
		}
		sent += int64(n)
		b = b[n:]
	}
	return sent, nil
}
