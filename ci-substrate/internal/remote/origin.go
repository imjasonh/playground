// Package remote implements the Bazel Remote Execution API surface that the
// control plane speaks: the authoritative CAS and action cache (the Origin),
// a read-only node-local cache server, and a client the runner and cache use.
package remote

import (
	"context"
	"errors"
	"io"

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
	"github.com/imjasonh/playground/ci-substrate/internal/telemetry"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
)

// Origin is the authoritative CAS and action cache. Blobs are content
// addressed and shared across tenants; action results are namespaced by
// instance name and isolated by tenant authorization, which is where one
// tenant's build results stay invisible to another.
type Origin struct {
	repb.UnimplementedContentAddressableStorageServer
	repb.UnimplementedActionCacheServer
	repb.UnimplementedCapabilitiesServer
	bytestream.UnimplementedByteStreamServer

	store       *blob.Store
	actions     *actioncache.Store
	tenants     *tenant.Registry
	invocations *invocation.Tracker
	metrics     originMetrics
}

// NewOrigin returns an Origin that keeps blobs in store and action results in
// actions, authorized by tenants, and accounts each call to its Bazel
// invocation in invocations, which may be nil.
func NewOrigin(store *blob.Store, actions *actioncache.Store, tenants *tenant.Registry, invocations *invocation.Tracker) *Origin {
	return &Origin{store: store, actions: actions, tenants: tenants, invocations: invocations, metrics: newOriginMetrics()}
}

// FindMissingBlobs reports which of the requested digests the CAS lacks.
func (o *Origin) FindMissingBlobs(ctx context.Context, req *repb.FindMissingBlobsRequest) (*repb.FindMissingBlobsResponse, error) {
	if err := o.tenants.Authorize(ctx, req.GetInstanceName()); err != nil {
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

// BatchUpdateBlobs stores many small blobs at once. Each blob is verified
// against its digest before it is stored, so the client cannot write bytes
// under a name they do not match.
func (o *Origin) BatchUpdateBlobs(ctx context.Context, req *repb.BatchUpdateBlobsRequest) (*repb.BatchUpdateBlobsResponse, error) {
	if err := o.tenants.Authorize(ctx, req.GetInstanceName()); err != nil {
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
		st := status.New(codes.OK, "")
		if err := o.store.Put(r.GetDigest(), r.GetData()); err != nil {
			st = status.New(codes.InvalidArgument, err.Error())
		} else {
			stored = append(stored, int64(len(r.GetData())))
		}
		resp.Responses = append(resp.Responses, &repb.BatchUpdateBlobsResponse_Response{
			Digest: r.GetDigest(),
			Status: st.Proto(),
		})
	}
	return resp, nil
}

// BatchReadBlobs returns many small blobs at once.
func (o *Origin) BatchReadBlobs(ctx context.Context, req *repb.BatchReadBlobsRequest) (*repb.BatchReadBlobsResponse, error) {
	if err := o.tenants.Authorize(ctx, req.GetInstanceName()); err != nil {
		return nil, err
	}
	var total int64
	for _, d := range req.GetDigests() {
		total += d.GetSizeBytes()
	}
	if total > MaxBatchBytes {
		return nil, status.Errorf(codes.InvalidArgument, "batch of %d bytes exceeds %d; use ByteStream", total, MaxBatchBytes)
	}
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
		case err == blob.ErrNotFound:
			r.Status = status.New(codes.NotFound, "blob not found").Proto()
		case err != nil:
			r.Status = status.New(codes.Internal, err.Error()).Proto()
		default:
			r.Data = b
			r.Status = status.New(codes.OK, "").Proto()
			served = append(served, int64(len(b)))
		}
		resp.Responses = append(resp.Responses, r)
	}
	return resp, nil
}

// GetActionResult returns a cached action result for the tenant's instance.
func (o *Origin) GetActionResult(ctx context.Context, req *repb.GetActionResultRequest) (*repb.ActionResult, error) {
	if err := o.tenants.Authorize(ctx, req.GetInstanceName()); err != nil {
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
	o.actionCacheLookup(ctx, req.GetInstanceName(), true)
	return ar, nil
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
	if err := o.tenants.Authorize(ctx, req.GetInstanceName()); err != nil {
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

// GetCapabilities advertises SHA-256 CAS with a writable action cache and
// remote execution.
func (o *Origin) GetCapabilities(ctx context.Context, req *repb.GetCapabilitiesRequest) (*repb.ServerCapabilities, error) {
	return &repb.ServerCapabilities{
		ExecutionCapabilities: &repb.ExecutionCapabilities{
			DigestFunction:  repb.DigestFunction_SHA256,
			DigestFunctions: []repb.DigestFunction_Value{repb.DigestFunction_SHA256},
			ExecEnabled:     true,
		},
		CacheCapabilities: &repb.CacheCapabilities{
			DigestFunctions:                 []repb.DigestFunction_Value{repb.DigestFunction_SHA256},
			ActionCacheUpdateCapabilities:   &repb.ActionCacheUpdateCapabilities{UpdateEnabled: true},
			MaxBatchTotalSizeBytes:          MaxBatchBytes,
			SymlinkAbsolutePathStrategy:     repb.SymlinkAbsolutePathStrategy_DISALLOWED,
			SupportedBatchUpdateCompressors: []repb.Compressor_Value{repb.Compressor_IDENTITY},
		},
		LowApiVersion:  &semver.SemVer{Major: 2, Minor: 0},
		HighApiVersion: &semver.SemVer{Major: 2, Minor: 3},
	}, nil
}

// Read streams a blob to the client (the ByteStream download path for large
// blobs).
func (o *Origin) Read(req *bytestream.ReadRequest, stream bytestream.ByteStream_ReadServer) error {
	instance, d, err := ParseReadResource(req.GetResourceName())
	if err != nil {
		return status.Error(codes.InvalidArgument, err.Error())
	}
	if err := o.tenants.Authorize(stream.Context(), instance); err != nil {
		return err
	}
	b, err := o.store.Get(d)
	if err == blob.ErrNotFound {
		return status.Error(codes.NotFound, "blob not found")
	} else if err != nil {
		return status.Error(codes.Internal, err.Error())
	}
	n, err := streamBytes(b, req.GetReadOffset(), req.GetReadLimit(), stream)
	o.moved(stream.Context(), instance, "read", "bytestream", n)
	return err
}

// Write stores a blob the client streams in (the ByteStream upload path for
// large blobs). Chunks must arrive in order, and the stream may not carry more
// bytes than the digest in its resource name declares, so a client cannot make
// the server buffer more than it was told to expect. The assembled blob is
// verified against that digest before it is committed.
func (o *Origin) Write(stream bytestream.ByteStream_WriteServer) error {
	var (
		buf      []byte
		d        *repb.Digest
		finished bool
	)
	var instance string
	for !finished {
		req, err := stream.Recv()
		if err == io.EOF {
			break
		}
		if err != nil {
			return err
		}
		if d == nil {
			instance, d, err = ParseWriteResource(req.GetResourceName())
			if err != nil {
				return status.Error(codes.InvalidArgument, err.Error())
			}
			if err := o.tenants.Authorize(stream.Context(), instance); err != nil {
				return err
			}
			buf = make([]byte, 0, d.GetSizeBytes())
		}
		if req.GetWriteOffset() != int64(len(buf)) {
			return status.Errorf(codes.InvalidArgument, "write offset %d, want %d", req.GetWriteOffset(), len(buf))
		}
		if int64(len(buf)+len(req.GetData())) > d.GetSizeBytes() {
			return status.Errorf(codes.InvalidArgument, "write exceeds declared size %d", d.GetSizeBytes())
		}
		buf = append(buf, req.GetData()...)
		finished = req.GetFinishWrite()
	}
	if d == nil {
		return status.Error(codes.InvalidArgument, "empty write stream")
	}
	if !finished {
		return status.Error(codes.InvalidArgument, "write stream closed before finish_write")
	}
	if err := o.store.Put(d, buf); err != nil {
		return status.Error(codes.InvalidArgument, err.Error())
	}
	o.moved(stream.Context(), instance, "write", "bytestream", int64(len(buf)))
	return stream.SendAndClose(&bytestream.WriteResponse{CommittedSize: int64(len(buf))})
}

// QueryWriteStatus reports how much of a blob is committed. This store commits
// a write atomically, so a known blob is fully committed and anything else is
// not found.
func (o *Origin) QueryWriteStatus(ctx context.Context, req *bytestream.QueryWriteStatusRequest) (*bytestream.QueryWriteStatusResponse, error) {
	instance, d, err := ParseWriteResource(req.GetResourceName())
	if err != nil {
		return nil, status.Error(codes.InvalidArgument, err.Error())
	}
	if err := o.tenants.Authorize(ctx, instance); err != nil {
		return nil, err
	}
	if !o.store.Has(d) {
		return nil, status.Error(codes.NotFound, "no such upload")
	}
	return &bytestream.QueryWriteStatusResponse{CommittedSize: d.GetSizeBytes(), Complete: true}, nil
}

// streamBytes writes b to the stream honoring offset and limit, in protocol
// sized chunks, and returns how many bytes it sent.
func streamBytes(b []byte, offset, limit int64, stream bytestream.ByteStream_ReadServer) (int64, error) {
	if offset < 0 || offset > int64(len(b)) {
		return 0, status.Errorf(codes.OutOfRange, "offset %d out of range for %d bytes", offset, len(b))
	}
	b = b[offset:]
	if limit > 0 && limit < int64(len(b)) {
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
