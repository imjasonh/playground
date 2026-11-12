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
	"google.golang.org/genproto/googleapis/bytestream"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/proto"

	"github.com/imjasonh/playground/ci-substrate/internal/actioncache"
	"github.com/imjasonh/playground/ci-substrate/internal/blob"
	"github.com/imjasonh/playground/ci-substrate/internal/digest"
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

	store   *blob.Store
	actions *actioncache.Store
	tenants *tenant.Registry
}

// NewOrigin returns an Origin that keeps blobs in store and action results in
// actions, authorized by tenants.
func NewOrigin(store *blob.Store, actions *actioncache.Store, tenants *tenant.Registry) *Origin {
	return &Origin{store: store, actions: actions, tenants: tenants}
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
	for _, r := range req.GetRequests() {
		st := status.New(codes.OK, "")
		if err := o.store.Put(r.GetDigest(), r.GetData()); err != nil {
			st = status.New(codes.InvalidArgument, err.Error())
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
		return nil, status.Error(codes.NotFound, "action result not found")
	}
	if err != nil {
		return nil, status.Error(codes.Internal, err.Error())
	}
	return ar, nil
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
	return streamBytes(b, req.GetReadOffset(), req.GetReadLimit(), stream)
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
	for !finished {
		req, err := stream.Recv()
		if err == io.EOF {
			break
		}
		if err != nil {
			return err
		}
		if d == nil {
			var instance string
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
// sized chunks.
func streamBytes(b []byte, offset, limit int64, stream bytestream.ByteStream_ReadServer) error {
	if offset < 0 || offset > int64(len(b)) {
		return status.Errorf(codes.OutOfRange, "offset %d out of range for %d bytes", offset, len(b))
	}
	b = b[offset:]
	if limit > 0 && limit < int64(len(b)) {
		b = b[:limit]
	}
	const chunk = 1 << 20
	for len(b) > 0 {
		n := min(chunk, len(b))
		if err := stream.Send(&bytestream.ReadResponse{Data: b[:n]}); err != nil {
			return err
		}
		b = b[n:]
	}
	return nil
}
