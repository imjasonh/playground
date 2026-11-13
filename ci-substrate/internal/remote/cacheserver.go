package remote

import (
	"context"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/trace"
	"google.golang.org/genproto/googleapis/bytestream"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	"github.com/imjasonh/playground/ci-substrate/internal/cache"
	"github.com/imjasonh/playground/ci-substrate/internal/digest"
	"github.com/imjasonh/playground/ci-substrate/internal/telemetry"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
)

// CacheServer is the read-only, node-local CAS endpoint that build actors talk
// to. Reads are served from the verified local cache, falling back to the
// origin on a miss. It authorizes the tenant on every call, so a tenant cannot
// read through an instance it was not granted even though the underlying cache
// is content addressed and shared.
type CacheServer struct {
	repb.UnimplementedContentAddressableStorageServer
	bytestream.UnimplementedByteStreamServer

	cache   *cache.Cache
	origin  *Client
	tenants *tenant.Registry
}

// NewCacheServer returns a read-only cache server.
func NewCacheServer(c *cache.Cache, origin *Client, tenants *tenant.Registry) *CacheServer {
	return &CacheServer{cache: c, origin: origin, tenants: tenants}
}

// FindMissingBlobs proxies to the origin so a client can check existence
// through the node-local endpoint.
func (s *CacheServer) FindMissingBlobs(ctx context.Context, req *repb.FindMissingBlobsRequest) (*repb.FindMissingBlobsResponse, error) {
	if err := s.tenants.Authorize(ctx, req.GetInstanceName()); err != nil {
		return nil, err
	}
	missing, err := s.origin.FindMissing(s.originCtx(ctx), req.GetInstanceName(), req.GetBlobDigests())
	if err != nil {
		return nil, err
	}
	return &repb.FindMissingBlobsResponse{MissingBlobDigests: missing}, nil
}

// BatchReadBlobs serves small blobs from the verified cache.
func (s *CacheServer) BatchReadBlobs(ctx context.Context, req *repb.BatchReadBlobsRequest) (*repb.BatchReadBlobsResponse, error) {
	if err := s.tenants.Authorize(ctx, req.GetInstanceName()); err != nil {
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
	var hits, misses int
	var hitBytes, missBytes int64
	for _, d := range req.GetDigests() {
		r := &repb.BatchReadBlobsResponse_Response{Digest: d}
		if err := digest.Validate(d); err != nil {
			r.Status = status.New(codes.InvalidArgument, err.Error()).Proto()
		} else if b, local, err := s.cache.Get(s.originCtx(ctx), req.GetInstanceName(), d); err != nil {
			r.Status = status.Convert(err).Proto()
		} else {
			r.Data = b
			r.Status = status.New(codes.OK, "").Proto()
			if local {
				hits++
				hitBytes += int64(len(b))
			} else {
				misses++
				missBytes += int64(len(b))
			}
		}
		resp.Responses = append(resp.Responses, r)
	}
	trace.SpanFromContext(ctx).SetAttributes(
		attribute.Int("ci_substrate.cache.hits", hits),
		attribute.Int("ci_substrate.cache.misses", misses),
		attribute.Int64("ci_substrate.cache.hit_bytes", hitBytes),
		attribute.Int64("ci_substrate.cache.miss_bytes", missBytes),
	)
	return resp, nil
}

// Read serves a blob from the verified cache over ByteStream.
func (s *CacheServer) Read(req *bytestream.ReadRequest, stream bytestream.ByteStream_ReadServer) error {
	instance, d, err := ParseReadResource(req.GetResourceName())
	if err != nil {
		return status.Error(codes.InvalidArgument, err.Error())
	}
	if err := s.tenants.Authorize(stream.Context(), instance); err != nil {
		return err
	}
	b, local, err := s.cache.Get(s.originCtx(stream.Context()), instance, d)
	if err != nil {
		return err
	}
	trace.SpanFromContext(stream.Context()).SetAttributes(
		attribute.Bool("ci_substrate.cache.hit", local),
		attribute.Int64("ci_substrate.bytes", int64(len(b))),
	)
	_, err = streamBytes(b, req.GetReadOffset(), req.GetReadLimit(), stream)
	return err
}

// originCtx forwards the caller's tenant token to origin calls the cache makes
// on a miss, so the origin applies the same authorization, and its
// RequestMetadata, so the origin accounts the fill to the same invocation.
func (s *CacheServer) originCtx(ctx context.Context) context.Context {
	return telemetry.Outgoing(tenant.Outgoing(ctx, tenant.Token(ctx)), telemetry.ToolCascache)
}
