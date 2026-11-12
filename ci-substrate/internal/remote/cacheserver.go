package remote

import (
	"context"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"google.golang.org/genproto/googleapis/bytestream"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	"github.com/imjasonh/playground/ci-substrate/internal/cache"
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
	missing, err := s.origin.FindMissing(tenant.Outgoing(ctx, tenant.Token(ctx)), req.GetInstanceName(), req.GetBlobDigests())
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
	resp := &repb.BatchReadBlobsResponse{}
	for _, d := range req.GetDigests() {
		r := &repb.BatchReadBlobsResponse_Response{Digest: d}
		if b, err := s.cache.Get(s.originCtx(ctx), req.GetInstanceName(), d); err != nil {
			r.Status = status.New(status.Code(err), statusMessage(err)).Proto()
		} else {
			r.Data = b
			r.Status = status.New(codes.OK, "").Proto()
		}
		resp.Responses = append(resp.Responses, r)
	}
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
	b, err := s.cache.Get(s.originCtx(stream.Context()), instance, d)
	if err != nil {
		return err
	}
	return streamBytes(b, req.GetReadOffset(), req.GetReadLimit(), stream)
}

// originCtx forwards the caller's tenant token to origin calls the cache makes
// on a miss, so the origin applies the same authorization.
func (s *CacheServer) originCtx(ctx context.Context) context.Context {
	return tenant.Outgoing(ctx, tenant.Token(ctx))
}

func statusMessage(err error) string {
	if err == nil {
		return ""
	}
	return err.Error()
}
