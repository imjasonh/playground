// Package asset implements the Bazel Remote Asset API
// (build.bazel.remote.asset.v1) Fetch and Push services. Assets are mapped from
// (instance, kind, uri, qualifiers) to CAS digests and stored on disk alongside
// the action cache, so Bazel's --experimental_remote_downloader can cache
// external downloads per tenant while sharing the underlying CAS blobs.
package asset

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"io/fs"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"time"

	assetpb "github.com/bazelbuild/remote-apis/build/bazel/remote/asset/v1"
	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/types/known/timestamppb"

	"github.com/imjasonh/playground/ci-substrate/internal/blob"
	"github.com/imjasonh/playground/ci-substrate/internal/digest"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
)

type record struct {
	URI        string      `json:"uri"`
	Qualifiers []qualifier `json:"qualifiers,omitempty"`
	Hash       string      `json:"hash"`
	SizeBytes  int64       `json:"size_bytes"`
	PushedAt   time.Time   `json:"pushed_at"`
	ExpireAt   *time.Time  `json:"expire_at,omitempty"`
}

type qualifier struct {
	Name  string `json:"name"`
	Value string `json:"value"`
}

// Server implements Remote Asset Fetch and Push backed by a local metadata
// directory and the CAS blob store.
type Server struct {
	assetpb.UnimplementedFetchServer
	assetpb.UnimplementedPushServer

	root    string
	blobs   *blob.Store
	tenants *tenant.Registry
	now     func() time.Time
}

// New creates the asset metadata root directory and returns a Remote Asset
// server backed by blobs and authorized by tenants.
func New(root string, blobs *blob.Store, tenants *tenant.Registry) (*Server, error) {
	if err := os.MkdirAll(root, 0o755); err != nil {
		return nil, err
	}
	return &Server{
		root:    root,
		blobs:   blobs,
		tenants: tenants,
		now:     time.Now,
	}, nil
}

// PushBlob associates one or more URIs and qualifiers with a blob already in
// CAS for the caller's instance.
func (s *Server) PushBlob(ctx context.Context, req *assetpb.PushBlobRequest) (*assetpb.PushBlobResponse, error) {
	if err := s.push(ctx, "blob", req.GetInstanceName(), req.GetUris(), req.GetQualifiers(), req.GetBlobDigest(), req.GetExpireAt(), req.GetDigestFunction()); err != nil {
		return nil, err
	}
	return &assetpb.PushBlobResponse{}, nil
}

// PushDirectory associates one or more URIs and qualifiers with a root
// Directory already in CAS for the caller's instance.
func (s *Server) PushDirectory(ctx context.Context, req *assetpb.PushDirectoryRequest) (*assetpb.PushDirectoryResponse, error) {
	if err := s.push(ctx, "dir", req.GetInstanceName(), req.GetUris(), req.GetQualifiers(), req.GetRootDirectoryDigest(), req.GetExpireAt(), req.GetDigestFunction()); err != nil {
		return nil, err
	}
	return &assetpb.PushDirectoryResponse{}, nil
}

// FetchBlob looks up a previously pushed blob asset for any of the requested
// URIs in the caller's instance.
func (s *Server) FetchBlob(ctx context.Context, req *assetpb.FetchBlobRequest) (*assetpb.FetchBlobResponse, error) {
	rec, err := s.fetch(ctx, "blob", req.GetInstanceName(), req.GetUris(), req.GetQualifiers(), req.GetOldestContentAccepted(), req.GetDigestFunction())
	if err != nil {
		return nil, err
	}
	resp := &assetpb.FetchBlobResponse{
		Status:         status.New(codes.OK, "").Proto(),
		Uri:            rec.URI,
		Qualifiers:     toProtoQualifiers(rec.Qualifiers),
		BlobDigest:     &repb.Digest{Hash: rec.Hash, SizeBytes: rec.SizeBytes},
		DigestFunction: repb.DigestFunction_SHA256,
	}
	if rec.ExpireAt != nil {
		resp.ExpiresAt = timestamppb.New(*rec.ExpireAt)
	}
	return resp, nil
}

// FetchDirectory looks up a previously pushed directory asset for any of the
// requested URIs in the caller's instance.
func (s *Server) FetchDirectory(ctx context.Context, req *assetpb.FetchDirectoryRequest) (*assetpb.FetchDirectoryResponse, error) {
	rec, err := s.fetch(ctx, "dir", req.GetInstanceName(), req.GetUris(), req.GetQualifiers(), req.GetOldestContentAccepted(), req.GetDigestFunction())
	if err != nil {
		return nil, err
	}
	resp := &assetpb.FetchDirectoryResponse{
		Status:              status.New(codes.OK, "").Proto(),
		Uri:                 rec.URI,
		Qualifiers:          toProtoQualifiers(rec.Qualifiers),
		RootDirectoryDigest: &repb.Digest{Hash: rec.Hash, SizeBytes: rec.SizeBytes},
		DigestFunction:      repb.DigestFunction_SHA256,
	}
	if rec.ExpireAt != nil {
		resp.ExpiresAt = timestamppb.New(*rec.ExpireAt)
	}
	return resp, nil
}

func (s *Server) push(ctx context.Context, kind, instance string, uris []string, qs []*assetpb.Qualifier, d *repb.Digest, expireAt *timestamppb.Timestamp, fn repb.DigestFunction_Value) error {
	if err := s.tenants.AuthorizeActionCacheWrite(ctx, instance); err != nil {
		return err
	}
	if err := checkDigestFunction(fn); err != nil {
		return err
	}
	if len(uris) == 0 {
		return status.Error(codes.InvalidArgument, "at least one URI is required")
	}
	if err := digest.Validate(d); err != nil {
		return status.Error(codes.InvalidArgument, err.Error())
	}
	sorted, err := normalizeQualifiers(qs)
	if err != nil {
		return status.Error(codes.InvalidArgument, err.Error())
	}
	for _, uri := range uris {
		if uri == "" {
			return status.Error(codes.InvalidArgument, "empty URI")
		}
	}
	if !s.blobs.Has(d) {
		return status.Errorf(codes.FailedPrecondition, "digest %s not in CAS", digest.Key(d))
	}
	now := s.now()
	var exp *time.Time
	if expireAt != nil {
		t := expireAt.AsTime()
		exp = &t
	}
	for _, uri := range uris {
		rec := record{
			URI:        uri,
			Qualifiers: sorted,
			Hash:       d.GetHash(),
			SizeBytes:  d.GetSizeBytes(),
			PushedAt:   now,
			ExpireAt:   exp,
		}
		if err := s.writeRecord(instance, kind, uri, sorted, rec); err != nil {
			return status.Error(codes.Internal, err.Error())
		}
	}
	return nil
}

func (s *Server) fetch(ctx context.Context, kind, instance string, uris []string, qs []*assetpb.Qualifier, oldest *timestamppb.Timestamp, fn repb.DigestFunction_Value) (*record, error) {
	if err := s.tenants.Authorize(ctx, instance); err != nil {
		return nil, err
	}
	if err := checkDigestFunction(fn); err != nil {
		return nil, err
	}
	if len(uris) == 0 {
		return nil, status.Error(codes.InvalidArgument, "at least one URI is required")
	}
	sorted, err := normalizeQualifiers(qs)
	if err != nil {
		return nil, status.Error(codes.InvalidArgument, err.Error())
	}
	for _, uri := range uris {
		if uri == "" {
			return nil, status.Error(codes.InvalidArgument, "empty URI")
		}
	}
	now := s.now()
	for _, uri := range uris {
		rec, err := s.readRecord(instance, kind, uri, sorted)
		if errors.Is(err, fs.ErrNotExist) {
			continue
		}
		if err != nil {
			return nil, status.Error(codes.Internal, err.Error())
		}
		if rec.ExpireAt != nil && !now.Before(*rec.ExpireAt) {
			continue
		}
		if oldest != nil && rec.PushedAt.Before(oldest.AsTime()) {
			continue
		}
		d := &repb.Digest{Hash: rec.Hash, SizeBytes: rec.SizeBytes}
		if !s.blobs.Has(d) {
			continue
		}
		return rec, nil
	}
	return nil, status.Error(codes.NotFound, "asset not found")
}

func checkDigestFunction(fn repb.DigestFunction_Value) error {
	if fn != repb.DigestFunction_UNKNOWN && fn != repb.DigestFunction_SHA256 {
		return status.Errorf(codes.Unimplemented, "digest function %v not supported", fn)
	}
	return nil
}

func normalizeQualifiers(qs []*assetpb.Qualifier) ([]qualifier, error) {
	if len(qs) == 0 {
		return nil, nil
	}
	out := make([]qualifier, len(qs))
	for i, q := range qs {
		out[i] = qualifier{Name: q.GetName(), Value: q.GetValue()}
	}
	slices.SortFunc(out, func(a, b qualifier) int {
		if c := strings.Compare(a.Name, b.Name); c != 0 {
			return c
		}
		return strings.Compare(a.Value, b.Value)
	})
	for i := 1; i < len(out); i++ {
		if out[i].Name == out[i-1].Name {
			return nil, errors.New("duplicate qualifier name")
		}
	}
	return out, nil
}

func toProtoQualifiers(qs []qualifier) []*assetpb.Qualifier {
	if len(qs) == 0 {
		return nil
	}
	out := make([]*assetpb.Qualifier, len(qs))
	for i, q := range qs {
		out[i] = &assetpb.Qualifier{Name: q.Name, Value: q.Value}
	}
	return out
}

func (s *Server) recordPath(instance, kind, uri string, qs []qualifier) string {
	h := sha256.New()
	h.Write([]byte(kind))
	h.Write([]byte{0})
	h.Write([]byte(uri))
	for _, q := range qs {
		h.Write([]byte{0})
		h.Write([]byte(q.Name))
		h.Write([]byte{'='})
		h.Write([]byte(q.Value))
	}
	key := hex.EncodeToString(h.Sum(nil))
	return filepath.Join(s.root, hex.EncodeToString([]byte(instance)), key[:2], key+".json")
}

func (s *Server) writeRecord(instance, kind, uri string, qs []qualifier, rec record) error {
	p := s.recordPath(instance, kind, uri, qs)
	b, err := json.Marshal(rec)
	if err != nil {
		return err
	}
	if err := os.MkdirAll(filepath.Dir(p), 0o755); err != nil {
		return err
	}
	tmp, err := os.CreateTemp(filepath.Dir(p), ".tmp-*")
	if err != nil {
		return err
	}
	tmpName := tmp.Name()
	defer os.Remove(tmpName)
	if _, err := tmp.Write(b); err != nil {
		tmp.Close()
		return err
	}
	if err := tmp.Close(); err != nil {
		return err
	}
	return os.Rename(tmpName, p)
}

func (s *Server) readRecord(instance, kind, uri string, qs []qualifier) (*record, error) {
	p := s.recordPath(instance, kind, uri, qs)
	b, err := os.ReadFile(p)
	if err != nil {
		return nil, err
	}
	var rec record
	if err := json.Unmarshal(b, &rec); err != nil {
		return nil, err
	}
	return &rec, nil
}
