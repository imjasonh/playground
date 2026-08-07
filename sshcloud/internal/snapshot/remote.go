package snapshot

import (
	"bytes"
	"context"
	"encoding/base64"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"net/url"
	"strings"
	"time"
)

const refHeader = "X-Sshcloud-Snapshot-Ref"

type HTTPDoer interface {
	Do(*http.Request) (*http.Response, error)
}

// RemoteStore proxies package bytes through snapshotd. It never receives GCS
// credentials, object names, or signed URLs.
type RemoteStore struct {
	BaseURL string
	Client  HTTPDoer
}

func NewRemoteStore(baseURL string, client HTTPDoer) (*RemoteStore, error) {
	parsed, err := url.Parse(strings.TrimRight(baseURL, "/"))
	if err != nil || parsed.Scheme != "https" || parsed.Host == "" || parsed.Path != "" ||
		parsed.User != nil || parsed.RawQuery != "" || parsed.Fragment != "" || parsed.Opaque != "" {
		return nil, fmt.Errorf("snapshotd URL must be an HTTPS origin")
	}
	if client == nil {
		return nil, fmt.Errorf("authenticated snapshotd client is required")
	}
	return &RemoteStore{BaseURL: parsed.String(), Client: client}, nil
}

func (s *RemoteStore) Put(ctx context.Context, ref Ref, pkg Package) error {
	if err := ref.Validate(); err != nil {
		return err
	}
	reader, writer := io.Pipe()
	go func() {
		writer.CloseWithError(WriteArchive(ctx, writer, ref, pkg, ""))
	}()
	req, err := http.NewRequestWithContext(ctx, http.MethodPut, s.BaseURL+"/v1/snapshots/package", reader)
	if err != nil {
		_ = reader.Close()
		return err
	}
	if err := setRefHeader(req, ref); err != nil {
		_ = reader.Close()
		return err
	}
	req.Header.Set("Content-Type", "application/vnd.sshcloud.snapshot+tar")
	res, err := s.Client.Do(req)
	if err != nil {
		_ = reader.Close()
		return err
	}
	_ = reader.Close()
	defer res.Body.Close()
	if res.StatusCode != http.StatusNoContent {
		return remoteError("put", res)
	}
	return nil
}

func (s *RemoteStore) Get(ctx context.Context, ref Ref, destDir string) (Package, error) {
	pkg := NewPackageDir(destDir)
	res, err := s.doRef(ctx, http.MethodPost, "/v1/snapshots/get", ref)
	if err != nil {
		return pkg, err
	}
	defer res.Body.Close()
	if res.StatusCode != http.StatusOK {
		return pkg, remoteError("get", res)
	}
	return ReadArchive(ctx, res.Body, ref, destDir, "")
}

func (s *RemoteStore) Has(ctx context.Context, ref Ref) (bool, error) {
	res, err := s.doRef(ctx, http.MethodPost, "/v1/snapshots/has", ref)
	if err != nil {
		return false, err
	}
	defer res.Body.Close()
	if res.StatusCode != http.StatusOK {
		return false, remoteError("has", res)
	}
	var response struct {
		Exists bool `json:"exists"`
	}
	if err := decodeResponse(res.Body, &response); err != nil {
		return false, err
	}
	return response.Exists, nil
}

func (s *RemoteStore) Meta(ctx context.Context, ref Ref) (Meta, error) {
	res, err := s.doRef(ctx, http.MethodPost, "/v1/snapshots/meta", ref)
	if err != nil {
		return Meta{}, err
	}
	defer res.Body.Close()
	if res.StatusCode != http.StatusOK {
		return Meta{}, remoteError("meta", res)
	}
	var meta Meta
	if err := decodeResponse(res.Body, &meta); err != nil {
		return Meta{}, err
	}
	if err := ValidateMeta(ref, meta, ""); err != nil {
		return Meta{}, err
	}
	return meta, nil
}

func (s *RemoteStore) Delete(ctx context.Context, ref Ref) error {
	res, err := s.doRef(ctx, http.MethodPost, "/v1/snapshots/delete", ref)
	if err != nil {
		return err
	}
	defer res.Body.Close()
	if res.StatusCode != http.StatusNoContent {
		return remoteError("delete", res)
	}
	return nil
}

func (s *RemoteStore) Health(ctx context.Context) error {
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, s.BaseURL+"/v1/healthz", nil)
	if err != nil {
		return err
	}
	res, err := s.Client.Do(req)
	if err != nil {
		return err
	}
	defer res.Body.Close()
	if res.StatusCode != http.StatusOK {
		return remoteError("health", res)
	}
	return nil
}

func (s *RemoteStore) doRef(ctx context.Context, method, endpoint string, ref Ref) (*http.Response, error) {
	if err := ref.Validate(); err != nil {
		return nil, err
	}
	body, err := json.Marshal(ref)
	if err != nil {
		return nil, err
	}
	req, err := http.NewRequestWithContext(ctx, method, s.BaseURL+endpoint, bytes.NewReader(body))
	if err != nil {
		return nil, err
	}
	req.Header.Set("Content-Type", "application/json")
	return s.Client.Do(req)
}

func setRefHeader(req *http.Request, ref Ref) error {
	body, err := json.Marshal(ref)
	if err != nil {
		return err
	}
	req.Header.Set(refHeader, base64.RawURLEncoding.EncodeToString(body))
	return nil
}

func ParseRefHeader(req *http.Request) (Ref, error) {
	if req == nil {
		return Ref{}, fmt.Errorf("request is required")
	}
	values := req.Header.Values(refHeader)
	if len(values) != 1 {
		return Ref{}, fmt.Errorf("exactly one structured snapshot reference is required")
	}
	if len(values[0]) > 8192 {
		return Ref{}, fmt.Errorf("invalid structured snapshot reference")
	}
	body, err := base64.RawURLEncoding.DecodeString(values[0])
	if err != nil || base64.RawURLEncoding.EncodeToString(body) != values[0] || len(body) > 4096 {
		return Ref{}, fmt.Errorf("invalid structured snapshot reference")
	}
	var ref Ref
	if err := decodeResponse(bytes.NewReader(body), &ref); err != nil {
		return Ref{}, err
	}
	return ref, ref.Validate()
}

func decodeResponse(reader io.Reader, out any) error {
	decoder := json.NewDecoder(io.LimitReader(reader, 64<<10))
	decoder.DisallowUnknownFields()
	if err := decoder.Decode(out); err != nil {
		return err
	}
	if err := decoder.Decode(&struct{}{}); err != io.EOF {
		return fmt.Errorf("response must contain one JSON value")
	}
	return nil
}

func remoteError(operation string, res *http.Response) error {
	body, _ := io.ReadAll(io.LimitReader(res.Body, 4096))
	return fmt.Errorf("snapshotd %s: %s: %s", operation, res.Status, strings.TrimSpace(string(body)))
}

var _ Store = (*RemoteStore)(nil)

// Keep the long package transfers bounded even if a caller forgets a deadline.
const RemoteOperationTimeout = 15 * time.Minute
