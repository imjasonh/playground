// Package secret reads secrets from Secret Manager or from files.
//
// Secret Manager is reached over REST with a token from the GCE metadata
// server, so the program needs no client library and no key file. Values
// never appear in errors.
package secret

import (
	"context"
	"encoding/base64"
	"encoding/json"
	"errors"
	"fmt"
	"hash/crc32"
	"io"
	"net/http"
	"os"
	"strconv"
	"strings"
	"sync"
	"time"
)

// Func returns a secret's current value.
type Func func(context.Context) (string, error)

// File returns a Func that reads path on each call and trims surrounding
// whitespace.
func File(path string) Func {
	return func(context.Context) (string, error) {
		b, err := os.ReadFile(path)
		if err != nil {
			return "", err
		}
		v := strings.TrimSpace(string(b))
		if v == "" {
			return "", fmt.Errorf("secret file %s is empty", path)
		}
		return v, nil
	}
}

// Cached returns a Func that calls fn at most once per ttl. Errors are
// not cached.
func Cached(fn Func, ttl time.Duration) Func {
	var mu sync.Mutex
	var val string
	var at time.Time
	return func(ctx context.Context) (string, error) {
		mu.Lock()
		defer mu.Unlock()
		if val != "" && time.Since(at) < ttl {
			return val, nil
		}
		v, err := fn(ctx)
		if err != nil {
			return "", err
		}
		val, at = v, time.Now()
		return v, nil
	}
}

// Manager reads secrets from Secret Manager.
type Manager struct {
	// API is the Secret Manager endpoint. Empty means
	// https://secretmanager.googleapis.com.
	API string
	// Metadata is the metadata server. Empty means
	// http://metadata.google.internal.
	Metadata string
	// Client sends requests. Nil means a client with a 10-second timeout.
	Client *http.Client

	mu      sync.Mutex
	token   string
	expires time.Time
	project string
}

// Secret returns a Func that reads the latest version of the named
// secret. name is a secret ID in the VM's project, or a full resource
// name starting with "projects/", with or without "/versions/...".
func (m *Manager) Secret(name string) Func {
	return func(ctx context.Context) (string, error) {
		return m.access(ctx, name)
	}
}

func (m *Manager) client() *http.Client {
	if m.Client != nil {
		return m.Client
	}
	return &http.Client{Timeout: 10 * time.Second}
}

func (m *Manager) api() string {
	if m.API != "" {
		return strings.TrimSuffix(m.API, "/")
	}
	return "https://secretmanager.googleapis.com"
}

func (m *Manager) metadata() string {
	if m.Metadata != "" {
		return strings.TrimSuffix(m.Metadata, "/")
	}
	return "http://metadata.google.internal"
}

func (m *Manager) access(ctx context.Context, name string) (string, error) {
	res, err := m.resource(ctx, name)
	if err != nil {
		return "", err
	}
	tok, err := m.accessToken(ctx)
	if err != nil {
		return "", err
	}
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, m.api()+"/v1/"+res+":access", nil)
	if err != nil {
		return "", err
	}
	req.Header.Set("Authorization", "Bearer "+tok)
	resp, err := m.client().Do(req)
	if err != nil {
		return "", fmt.Errorf("accessing %s: %w", res, err)
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		if resp.StatusCode == http.StatusUnauthorized {
			m.mu.Lock()
			m.token = ""
			m.mu.Unlock()
		}
		return "", fmt.Errorf("accessing %s: %s", res, httpError(resp))
	}
	var body struct {
		Payload struct {
			Data       string `json:"data"`
			DataCrc32c string `json:"dataCrc32c"`
		} `json:"payload"`
	}
	if err := json.NewDecoder(io.LimitReader(resp.Body, 1<<20)).Decode(&body); err != nil {
		return "", fmt.Errorf("accessing %s: decoding response: %w", res, err)
	}
	data, err := base64.StdEncoding.DecodeString(body.Payload.Data)
	if err != nil {
		return "", fmt.Errorf("accessing %s: payload is not base64", res)
	}
	if body.Payload.DataCrc32c != "" {
		want, err := strconv.ParseUint(body.Payload.DataCrc32c, 10, 32)
		if err != nil || crc32.Checksum(data, crc32.MakeTable(crc32.Castagnoli)) != uint32(want) {
			return "", fmt.Errorf("accessing %s: payload checksum mismatch", res)
		}
	}
	v := strings.TrimSpace(string(data))
	if v == "" {
		return "", fmt.Errorf("secret %s is empty; add a version with gcloud secrets versions add", res)
	}
	return v, nil
}

func (m *Manager) resource(ctx context.Context, name string) (string, error) {
	if name == "" {
		return "", errors.New("empty secret name")
	}
	if !strings.HasPrefix(name, "projects/") {
		p, err := m.projectID(ctx)
		if err != nil {
			return "", err
		}
		name = "projects/" + p + "/secrets/" + name
	}
	if !strings.Contains(name, "/versions/") {
		name += "/versions/latest"
	}
	return name, nil
}

func (m *Manager) projectID(ctx context.Context) (string, error) {
	m.mu.Lock()
	defer m.mu.Unlock()
	if m.project != "" {
		return m.project, nil
	}
	b, err := m.get(ctx, "/computeMetadata/v1/project/project-id")
	if err != nil {
		return "", fmt.Errorf("reading project ID: %w", err)
	}
	m.project = strings.TrimSpace(string(b))
	return m.project, nil
}

func (m *Manager) accessToken(ctx context.Context) (string, error) {
	m.mu.Lock()
	defer m.mu.Unlock()
	if m.token != "" && time.Until(m.expires) > time.Minute {
		return m.token, nil
	}
	b, err := m.get(ctx, "/computeMetadata/v1/instance/service-accounts/default/token")
	if err != nil {
		return "", fmt.Errorf("getting access token: %w", err)
	}
	var tok struct {
		AccessToken string `json:"access_token"`
		ExpiresIn   int    `json:"expires_in"`
	}
	if err := json.Unmarshal(b, &tok); err != nil || tok.AccessToken == "" {
		return "", errors.New("getting access token: malformed response")
	}
	m.token = tok.AccessToken
	m.expires = time.Now().Add(time.Duration(tok.ExpiresIn) * time.Second)
	return m.token, nil
}

func (m *Manager) get(ctx context.Context, path string) ([]byte, error) {
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, m.metadata()+path, nil)
	if err != nil {
		return nil, err
	}
	req.Header.Set("Metadata-Flavor", "Google")
	resp, err := m.client().Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil, errors.New(httpError(resp))
	}
	return io.ReadAll(io.LimitReader(resp.Body, 64<<10))
}

// httpError describes a failed response. Error bodies from these APIs
// hold a status message, never a secret value.
func httpError(resp *http.Response) string {
	b, _ := io.ReadAll(io.LimitReader(resp.Body, 512))
	msg := strings.Join(strings.Fields(string(b)), " ")
	if msg == "" {
		return resp.Status
	}
	return resp.Status + ": " + msg
}
