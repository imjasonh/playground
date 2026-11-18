// Package workerpool reads and sets the replicas of one Substrate WorkerPool
// through its scale subresource, as the pod's ServiceAccount. It implements
// actorpool.Workers.
package workerpool

import (
	"bytes"
	"context"
	"crypto/tls"
	"crypto/x509"
	"encoding/json"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/url"
	"os"
	"strings"
	"time"
)

// Scaler reads and sets one WorkerPool's replicas.
type Scaler struct {
	client    *http.Client
	url       string
	tokenFile string
}

// New returns a Scaler for the WorkerPool namespace/name on the API server at
// host and port, which it verifies against the PEM bundle in caFile. It sends
// the bearer token in tokenFile, read on every request so a rotated projected
// token takes effect without a restart.
func New(host, port, caFile, tokenFile, workerPool string) (*Scaler, error) {
	namespace, name, ok := strings.Cut(workerPool, "/")
	if !ok || namespace == "" || name == "" || strings.Contains(name, "/") {
		return nil, fmt.Errorf("workerpool: %q is not namespace/name", workerPool)
	}
	if host == "" || port == "" {
		return nil, fmt.Errorf("workerpool: no API server address (host %q, port %q)", host, port)
	}
	pem, err := os.ReadFile(caFile)
	if err != nil {
		return nil, err
	}
	roots := x509.NewCertPool()
	if !roots.AppendCertsFromPEM(pem) {
		return nil, fmt.Errorf("workerpool: %s holds no certificates", caFile)
	}
	u := url.URL{
		Scheme: "https",
		Host:   net.JoinHostPort(host, port),
		Path:   fmt.Sprintf("/apis/ate.dev/v1/namespaces/%s/workerpools/%s/scale", namespace, name),
	}
	return &Scaler{
		client: &http.Client{
			Timeout:   30 * time.Second,
			Transport: &http.Transport{TLSClientConfig: &tls.Config{MinVersion: tls.VersionTLS12, RootCAs: roots}},
		},
		url:       u.String(),
		tokenFile: tokenFile,
	}, nil
}

// scale is the part of an autoscaling/v1 Scale the pool reads and writes.
type scale struct {
	Spec struct {
		Replicas int `json:"replicas"`
	} `json:"spec"`
}

// Replicas returns the WorkerPool's desired replicas.
func (s *Scaler) Replicas(ctx context.Context) (int, error) {
	var got scale
	if err := s.do(ctx, http.MethodGet, nil, &got); err != nil {
		return 0, err
	}
	return got.Spec.Replicas, nil
}

// Scale sets the WorkerPool's desired replicas.
func (s *Scaler) Scale(ctx context.Context, replicas int) error {
	var patch scale
	patch.Spec.Replicas = replicas
	body, err := json.Marshal(patch)
	if err != nil {
		return err
	}
	return s.do(ctx, http.MethodPatch, body, nil)
}

func (s *Scaler) do(ctx context.Context, method string, body []byte, out any) error {
	token, err := os.ReadFile(s.tokenFile)
	if err != nil {
		return err
	}
	req, err := http.NewRequestWithContext(ctx, method, s.url, bytes.NewReader(body))
	if err != nil {
		return err
	}
	req.Header.Set("Authorization", "Bearer "+strings.TrimSpace(string(token)))
	req.Header.Set("Accept", "application/json")
	if body != nil {
		req.Header.Set("Content-Type", "application/merge-patch+json")
	}
	resp, err := s.client.Do(req)
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	b, err := io.ReadAll(io.LimitReader(resp.Body, 1<<20))
	if err != nil {
		return err
	}
	if resp.StatusCode != http.StatusOK {
		return fmt.Errorf("%s %s: %s: %s", method, s.url, resp.Status, bytes.TrimSpace(b))
	}
	if out == nil {
		return nil
	}
	return json.Unmarshal(b, out)
}
