package client

import (
	"bytes"
	"context"
	"crypto/tls"
	"encoding/json"
	"errors"
	"fmt"
	"net/http"
	"os"
	"os/exec"
	"strings"
	"sync"
	"time"
)

// authenticator supplies credentials for each request.
type authenticator interface {
	// authorization returns the Authorization header value, or "".
	authorization(ctx context.Context) (string, error)
	// certificate returns a client certificate obtained at request time, or
	// nil when credentials come from the static TLS configuration.
	certificate(ctx context.Context) (*tls.Certificate, error)
	// reset drops cached credentials, for example after a 401 response.
	reset()
}

type staticAuth string

func (s staticAuth) authorization(context.Context) (string, error)        { return string(s), nil }
func (staticAuth) certificate(context.Context) (*tls.Certificate, error) { return nil, nil }
func (staticAuth) reset()                                                {}

// tokenFileAuth rereads a bearer token file at most once a minute, so
// rotated service account tokens take effect without a restart.
type tokenFileAuth struct {
	path string

	mu     sync.Mutex
	cached string
	readAt time.Time
}

const tokenFileTTL = time.Minute

func (t *tokenFileAuth) token() (string, error) {
	t.mu.Lock()
	defer t.mu.Unlock()
	if t.cached != "" && time.Since(t.readAt) < tokenFileTTL {
		return t.cached, nil
	}
	b, err := os.ReadFile(t.path)
	if err != nil {
		if t.cached != "" {
			return t.cached, nil
		}
		return "", fmt.Errorf("reading token file: %w", err)
	}
	t.cached, t.readAt = strings.TrimSpace(string(b)), time.Now()
	return t.cached, nil
}

func (t *tokenFileAuth) authorization(context.Context) (string, error) {
	tok, err := t.token()
	if err != nil {
		return "", err
	}
	return "Bearer " + tok, nil
}

func (*tokenFileAuth) certificate(context.Context) (*tls.Certificate, error) { return nil, nil }

func (t *tokenFileAuth) reset() {
	t.mu.Lock()
	t.readAt = time.Time{}
	t.mu.Unlock()
}

// execConfig is the kubeconfig "exec" credential plugin stanza.
type execConfig struct {
	APIVersion string   `json:"apiVersion"`
	Command    string   `json:"command"`
	Args       []string `json:"args"`
	Env        []struct {
		Name  string `json:"name"`
		Value string `json:"value"`
	} `json:"env"`
	InstallHint        string `json:"installHint"`
	ProvideClusterInfo bool   `json:"provideClusterInfo"`
}

// execAuth runs a client-go credential plugin and caches its result until it
// expires or the server rejects it.
type execAuth struct {
	cfg      execConfig
	server   string
	caData   string
	insecure bool

	mu      sync.Mutex
	token   string
	cert    *tls.Certificate
	expires time.Time
	valid   bool
}

type execCredential struct {
	APIVersion string `json:"apiVersion"`
	Kind       string `json:"kind"`
	Spec       struct {
		Interactive bool `json:"interactive"`
		Cluster     *struct {
			Server                   string `json:"server"`
			CertificateAuthorityData string `json:"certificate-authority-data,omitempty"`
			InsecureSkipTLSVerify    bool   `json:"insecure-skip-tls-verify,omitempty"`
		} `json:"cluster,omitempty"`
	} `json:"spec"`
	Status *struct {
		Token                 string    `json:"token"`
		ClientCertificateData string    `json:"clientCertificateData"`
		ClientKeyData         string    `json:"clientKeyData"`
		ExpirationTimestamp   time.Time `json:"expirationTimestamp,omitzero"`
	} `json:"status,omitempty"`
}

// execRefreshSlack renews credentials this long before they expire, so a
// request doesn't start with a token that lapses in flight.
const execRefreshSlack = 30 * time.Second

func (e *execAuth) refresh(ctx context.Context) error {
	e.mu.Lock()
	defer e.mu.Unlock()
	if e.valid && (e.expires.IsZero() || time.Until(e.expires) > execRefreshSlack) {
		return nil
	}
	apiVersion := e.cfg.APIVersion
	if apiVersion == "" {
		apiVersion = "client.authentication.k8s.io/v1"
	}
	var in execCredential
	in.APIVersion, in.Kind = apiVersion, "ExecCredential"
	if e.cfg.ProvideClusterInfo {
		in.Spec.Cluster = &struct {
			Server                   string `json:"server"`
			CertificateAuthorityData string `json:"certificate-authority-data,omitempty"`
			InsecureSkipTLSVerify    bool   `json:"insecure-skip-tls-verify,omitempty"`
		}{e.server, e.caData, e.insecure}
	}
	info, err := json.Marshal(in)
	if err != nil {
		return err
	}
	cmd := exec.CommandContext(ctx, e.cfg.Command, e.cfg.Args...) // #nosec G204 -- the kubeconfig names the plugin.
	cmd.Env = append(os.Environ(), "KUBERNETES_EXEC_INFO="+string(info))
	for _, kv := range e.cfg.Env {
		cmd.Env = append(cmd.Env, kv.Name+"="+kv.Value)
	}
	var stdout, stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = &stdout, &stderr
	if err := cmd.Run(); err != nil {
		var notFound *exec.Error
		if errors.As(err, &notFound) && e.cfg.InstallHint != "" {
			return fmt.Errorf("credential plugin %q: %w\n%s", e.cfg.Command, err, e.cfg.InstallHint)
		}
		return fmt.Errorf("credential plugin %q: %w: %s", e.cfg.Command, err, strings.TrimSpace(stderr.String()))
	}
	var out execCredential
	if err := json.Unmarshal(stdout.Bytes(), &out); err != nil {
		return fmt.Errorf("credential plugin %q: decoding output: %w", e.cfg.Command, err)
	}
	if out.Status == nil {
		return fmt.Errorf("credential plugin %q returned no status", e.cfg.Command)
	}
	e.token, e.cert = out.Status.Token, nil
	if out.Status.ClientCertificateData != "" {
		cert, err := tls.X509KeyPair([]byte(out.Status.ClientCertificateData), []byte(out.Status.ClientKeyData))
		if err != nil {
			return fmt.Errorf("credential plugin %q: client certificate: %w", e.cfg.Command, err)
		}
		e.cert = &cert
	}
	if e.token == "" && e.cert == nil {
		return fmt.Errorf("credential plugin %q returned neither a token nor a certificate", e.cfg.Command)
	}
	e.expires, e.valid = out.Status.ExpirationTimestamp, true
	return nil
}

func (e *execAuth) authorization(ctx context.Context) (string, error) {
	if err := e.refresh(ctx); err != nil {
		return "", err
	}
	e.mu.Lock()
	defer e.mu.Unlock()
	if e.token == "" {
		return "", nil
	}
	return "Bearer " + e.token, nil
}

func (e *execAuth) certificate(ctx context.Context) (*tls.Certificate, error) {
	if err := e.refresh(ctx); err != nil {
		return nil, err
	}
	e.mu.Lock()
	defer e.mu.Unlock()
	return e.cert, nil
}

func (e *execAuth) reset() {
	e.mu.Lock()
	e.valid = false
	e.mu.Unlock()
}

// authTransport adds credentials and a User-Agent to each request.
type authTransport struct {
	base      http.RoundTripper
	auth      authenticator
	userAgent string
}

func (t *authTransport) RoundTrip(req *http.Request) (*http.Response, error) {
	req = req.Clone(req.Context())
	if t.userAgent != "" {
		req.Header.Set("User-Agent", t.userAgent)
	}
	if t.auth != nil {
		h, err := t.auth.authorization(req.Context())
		if err != nil {
			return nil, err
		}
		if h != "" {
			req.Header.Set("Authorization", h)
		}
	}
	resp, err := t.base.RoundTrip(req)
	if err == nil && resp.StatusCode == http.StatusUnauthorized && t.auth != nil {
		t.auth.reset()
	}
	return resp, err
}
