package controlauth

import (
	"crypto/tls"
	"crypto/x509"
	"encoding/pem"
	"fmt"
	"net/http"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"time"
)

const DefaultBundleLease = 15 * time.Minute

// TLSFiles names reloadable PEM files. CurrentCAFile and PreviousCAFile are
// both mandatory trust slots so a new CA can overlap the old CA during leaf
// rotation. Production sets BundleDir to an atomically switched, validated
// version directory. The individual paths remain for explicit local tests.
type TLSFiles struct {
	BundleDir      string
	MaxAge         time.Duration
	CertFile       string
	KeyFile        string
	CurrentCAFile  string
	PreviousCAFile string
}

func (f TLSFiles) validate() error {
	resolved, err := f.resolve()
	if err != nil {
		return err
	}
	for name, path := range map[string]string{
		"certificate": resolved.CertFile,
		"private key": resolved.KeyFile,
		"current CA":  resolved.CurrentCAFile,
		"previous CA": resolved.PreviousCAFile,
	} {
		if path == "" {
			return fmt.Errorf("control TLS %s file is required", name)
		}
	}
	return nil
}

func (f TLSFiles) resolve() (TLSFiles, error) {
	if strings.TrimSpace(f.BundleDir) == "" {
		return f, nil
	}
	dir, err := filepath.EvalSymlinks(f.BundleDir)
	if err != nil {
		return TLSFiles{}, fmt.Errorf("resolve control TLS bundle: %w", err)
	}
	info, err := os.Stat(dir)
	if err != nil {
		return TLSFiles{}, fmt.Errorf("stat control TLS bundle: %w", err)
	}
	if !info.IsDir() {
		return TLSFiles{}, fmt.Errorf("control TLS bundle %s is not a directory", dir)
	}
	return TLSFiles{
		BundleDir:      dir,
		MaxAge:         f.MaxAge,
		CertFile:       filepath.Join(dir, "tls.crt"),
		KeyFile:        filepath.Join(dir, "tls.key"),
		CurrentCAFile:  filepath.Join(dir, "ca-current.pem"),
		PreviousCAFile: filepath.Join(dir, "ca-previous.pem"),
	}, nil
}

// BundleFresh reports whether the last fully validated bundle is still inside
// its last-known-good lease. Services remain live for diagnosis but become
// unready after the lease instead of trusting stale identity indefinitely.
func BundleFresh(bundleDir string, maxAge time.Duration) error {
	if strings.TrimSpace(bundleDir) == "" {
		return nil
	}
	if maxAge <= 0 {
		maxAge = DefaultBundleLease
	}
	resolved, err := (TLSFiles{BundleDir: bundleDir}).resolve()
	if err != nil {
		return err
	}
	raw, err := os.ReadFile(filepath.Join(resolved.BundleDir, "validated-at"))
	if err != nil {
		return fmt.Errorf("read control TLS bundle validation time: %w", err)
	}
	seconds, err := strconv.ParseInt(strings.TrimSpace(string(raw)), 10, 64)
	if err != nil || seconds <= 0 {
		return fmt.Errorf("control TLS bundle validation time is invalid")
	}
	validatedAt := time.Unix(seconds, 0)
	now := time.Now()
	if validatedAt.After(now.Add(time.Minute)) {
		return fmt.Errorf("control TLS bundle validation time is in the future")
	}
	if now.Sub(validatedAt) > maxAge {
		return fmt.Errorf("control TLS bundle last-known-good lease expired")
	}
	return nil
}

type certificateReloader struct {
	files        TLSFiles
	expectedRole Role

	mu   sync.RWMutex
	last *tls.Certificate
}

func newCertificateReloader(files TLSFiles, expectedRole Role) (*certificateReloader, error) {
	if err := files.validate(); err != nil {
		return nil, err
	}
	if !validRole(expectedRole) {
		return nil, fmt.Errorf("invalid control certificate role %q", expectedRole)
	}
	reloader := &certificateReloader{files: files, expectedRole: expectedRole}
	if _, err := reloader.reload(); err != nil {
		return nil, err
	}
	return reloader, nil
}

func (r *certificateReloader) reload() (*tls.Certificate, error) {
	if r.files.BundleDir != "" {
		if err := BundleFresh(r.files.BundleDir, r.files.MaxAge); err != nil {
			return nil, err
		}
	}
	files, resolveErr := r.files.resolve()
	if resolveErr != nil {
		return r.cachedOrError(resolveErr)
	}
	cert, err := tls.LoadX509KeyPair(files.CertFile, files.KeyFile)
	if err == nil {
		if len(cert.Certificate) == 0 {
			err = fmt.Errorf("control TLS certificate chain is empty")
		} else if cert.Leaf, err = x509.ParseCertificate(cert.Certificate[0]); err == nil {
			if roleErr := certificateRole(cert.Leaf, r.expectedRole); roleErr != nil {
				err = roleErr
			} else {
				copy := cert
				r.mu.Lock()
				r.last = &copy
				r.mu.Unlock()
				return &copy, nil
			}
		}
	}
	return r.cachedOrError(fmt.Errorf("load control TLS key pair: %w", err))
}

func (r *certificateReloader) cachedOrError(err error) (*tls.Certificate, error) {
	r.mu.RLock()
	last := r.last
	r.mu.RUnlock()
	if last != nil {
		// Local/test callers may still use independent paths, and a transient
		// filesystem read can fail even for an atomically selected production
		// bundle. Retain only the last pair that parsed and matched its role.
		return last, nil
	}
	return nil, err
}

func (r *certificateReloader) certificate(*tls.ClientHelloInfo) (*tls.Certificate, error) {
	return r.reload()
}

func (r *certificateReloader) clientCertificate(*tls.CertificateRequestInfo) (*tls.Certificate, error) {
	return r.reload()
}

type rootsReloader struct {
	files TLSFiles

	mu   sync.RWMutex
	last *x509.CertPool
}

func newRootsReloader(files TLSFiles) (*rootsReloader, error) {
	reloader := &rootsReloader{files: files}
	if _, err := reloader.reload(); err != nil {
		return nil, err
	}
	return reloader, nil
}

func (r *rootsReloader) reload() (*x509.CertPool, error) {
	if r.files.BundleDir != "" {
		if err := BundleFresh(r.files.BundleDir, r.files.MaxAge); err != nil {
			return nil, err
		}
	}
	files, err := r.files.resolve()
	if err != nil {
		return r.cachedOrError(err)
	}
	pool := x509.NewCertPool()
	for _, path := range []string{files.CurrentCAFile, files.PreviousCAFile} {
		data, err := os.ReadFile(path)
		if err != nil {
			return r.cachedOrError(fmt.Errorf("read control CA %s: %w", path, err))
		}
		if !appendCertificates(pool, data) {
			return r.cachedOrError(fmt.Errorf("control CA %s contains no certificates", path))
		}
	}
	r.mu.Lock()
	r.last = pool
	r.mu.Unlock()
	return pool, nil
}

func (r *rootsReloader) cachedOrError(err error) (*x509.CertPool, error) {
	r.mu.RLock()
	last := r.last
	r.mu.RUnlock()
	if last != nil {
		return last, nil
	}
	return nil, err
}

func appendCertificates(pool *x509.CertPool, data []byte) bool {
	added := false
	for len(data) > 0 {
		block, rest := pem.Decode(data)
		data = rest
		if block == nil {
			break
		}
		if block.Type != "CERTIFICATE" {
			continue
		}
		cert, err := x509.ParseCertificate(block.Bytes)
		if err != nil {
			continue
		}
		pool.AddCert(cert)
		added = true
	}
	return added
}

// ServerTLSConfig returns a TLS 1.3-only server configuration that reloads its
// leaf and both client-CA trust slots at each handshake.
func ServerTLSConfig(files TLSFiles, serverRole Role) (*tls.Config, error) {
	if !validRole(serverRole) {
		return nil, fmt.Errorf("invalid server role %q", serverRole)
	}
	certs, err := newCertificateReloader(files, serverRole)
	if err != nil {
		return nil, err
	}
	roots, err := newRootsReloader(files)
	if err != nil {
		return nil, err
	}
	return &tls.Config{
		MinVersion:             tls.VersionTLS13,
		SessionTicketsDisabled: true,
		ClientAuth:             tls.RequireAnyClientCert,
		GetCertificate:         certs.certificate,
		VerifyPeerCertificate: func(rawCerts [][]byte, _ [][]*x509.Certificate) error {
			chain, err := parseCertificateChain(rawCerts)
			if err != nil {
				return err
			}
			pool, err := roots.reload()
			if err != nil {
				return err
			}
			if err := verifyChain(chain, pool, x509.ExtKeyUsageClientAuth); err != nil {
				return fmt.Errorf("verify control client certificate: %w", err)
			}
			if _, err := roleFromCertificate(chain[0]); err != nil {
				return err
			}
			return nil
		},
	}, nil
}

// ClientTLSConfig returns a TLS 1.3-only client configuration that dynamically
// reloads its leaf and both server-CA trust slots. Server identity is the exact
// expected role URI, not a leaf fingerprint or a DNS name.
func ClientTLSConfig(files TLSFiles, clientRole, serverRole Role) (*tls.Config, error) {
	if !validRole(clientRole) || !validRole(serverRole) {
		return nil, fmt.Errorf("invalid control TLS roles client=%q server=%q", clientRole, serverRole)
	}
	certs, err := newCertificateReloader(files, clientRole)
	if err != nil {
		return nil, err
	}
	roots, err := newRootsReloader(files)
	if err != nil {
		return nil, err
	}
	return &tls.Config{
		MinVersion:             tls.VersionTLS13,
		SessionTicketsDisabled: true,
		InsecureSkipVerify:     true, // Verification below uses dynamic roots and an exact URI SAN.
		GetClientCertificate:   certs.clientCertificate,
		VerifyConnection: func(state tls.ConnectionState) error {
			if len(state.PeerCertificates) == 0 {
				return fmt.Errorf("control server did not present a certificate")
			}
			pool, err := roots.reload()
			if err != nil {
				return err
			}
			if err := verifyChain(state.PeerCertificates, pool, x509.ExtKeyUsageServerAuth); err != nil {
				return fmt.Errorf("verify control server certificate: %w", err)
			}
			return certificateRole(state.PeerCertificates[0], serverRole)
		},
	}, nil
}

// HTTPClient creates a production control client with dynamic mTLS.
func HTTPClient(files TLSFiles, clientRole, serverRole Role, timeout time.Duration) (*http.Client, error) {
	config, err := ClientTLSConfig(files, clientRole, serverRole)
	if err != nil {
		return nil, err
	}
	transport := http.DefaultTransport.(*http.Transport).Clone()
	transport.TLSClientConfig = config
	transport.DisableKeepAlives = true
	return &http.Client{
		Transport: transport,
		Timeout:   timeout,
		CheckRedirect: func(*http.Request, []*http.Request) error {
			// A redirect would create another control request without fetching
			// a new identity token and could cross an authorization boundary.
			return http.ErrUseLastResponse
		},
	}, nil
}

// Client is a complete production control client. Callers cannot accidentally
// add an identity token without also using the role-bound mTLS transport.
type Client struct {
	http       *http.Client
	authorizer RequestAuthorizer
}

func NewClient(files TLSFiles, clientRole, serverRole Role, source TokenSource, audience string, timeout time.Duration) (*Client, error) {
	if source == nil {
		return nil, fmt.Errorf("control identity-token source is required")
	}
	httpClient, err := HTTPClient(files, clientRole, serverRole, timeout)
	if err != nil {
		return nil, err
	}
	if audience == "" {
		return nil, fmt.Errorf("control identity-token audience is required")
	}
	return &Client{
		http:       httpClient,
		authorizer: RequestAuthorizer{Source: source, Audience: audience},
	}, nil
}

func (c *Client) Do(req *http.Request) (*http.Response, error) {
	if c == nil || c.http == nil {
		return nil, fmt.Errorf("production control client is required")
	}
	if err := PrepareRequest(req, &c.authorizer, false); err != nil {
		return nil, err
	}
	return c.http.Do(req)
}

func parseCertificateChain(rawCerts [][]byte) ([]*x509.Certificate, error) {
	if len(rawCerts) == 0 {
		return nil, fmt.Errorf("mutual TLS client certificate is required")
	}
	chain := make([]*x509.Certificate, 0, len(rawCerts))
	for _, raw := range rawCerts {
		cert, err := x509.ParseCertificate(raw)
		if err != nil {
			return nil, fmt.Errorf("parse control certificate: %w", err)
		}
		chain = append(chain, cert)
	}
	return chain, nil
}

func verifyChain(chain []*x509.Certificate, roots *x509.CertPool, usage x509.ExtKeyUsage) error {
	intermediates := x509.NewCertPool()
	for _, cert := range chain[1:] {
		intermediates.AddCert(cert)
	}
	_, err := chain[0].Verify(x509.VerifyOptions{
		Roots:         roots,
		Intermediates: intermediates,
		KeyUsages:     []x509.ExtKeyUsage{usage},
	})
	return err
}

func certificateRole(cert *x509.Certificate, expected Role) error {
	role, err := roleFromCertificate(cert)
	if err != nil {
		return err
	}
	if role != expected {
		return fmt.Errorf("control certificate URI identifies %q, want %q", role, expected)
	}
	return nil
}

func roleFromCertificate(cert *x509.Certificate) (Role, error) {
	if cert == nil || len(cert.URIs) != 1 {
		return "", fmt.Errorf("control certificate must contain exactly one URI SAN")
	}
	got := cert.URIs[0].String()
	for role, uri := range roleURIs {
		if got == uri {
			return role, nil
		}
	}
	return "", fmt.Errorf("unrecognized control certificate URI %q", got)
}

// PeerRole returns the role already authenticated by ServerTLSConfig.
func PeerRole(req *http.Request) (Role, error) {
	if req == nil || req.TLS == nil || len(req.TLS.PeerCertificates) == 0 {
		return "", fmt.Errorf("mutual TLS peer certificate is required")
	}
	if req.TLS.Version != tls.VersionTLS13 {
		return "", fmt.Errorf("control connection must use TLS 1.3")
	}
	return roleFromCertificate(req.TLS.PeerCertificates[0])
}
