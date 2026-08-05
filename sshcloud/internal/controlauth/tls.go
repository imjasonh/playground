package controlauth

import (
	"crypto/tls"
	"crypto/x509"
	"encoding/pem"
	"fmt"
	"net/http"
	"os"
	"sync"
	"time"
)

// TLSFiles names reloadable PEM files. CurrentCAFile and PreviousCAFile are
// both mandatory trust slots so a new CA can overlap the old CA during leaf
// rotation. Files are reread for every new TLS handshake.
type TLSFiles struct {
	CertFile       string
	KeyFile        string
	CurrentCAFile  string
	PreviousCAFile string
}

func (f TLSFiles) validate() error {
	for name, path := range map[string]string{
		"certificate": f.CertFile,
		"private key": f.KeyFile,
		"current CA":  f.CurrentCAFile,
		"previous CA": f.PreviousCAFile,
	} {
		if path == "" {
			return fmt.Errorf("control TLS %s file is required", name)
		}
	}
	return nil
}

type certificateReloader struct {
	files TLSFiles

	mu   sync.RWMutex
	last *tls.Certificate
}

func newCertificateReloader(files TLSFiles) (*certificateReloader, error) {
	if err := files.validate(); err != nil {
		return nil, err
	}
	reloader := &certificateReloader{files: files}
	if _, err := reloader.reload(); err != nil {
		return nil, err
	}
	return reloader, nil
}

func (r *certificateReloader) reload() (*tls.Certificate, error) {
	cert, err := tls.LoadX509KeyPair(r.files.CertFile, r.files.KeyFile)
	if err == nil {
		if len(cert.Certificate) == 0 {
			err = fmt.Errorf("control TLS certificate chain is empty")
		} else if cert.Leaf, err = x509.ParseCertificate(cert.Certificate[0]); err == nil {
			copy := cert
			r.mu.Lock()
			r.last = &copy
			r.mu.Unlock()
			return &copy, nil
		}
	}
	r.mu.RLock()
	last := r.last
	r.mu.RUnlock()
	if last != nil {
		// Secret refreshers replace the cert and key independently. Retaining
		// the last valid pair avoids a transient mismatch during that window.
		return last, nil
	}
	return nil, fmt.Errorf("load control TLS key pair: %w", err)
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
	pool := x509.NewCertPool()
	for _, path := range []string{r.files.CurrentCAFile, r.files.PreviousCAFile} {
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
	certs, err := newCertificateReloader(files)
	if err != nil {
		return nil, err
	}
	roots, err := newRootsReloader(files)
	if err != nil {
		return nil, err
	}
	if cert, err := certs.reload(); err != nil {
		return nil, err
	} else if err := certificateRole(cert.Leaf, serverRole); err != nil {
		return nil, fmt.Errorf("server certificate: %w", err)
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
	certs, err := newCertificateReloader(files)
	if err != nil {
		return nil, err
	}
	roots, err := newRootsReloader(files)
	if err != nil {
		return nil, err
	}
	if cert, err := certs.reload(); err != nil {
		return nil, err
	} else if err := certificateRole(cert.Leaf, clientRole); err != nil {
		return nil, fmt.Errorf("client certificate: %w", err)
	}
	return &tls.Config{
		MinVersion:             tls.VersionTLS13,
		SessionTicketsDisabled: true,
		InsecureSkipVerify:     true, // Verification below uses dynamic roots and an exact URI SAN.
		GetClientCertificate: certs.clientCertificate,
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
