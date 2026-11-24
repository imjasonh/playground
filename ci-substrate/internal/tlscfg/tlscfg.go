// Package tlscfg builds optional TLS and mTLS gRPC transport credentials from
// PEM files. When no certificate files are configured, callers fall back to
// plaintext so local and KinD demos work without certificates.
package tlscfg

import (
	"crypto/tls"
	"crypto/x509"
	"fmt"
	"os"

	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials"
	"google.golang.org/grpc/credentials/insecure"
)

// ServerConfig configures TLS/mTLS for a gRPC server. If CertFile and KeyFile
// are empty, ServerOption returns (nil, nil) so the server runs in plaintext.
// If ClientCAFile is set, clients must present a certificate signed by that CA.
type ServerConfig struct {
	CertFile     string
	KeyFile      string
	ClientCAFile string
}

// ServerOption returns a grpc.ServerOption enabling TLS/mTLS, or nil when
// plaintext is configured.
func (c ServerConfig) ServerOption() (grpc.ServerOption, error) {
	if c.CertFile == "" && c.KeyFile == "" {
		if c.ClientCAFile != "" {
			return nil, fmt.Errorf("client CA file requires TLS cert and key files")
		}
		return nil, nil
	}
	if c.CertFile == "" || c.KeyFile == "" {
		return nil, fmt.Errorf("both TLS cert and key files must be set")
	}
	cert, err := tls.LoadX509KeyPair(c.CertFile, c.KeyFile)
	if err != nil {
		return nil, fmt.Errorf("loading server TLS keypair: %w", err)
	}
	cfg := &tls.Config{
		MinVersion:   tls.VersionTLS13,
		Certificates: []tls.Certificate{cert},
	}
	if c.ClientCAFile != "" {
		pem, err := os.ReadFile(c.ClientCAFile)
		if err != nil {
			return nil, fmt.Errorf("reading client CA file: %w", err)
		}
		pool := x509.NewCertPool()
		if !pool.AppendCertsFromPEM(pem) {
			return nil, fmt.Errorf("parsing client CA PEM %q", c.ClientCAFile)
		}
		cfg.ClientCAs = pool
		cfg.ClientAuth = tls.RequireAndVerifyClientCert
	}
	return grpc.Creds(credentials.NewTLS(cfg)), nil
}

// ClientConfig configures TLS/mTLS for a gRPC client. If Enabled is false and
// no PEM files are set, DialOption returns insecure credentials.
type ClientConfig struct {
	Enabled    bool
	CAFile     string
	CertFile   string
	KeyFile    string
	ServerName string
}

// DialOption returns transport credentials for a gRPC client.
func (c ClientConfig) DialOption() (grpc.DialOption, error) {
	if !c.Enabled && c.CAFile == "" && c.CertFile == "" && c.KeyFile == "" {
		return grpc.WithTransportCredentials(insecure.NewCredentials()), nil
	}
	cfg := &tls.Config{
		MinVersion: tls.VersionTLS13,
		ServerName: c.ServerName,
	}
	if c.CAFile != "" {
		pem, err := os.ReadFile(c.CAFile)
		if err != nil {
			return nil, fmt.Errorf("reading CA file: %w", err)
		}
		pool := x509.NewCertPool()
		if !pool.AppendCertsFromPEM(pem) {
			return nil, fmt.Errorf("parsing CA PEM %q", c.CAFile)
		}
		cfg.RootCAs = pool
	}
	if c.CertFile != "" || c.KeyFile != "" {
		if c.CertFile == "" || c.KeyFile == "" {
			return nil, fmt.Errorf("both client TLS cert and key files must be set")
		}
		cert, err := tls.LoadX509KeyPair(c.CertFile, c.KeyFile)
		if err != nil {
			return nil, fmt.Errorf("loading client TLS keypair: %w", err)
		}
		cfg.Certificates = []tls.Certificate{cert}
	}
	return grpc.WithTransportCredentials(credentials.NewTLS(cfg)), nil
}
