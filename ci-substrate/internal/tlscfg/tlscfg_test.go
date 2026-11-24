package tlscfg

import (
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/pem"
	"math/big"
	"net"
	"os"
	"path/filepath"
	"testing"
	"time"

	"google.golang.org/grpc"
	"google.golang.org/grpc/health"
	healthpb "google.golang.org/grpc/health/grpc_health_v1"
)

func writeCertPair(t *testing.T, dir, name string, tmpl *x509.Certificate, parent *x509.Certificate, parentKey any) (*x509.Certificate, *ecdsa.PrivateKey, string, string) {
	t.Helper()
	key, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	if parent == nil {
		parent = tmpl
		parentKey = key
	}
	der, err := x509.CreateCertificate(rand.Reader, tmpl, parent, &key.PublicKey, parentKey)
	if err != nil {
		t.Fatal(err)
	}
	cert, err := x509.ParseCertificate(der)
	if err != nil {
		t.Fatal(err)
	}
	certPath := filepath.Join(dir, name+".crt")
	keyPath := filepath.Join(dir, name+".key")
	if err := os.WriteFile(certPath, pem.EncodeToMemory(&pem.Block{Type: "CERTIFICATE", Bytes: der}), 0o600); err != nil {
		t.Fatal(err)
	}
	kder, err := x509.MarshalECPrivateKey(key)
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(keyPath, pem.EncodeToMemory(&pem.Block{Type: "EC PRIVATE KEY", Bytes: kder}), 0o600); err != nil {
		t.Fatal(err)
	}
	return cert, key, certPath, keyPath
}

func TestMTLSHandshake(t *testing.T) {
	dir := t.TempDir()
	now := time.Now()
	caTmpl := &x509.Certificate{
		SerialNumber:          big.NewInt(1),
		Subject:               pkix.Name{CommonName: "test-ca"},
		NotBefore:             now.Add(-time.Hour),
		NotAfter:              now.Add(time.Hour),
		IsCA:                  true,
		BasicConstraintsValid: true,
		KeyUsage:              x509.KeyUsageCertSign,
	}
	caCert, caKey, caPath, _ := writeCertPair(t, dir, "ca", caTmpl, nil, nil)

	srvTmpl := &x509.Certificate{
		SerialNumber: big.NewInt(2),
		Subject:      pkix.Name{CommonName: "localhost"},
		IPAddresses:  []net.IP{net.ParseIP("127.0.0.1")},
		NotBefore:    now.Add(-time.Hour),
		NotAfter:     now.Add(time.Hour),
		ExtKeyUsage:  []x509.ExtKeyUsage{x509.ExtKeyUsageServerAuth},
	}
	_, _, srvCert, srvKey := writeCertPair(t, dir, "server", srvTmpl, caCert, caKey)

	cliTmpl := &x509.Certificate{
		SerialNumber: big.NewInt(3),
		Subject:      pkix.Name{CommonName: "runner"},
		NotBefore:    now.Add(-time.Hour),
		NotAfter:     now.Add(time.Hour),
		ExtKeyUsage:  []x509.ExtKeyUsage{x509.ExtKeyUsageClientAuth},
	}
	_, _, cliCert, cliKey := writeCertPair(t, dir, "client", cliTmpl, caCert, caKey)

	opt, err := (ServerConfig{CertFile: srvCert, KeyFile: srvKey, ClientCAFile: caPath}).ServerOption()
	if err != nil {
		t.Fatal(err)
	}
	lis, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	srv := grpc.NewServer(opt)
	hs := health.NewServer()
	hs.SetServingStatus("", healthpb.HealthCheckResponse_SERVING)
	healthpb.RegisterHealthServer(srv, hs)
	go srv.Serve(lis)
	t.Cleanup(srv.Stop)

	// Client with valid mTLS cert succeeds.
	dialOpt, err := (ClientConfig{CAFile: caPath, CertFile: cliCert, KeyFile: cliKey}).DialOption()
	if err != nil {
		t.Fatal(err)
	}
	conn, err := grpc.NewClient(lis.Addr().String(), dialOpt)
	if err != nil {
		t.Fatal(err)
	}
	defer conn.Close()
	resp, err := healthpb.NewHealthClient(conn).Check(t.Context(), &healthpb.HealthCheckRequest{})
	if err != nil || resp.GetStatus() != healthpb.HealthCheckResponse_SERVING {
		t.Fatalf("mTLS health check = (%v, %v), want SERVING", resp, err)
	}

	// Client without a client cert fails mTLS handshake.
	noCertOpt, err := (ClientConfig{CAFile: caPath}).DialOption()
	if err != nil {
		t.Fatal(err)
	}
	badConn, err := grpc.NewClient(lis.Addr().String(), noCertOpt)
	if err != nil {
		t.Fatal(err)
	}
	defer badConn.Close()
	if _, err := healthpb.NewHealthClient(badConn).Check(t.Context(), &healthpb.HealthCheckRequest{}); err == nil {
		t.Fatal("client without cert passed mTLS check")
	}
}
