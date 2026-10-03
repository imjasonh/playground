package client

import (
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/tls"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/base64"
	"encoding/pem"
	"fmt"
	"math/big"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"strings"
	"sync/atomic"
	"testing"
	"time"
)

// serverCAData returns the base64 PEM of a TLS test server's certificate,
// as kubeconfig's certificate-authority-data expects.
func serverCAData(s *httptest.Server) string {
	p := pem.EncodeToMemory(&pem.Block{Type: "CERTIFICATE", Bytes: s.Certificate().Raw})
	return base64.StdEncoding.EncodeToString(p)
}

func writeFile(t *testing.T, dir, name, content string) string {
	t.Helper()
	p := filepath.Join(dir, name)
	if err := os.WriteFile(p, []byte(content), 0o600); err != nil {
		t.Fatal(err)
	}
	return p
}

// authEcho is a TLS server that reports the Authorization header it saw.
func authEcho(t *testing.T) (*httptest.Server, *atomic.Value) {
	t.Helper()
	var seen atomic.Value
	seen.Store("")
	s := httptest.NewTLSServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		seen.Store(r.Header.Get("Authorization"))
		fmt.Fprint(w, `{}`)
	}))
	t.Cleanup(s.Close)
	return s, &seen
}

func get(t *testing.T, cfg *Config) {
	t.Helper()
	c, err := New(cfg, "test")
	if err != nil {
		t.Fatal(err)
	}
	if err := c.Get(t.Context(), "/version", nil); err != nil {
		t.Fatal(err)
	}
}

func TestKubeconfigToken(t *testing.T) {
	s, seen := authEcho(t)
	dir := t.TempDir()
	p := writeFile(t, dir, "config", fmt.Sprintf(`apiVersion: v1
kind: Config
current-context: dev
clusters:
- name: c
  cluster:
    server: %s/
    certificate-authority-data: %s
contexts:
- name: dev
  context: {cluster: c, user: u, namespace: team-a}
users:
- name: u
  user:
    token: abc123
`, s.URL, serverCAData(s)))
	cfg, err := LoadKubeconfig([]string{p}, "")
	if err != nil {
		t.Fatal(err)
	}
	if cfg.Namespace != "team-a" || cfg.Host != s.URL {
		t.Errorf("cfg = %+v", cfg)
	}
	get(t, cfg)
	if got := seen.Load(); got != "Bearer abc123" {
		t.Errorf("Authorization = %q", got)
	}
}

func TestKubeconfigMergeAndRelativePaths(t *testing.T) {
	s, seen := authEcho(t)
	dir := t.TempDir()
	caPEM := pem.EncodeToMemory(&pem.Block{Type: "CERTIFICATE", Bytes: s.Certificate().Raw})
	writeFile(t, dir, "ca.crt", string(caPEM))
	writeFile(t, dir, "token", "from-file\n")
	first := writeFile(t, dir, "first", fmt.Sprintf(`current-context: prod
clusters:
- name: c
  cluster:
    server: %s
    certificate-authority: ca.crt
users:
- name: u
  user:
    tokenFile: token
`, s.URL))
	second := writeFile(t, dir, "second", `current-context: ignored
contexts:
- name: prod
  context:
    cluster: c
    user: u
- name: other
  context:
    cluster: missing
    user: u
`)
	cfg, err := LoadKubeconfig([]string{first, filepath.Join(dir, "absent"), second}, "")
	if err != nil {
		t.Fatal(err)
	}
	get(t, cfg)
	if got := seen.Load(); got != "Bearer from-file" {
		t.Errorf("Authorization = %q", got)
	}
	if _, err := LoadKubeconfig([]string{first, second}, "other"); err == nil || !strings.Contains(err.Error(), "unknown cluster") {
		t.Errorf("context with a missing cluster: err = %v", err)
	}
	if _, err := LoadKubeconfig([]string{first, second}, "nope"); err == nil {
		t.Error("missing context: want error")
	}
}

func TestKubeconfigClientCertificate(t *testing.T) {
	caKey, caCert := newCA(t)
	certPEM, keyPEM := newLeaf(t, caKey, caCert, "alice")
	pool := x509.NewCertPool()
	pool.AddCert(caCert)
	var seen atomic.Value
	s := httptest.NewUnstartedServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		seen.Store(r.TLS.PeerCertificates[0].Subject.CommonName)
		fmt.Fprint(w, `{}`)
	}))
	s.TLS = &tls.Config{ClientAuth: tls.RequireAndVerifyClientCert, ClientCAs: pool}
	s.StartTLS()
	t.Cleanup(s.Close)

	dir := t.TempDir()
	p := writeFile(t, dir, "config", fmt.Sprintf(`current-context: x
clusters: [{name: c, cluster: {server: %q, insecure-skip-tls-verify: true}}]
contexts: [{name: x, context: {cluster: c, user: u}}]
users:
- name: u
  user:
    client-certificate-data: %s
    client-key-data: %s
`, s.URL, base64.StdEncoding.EncodeToString(certPEM), base64.StdEncoding.EncodeToString(keyPEM)))
	cfg, err := LoadKubeconfig([]string{p}, "")
	if err != nil {
		t.Fatal(err)
	}
	get(t, cfg)
	if got := seen.Load(); got != "alice" {
		t.Errorf("client certificate CN = %v, want alice", got)
	}
}

func TestExecPlugin(t *testing.T) {
	s, seen := authEcho(t)
	dir := t.TempDir()
	counter := filepath.Join(dir, "count")
	script := writeFile(t, dir, "plugin.sh", `#!/bin/sh
echo x >> "`+counter+`"
case "$KUBERNETES_EXEC_INFO" in
  *'"server":"`+s.URL+`"'*) ;;
  *) echo "missing cluster info: $KUBERNETES_EXEC_INFO" >&2; exit 1 ;;
esac
echo '{"apiVersion":"client.authentication.k8s.io/v1","kind":"ExecCredential","status":{"token":"tok-'"$EXTRA"'","expirationTimestamp":"`+time.Now().Add(time.Hour).UTC().Format(time.RFC3339)+`"}}'
`)
	if err := os.Chmod(script, 0o700); err != nil {
		t.Fatal(err)
	}
	p := writeFile(t, dir, "config", fmt.Sprintf(`current-context: x
clusters:
- name: c
  cluster: {server: %q, certificate-authority-data: %s}
contexts: [{name: x, context: {cluster: c, user: u}}]
users:
- name: u
  user:
    exec:
      apiVersion: client.authentication.k8s.io/v1
      command: ./plugin.sh
      provideClusterInfo: true
      env:
      - name: EXTRA
        value: "42"
`, s.URL, serverCAData(s)))
	cfg, err := LoadKubeconfig([]string{p}, "")
	if err != nil {
		t.Fatal(err)
	}
	c, err := New(cfg, "test")
	if err != nil {
		t.Fatal(err)
	}
	for range 3 {
		if err := c.Get(t.Context(), "/version", nil); err != nil {
			t.Fatal(err)
		}
	}
	if got := seen.Load(); got != "Bearer tok-42" {
		t.Errorf("Authorization = %q", got)
	}
	runs, _ := os.ReadFile(counter)
	if n := strings.Count(string(runs), "x"); n != 1 {
		t.Errorf("plugin ran %d times, want 1 (credentials are cached until expiry)", n)
	}
	cfg.auth.reset()
	if err := c.Get(t.Context(), "/version", nil); err != nil {
		t.Fatal(err)
	}
	runs, _ = os.ReadFile(counter)
	if n := strings.Count(string(runs), "x"); n != 2 {
		t.Errorf("plugin ran %d times after reset, want 2", n)
	}
}

func TestExecPluginMissing(t *testing.T) {
	a := &execAuth{cfg: execConfig{Command: "definitely-not-a-real-plugin", InstallHint: "install it from example.com"}}
	_, err := a.authorization(t.Context())
	if err == nil || !strings.Contains(err.Error(), "install it from example.com") {
		t.Errorf("err = %v, want install hint", err)
	}
}

func TestInCluster(t *testing.T) {
	s, seen := authEcho(t)
	dir := t.TempDir()
	caPEM := pem.EncodeToMemory(&pem.Block{Type: "CERTIFICATE", Bytes: s.Certificate().Raw})
	ca := writeFile(t, dir, "ca.crt", string(caPEM))
	tok := writeFile(t, dir, "token", "sa-token")
	ns := writeFile(t, dir, "namespace", "kube-system")
	cfg, err := inCluster(s.URL, tok, ca, ns)
	if err != nil {
		t.Fatal(err)
	}
	if cfg.Namespace != "kube-system" {
		t.Errorf("Namespace = %q", cfg.Namespace)
	}
	get(t, cfg)
	if got := seen.Load(); got != "Bearer sa-token" {
		t.Errorf("Authorization = %q", got)
	}
	// A rotated token takes effect after the cached copy expires.
	writeFile(t, dir, "token", "rotated")
	cfg.auth.(*tokenFileAuth).reset()
	get(t, cfg)
	if got := seen.Load(); got != "Bearer rotated" {
		t.Errorf("Authorization after rotation = %q", got)
	}
}

func TestLoadPrecedence(t *testing.T) {
	dir := t.TempDir()
	p := writeFile(t, dir, "config", "current-context: x\nclusters: [{name: c, cluster: {server: 'https://env.example.com'}}]\ncontexts: [{name: x, context: {cluster: c}}]\n")
	t.Setenv("KUBECONFIG", p)
	cfg, err := Load("")
	if err != nil {
		t.Fatal(err)
	}
	if cfg.Host != "https://env.example.com" {
		t.Errorf("Host = %q", cfg.Host)
	}
	explicit := writeFile(t, dir, "explicit", "current-context: x\nclusters: [{name: c, cluster: {server: 'https://flag.example.com'}}]\ncontexts: [{name: x, context: {cluster: c}}]\n")
	if cfg, err = Load(explicit); err != nil || cfg.Host != "https://flag.example.com" {
		t.Errorf("Load(explicit) = %+v, %v", cfg, err)
	}
}

func newCA(t *testing.T) (*ecdsa.PrivateKey, *x509.Certificate) {
	t.Helper()
	key, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	tmpl := &x509.Certificate{
		SerialNumber:          big.NewInt(1),
		Subject:               pkix.Name{CommonName: "test-ca"},
		NotBefore:             time.Now().Add(-time.Hour),
		NotAfter:              time.Now().Add(time.Hour),
		IsCA:                  true,
		KeyUsage:              x509.KeyUsageCertSign,
		BasicConstraintsValid: true,
	}
	der, err := x509.CreateCertificate(rand.Reader, tmpl, tmpl, &key.PublicKey, key)
	if err != nil {
		t.Fatal(err)
	}
	cert, err := x509.ParseCertificate(der)
	if err != nil {
		t.Fatal(err)
	}
	return key, cert
}

func newLeaf(t *testing.T, caKey *ecdsa.PrivateKey, ca *x509.Certificate, cn string) (certPEM, keyPEM []byte) {
	t.Helper()
	key, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	tmpl := &x509.Certificate{
		SerialNumber: big.NewInt(2),
		Subject:      pkix.Name{CommonName: cn},
		NotBefore:    time.Now().Add(-time.Hour),
		NotAfter:     time.Now().Add(time.Hour),
		ExtKeyUsage:  []x509.ExtKeyUsage{x509.ExtKeyUsageClientAuth},
	}
	der, err := x509.CreateCertificate(rand.Reader, tmpl, ca, &key.PublicKey, caKey)
	if err != nil {
		t.Fatal(err)
	}
	kb, err := x509.MarshalECPrivateKey(key)
	if err != nil {
		t.Fatal(err)
	}
	return pem.EncodeToMemory(&pem.Block{Type: "CERTIFICATE", Bytes: der}), pem.EncodeToMemory(&pem.Block{Type: "EC PRIVATE KEY", Bytes: kb})
}
