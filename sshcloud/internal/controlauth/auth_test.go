package controlauth

import (
	"context"
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/tls"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/pem"
	"fmt"
	"math/big"
	"net"
	"net/http"
	"net/http/httptest"
	"net/url"
	"os"
	"path/filepath"
	"strconv"
	"testing"
	"time"

	"google.golang.org/api/idtoken"
)

type verifierFunc func(context.Context, string, VerificationPolicy) error

func (f verifierFunc) Verify(ctx context.Context, token string, policy VerificationPolicy) error {
	return f(ctx, token, policy)
}

type tokenSourceFunc func(context.Context, string) (string, error)

func (f tokenSourceFunc) Token(ctx context.Context, audience string) (string, error) {
	return f(ctx, audience)
}

func TestRequireRejectsWrongRoleAndStaticBearer(t *testing.T) {
	gateway := testLeaf(t, RoleGateway)
	agent := testLeaf(t, RoleAgent)
	accept := verifierFunc(func(_ context.Context, token string, _ VerificationPolicy) error {
		if token != "signed-google-token" {
			return fmt.Errorf("invalid token")
		}
		return nil
	})
	h := Require(accept, VerificationPolicy{
		CallerRole: RoleGateway, ServiceAccount: "gateway@example.iam.gserviceaccount.com",
		Audience: AudienceOrchestratorGateway,
	}, http.HandlerFunc(func(w http.ResponseWriter, _ *http.Request) {
		w.WriteHeader(http.StatusNoContent)
	}))

	for name, tc := range map[string]struct {
		cert  *x509.Certificate
		token string
		want  int
	}{
		"missing certificate": {},
		"wrong role":          {cert: agent, token: "signed-google-token", want: http.StatusForbidden},
		"static bearer":       {cert: gateway, token: "old-static-secret"},
		"valid":               {cert: gateway, token: "signed-google-token", want: http.StatusNoContent},
	} {
		t.Run(name, func(t *testing.T) {
			req := httptest.NewRequest(http.MethodPost, "/", nil)
			if tc.cert != nil {
				req.TLS = &tls.ConnectionState{
					Version: tls.VersionTLS13, PeerCertificates: []*x509.Certificate{tc.cert},
				}
			}
			if tc.token != "" {
				req.Header.Set("Authorization", "Bearer "+tc.token)
			}
			rec := httptest.NewRecorder()
			h.ServeHTTP(rec, req)
			want := tc.want
			if want == 0 {
				want = http.StatusUnauthorized
			}
			if rec.Code != want {
				t.Fatalf("status %d, want %d", rec.Code, want)
			}
		})
	}
}

func TestGCEVerifierRejectsWrongAudienceServiceAccountAndReplay(t *testing.T) {
	now := time.Unix(1_800_000_000, 0)
	payload := validPayload(now)
	verifier := &GCEVerifier{
		ProjectID: "test-project", ProjectNumber: "123456789",
		Now: func() time.Time { return now },
		validate: func(_ context.Context, _, _ string) (*idtoken.Payload, error) {
			return payload, nil
		},
	}
	valid := VerificationPolicy{
		CallerRole: RoleGateway, ServiceAccount: "gateway@test-project.iam.gserviceaccount.com",
		Audience: AudienceOrchestratorGateway,
	}
	if err := verifier.Verify(t.Context(), "token", valid); err != nil {
		t.Fatalf("valid payload: %v", err)
	}

	wrongAccount := valid
	wrongAccount.ServiceAccount = "orchestrator@test-project.iam.gserviceaccount.com"
	if err := verifier.Verify(t.Context(), "token", wrongAccount); err == nil {
		t.Fatal("token authorized a different service account")
	}

	wrongAudience := valid
	wrongAudience.Audience = AudienceAgent
	if err := verifier.Verify(t.Context(), "same-token-replayed", wrongAudience); err == nil {
		t.Fatal("token replayed from orchestrator audience to agent audience")
	}

	payload.Audience = AudienceAgent
	if err := verifier.Verify(t.Context(), "token", valid); err == nil {
		t.Fatal("wrong audience was accepted")
	}
	payload.Audience = AudienceOrchestratorGateway
	delete(payload.Claims["google"].(map[string]any)["compute_engine"].(map[string]any), "instance_id")
	if err := verifier.Verify(t.Context(), "token", valid); err == nil {
		t.Fatal("token without full Compute Engine claims was accepted")
	}
}

func TestPrepareRequestRequiresProductionAuthOrExplicitLoopback(t *testing.T) {
	loopback, _ := http.NewRequest(http.MethodGet, "http://127.0.0.1:8080/v1/test", nil)
	if err := PrepareRequest(loopback, nil, true); err != nil {
		t.Fatalf("explicit loopback mode: %v", err)
	}
	private, _ := http.NewRequest(http.MethodGet, "http://10.20.0.2:8080/v1/test", nil)
	if err := PrepareRequest(private, nil, true); err == nil {
		t.Fatal("insecure mode accepted a non-loopback destination")
	}

	calls := 0
	authorizer := &RequestAuthorizer{
		Audience: AudienceAgent,
		Source: tokenSourceFunc(func(_ context.Context, audience string) (string, error) {
			calls++
			if audience != AudienceAgent {
				t.Fatalf("audience %q", audience)
			}
			return "fresh-token-" + strconv.Itoa(calls), nil
		}),
	}
	for i := 1; i <= 2; i++ {
		req, _ := http.NewRequest(http.MethodGet, "https://10.20.0.2:8080/v1/test", nil)
		if err := PrepareRequest(req, authorizer, false); err != nil {
			t.Fatal(err)
		}
		if got := req.Header.Get("Authorization"); got != "Bearer fresh-token-"+strconv.Itoa(i) {
			t.Fatalf("request %d authorization %q", i, got)
		}
	}
	if calls != 2 {
		t.Fatalf("metadata token source called %d times, want once per request", calls)
	}
}

func TestTLSRejectsMissingCertificateAndWrongRole(t *testing.T) {
	pki := newTestPKI(t)
	serverFiles := pki.files(t, RoleOrchestrator, pki.caA, 10)
	handler := Require(verifierFunc(func(context.Context, string, VerificationPolicy) error {
		return nil
	}), VerificationPolicy{
		CallerRole: RoleGateway, ServiceAccount: "gateway@test-project.iam.gserviceaccount.com",
		Audience: AudienceOrchestratorGateway,
	}, http.HandlerFunc(func(w http.ResponseWriter, _ *http.Request) {
		w.WriteHeader(http.StatusNoContent)
	}))
	serverTLS, err := ServerTLSConfig(serverFiles, RoleOrchestrator)
	if err != nil {
		t.Fatal(err)
	}
	serverURL := startTLSServer(t, serverTLS, handler)

	noCert := &http.Client{Transport: &http.Transport{TLSClientConfig: &tls.Config{
		MinVersion: tls.VersionTLS13, InsecureSkipVerify: true,
	}}}
	req, _ := http.NewRequest(http.MethodGet, serverURL, nil)
	req.Header.Set("Authorization", "Bearer token")
	if _, err := noCert.Do(req); err == nil {
		t.Fatal("TLS server accepted a client without a certificate")
	}

	agentFiles := pki.files(t, RoleAgent, pki.caA, 11)
	wrongRole, err := HTTPClient(agentFiles, RoleAgent, RoleOrchestrator, time.Second)
	if err != nil {
		t.Fatal(err)
	}
	req, _ = http.NewRequest(http.MethodGet, serverURL, nil)
	req.Header.Set("Authorization", "Bearer token")
	res, err := wrongRole.Do(req)
	if err != nil {
		t.Fatal(err)
	}
	defer res.Body.Close()
	if res.StatusCode != http.StatusForbidden {
		t.Fatalf("wrong role status %d", res.StatusCode)
	}
}

func TestTLSClientRejectsWrongServerURI(t *testing.T) {
	pki := newTestPKI(t)
	serverFiles := pki.files(t, RoleAgent, pki.caA, 12)
	serverTLS, err := ServerTLSConfig(serverFiles, RoleAgent)
	if err != nil {
		t.Fatal(err)
	}
	serverURL := startTLSServer(t, serverTLS, http.HandlerFunc(func(w http.ResponseWriter, _ *http.Request) {
		w.WriteHeader(http.StatusNoContent)
	}))
	clientFiles := pki.files(t, RoleGateway, pki.caA, 13)
	client, err := HTTPClient(clientFiles, RoleGateway, RoleOrchestrator, time.Second)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := client.Get(serverURL); err == nil {
		t.Fatal("client accepted agent URI when orchestrator URI was required")
	}
}

func TestTLSReloadsLeafCertificatesAcrossTwoCAs(t *testing.T) {
	pki := newTestPKI(t)
	serverFiles := pki.files(t, RoleOrchestrator, pki.caA, 20)
	clientFiles := pki.files(t, RoleGateway, pki.caA, 21)
	serverTLS, err := ServerTLSConfig(serverFiles, RoleOrchestrator)
	if err != nil {
		t.Fatal(err)
	}
	serverURL := startTLSServer(t, serverTLS, http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		_, _ = fmt.Fprint(w, r.TLS.PeerCertificates[0].SerialNumber.String())
	}))

	clientTLS, err := ClientTLSConfig(clientFiles, RoleGateway, RoleOrchestrator)
	if err != nil {
		t.Fatal(err)
	}
	transport := &http.Transport{TLSClientConfig: clientTLS, DisableKeepAlives: true}
	client := &http.Client{Transport: transport, Timeout: time.Second}
	if body, peer := getBodyAndPeerSerial(t, client, serverURL); body != "21" || peer != "20" {
		t.Fatalf("initial client/server serials %q/%q", body, peer)
	}

	pki.writeRole(t, clientFiles.CertFile, clientFiles.KeyFile, RoleGateway, pki.caB, 22)
	pki.writeRole(t, serverFiles.CertFile, serverFiles.KeyFile, RoleOrchestrator, pki.caB, 23)
	if body, peer := getBodyAndPeerSerial(t, client, serverURL); body != "22" || peer != "23" {
		t.Fatalf("reloaded client/server serials %q/%q", body, peer)
	}
}

func startTLSServer(t *testing.T, config *tls.Config, handler http.Handler) string {
	t.Helper()
	listener, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	server := &http.Server{Handler: handler}
	t.Cleanup(func() {
		_ = server.Close()
		_ = listener.Close()
	})
	go func() {
		_ = server.Serve(tls.NewListener(listener, config))
	}()
	return "https://" + listener.Addr().String()
}

func getBodyAndPeerSerial(t *testing.T, client *http.Client, endpoint string) (string, string) {
	t.Helper()
	res, err := client.Get(endpoint)
	if err != nil {
		t.Fatal(err)
	}
	defer res.Body.Close()
	var body [32]byte
	n, _ := res.Body.Read(body[:])
	peer := ""
	if res.TLS != nil && len(res.TLS.PeerCertificates) > 0 {
		peer = res.TLS.PeerCertificates[0].SerialNumber.String()
	}
	return string(body[:n]), peer
}

func validPayload(now time.Time) *idtoken.Payload {
	return &idtoken.Payload{
		Issuer: "https://accounts.google.com", Audience: AudienceOrchestratorGateway,
		IssuedAt: now.Add(-time.Minute).Unix(), Expires: now.Add(time.Hour).Unix(),
		Claims: map[string]any{
			"email":          "gateway@test-project.iam.gserviceaccount.com",
			"email_verified": true,
			"google": map[string]any{
				"compute_engine": map[string]any{
					"instance_id":                 "987654321",
					"instance_name":               "sshcloud-gateway",
					"zone":                        "us-central1-a",
					"project_id":                  "test-project",
					"project_number":              "123456789",
					"instance_creation_timestamp": "1700000000",
				},
			},
		},
	}
}

type testCA struct {
	cert *x509.Certificate
	key  *ecdsa.PrivateKey
	pem  []byte
}

type testPKI struct {
	dir     string
	caA     testCA
	caB     testCA
	caAFile string
	caBFile string
}

func newTestPKI(t *testing.T) testPKI {
	t.Helper()
	dir := t.TempDir()
	a := makeTestCA(t, 1)
	b := makeTestCA(t, 2)
	aFile := filepath.Join(dir, "ca-a.pem")
	bFile := filepath.Join(dir, "ca-b.pem")
	if err := os.WriteFile(aFile, a.pem, 0o600); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(bFile, b.pem, 0o600); err != nil {
		t.Fatal(err)
	}
	return testPKI{dir: dir, caA: a, caB: b, caAFile: aFile, caBFile: bFile}
}

func (p testPKI) files(t *testing.T, role Role, ca testCA, serial int64) TLSFiles {
	t.Helper()
	prefix := string(role) + "-" + strconv.FormatInt(serial, 10)
	files := TLSFiles{
		CertFile:      filepath.Join(p.dir, prefix+".crt"),
		KeyFile:       filepath.Join(p.dir, prefix+".key"),
		CurrentCAFile: p.caAFile, PreviousCAFile: p.caBFile,
	}
	p.writeRole(t, files.CertFile, files.KeyFile, role, ca, serial)
	return files
}

func (p testPKI) writeRole(t *testing.T, certPath, keyPath string, role Role, ca testCA, serial int64) {
	t.Helper()
	key, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	uri, err := url.Parse(role.URI())
	if err != nil {
		t.Fatal(err)
	}
	template := &x509.Certificate{
		SerialNumber: big.NewInt(serial), Subject: pkix.Name{CommonName: string(role)},
		NotBefore: time.Now().Add(-time.Hour), NotAfter: time.Now().Add(time.Hour),
		URIs:        []*url.URL{uri},
		KeyUsage:    x509.KeyUsageDigitalSignature,
		ExtKeyUsage: []x509.ExtKeyUsage{x509.ExtKeyUsageClientAuth, x509.ExtKeyUsageServerAuth},
	}
	der, err := x509.CreateCertificate(rand.Reader, template, ca.cert, &key.PublicKey, ca.key)
	if err != nil {
		t.Fatal(err)
	}
	keyDER, err := x509.MarshalPKCS8PrivateKey(key)
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(certPath, pem.EncodeToMemory(&pem.Block{Type: "CERTIFICATE", Bytes: der}), 0o600); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(keyPath, pem.EncodeToMemory(&pem.Block{Type: "PRIVATE KEY", Bytes: keyDER}), 0o600); err != nil {
		t.Fatal(err)
	}
}

func makeTestCA(t *testing.T, serial int64) testCA {
	t.Helper()
	key, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	template := &x509.Certificate{
		SerialNumber: big.NewInt(serial), Subject: pkix.Name{CommonName: fmt.Sprintf("test-ca-%d", serial)},
		NotBefore: time.Now().Add(-time.Hour), NotAfter: time.Now().Add(time.Hour),
		IsCA: true, BasicConstraintsValid: true,
		KeyUsage: x509.KeyUsageCertSign | x509.KeyUsageCRLSign,
	}
	der, err := x509.CreateCertificate(rand.Reader, template, template, &key.PublicKey, key)
	if err != nil {
		t.Fatal(err)
	}
	cert, err := x509.ParseCertificate(der)
	if err != nil {
		t.Fatal(err)
	}
	return testCA{cert: cert, key: key, pem: pem.EncodeToMemory(&pem.Block{Type: "CERTIFICATE", Bytes: der})}
}

func testLeaf(t *testing.T, role Role) *x509.Certificate {
	t.Helper()
	uri, err := url.Parse(role.URI())
	if err != nil {
		t.Fatal(err)
	}
	return &x509.Certificate{URIs: []*url.URL{uri}}
}
