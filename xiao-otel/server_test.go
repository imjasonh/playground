package main

import (
	"bytes"
	"context"
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/sha256"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/asn1"
	"encoding/base64"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"math/big"
	"net/http"
	"net/http/httptest"
	"sync"
	"testing"
	"time"

	"github.com/fxamacker/cbor/v2"
	"github.com/imjasonh/playground/xiao-otel/internal/attest"
	"github.com/imjasonh/playground/xiao-otel/internal/otlp"
)

const testAppID = "W5LPA2QM2W.io.github.imjasonh.playground"

const sampleOTLPJSON = `{"resourceMetrics":[{"resource":{"attributes":[{"key":"service.name","value":{"stringValue":"xiao-esp32c3"}},{"key":"device.id","value":{"stringValue":"xiao-c3-01"}}]},"scopeMetrics":[{"metrics":[{"name":"mcu.wake.count","gauge":{"dataPoints":[{"asInt":"15","timeUnixNano":"1700000000000000000"}]}},{"name":"mcu.phase.duration_us","gauge":{"dataPoints":[{"asInt":"1100","timeUnixNano":"1700000000000000000","attributes":[{"key":"phase","value":{"stringValue":"sensor"}}]},{"asInt":"3400","timeUnixNano":"1700000000000000000","attributes":[{"key":"phase","value":{"stringValue":"compute"}}]},{"asInt":"320000","timeUnixNano":"1700000000000000000","attributes":[{"key":"phase","value":{"stringValue":"epd_refresh"}}]},{"asInt":"150000","timeUnixNano":"1700000000000000000","attributes":[{"key":"phase","value":{"stringValue":"radio"}}]}]}},{"name":"mcu.battery_mv","gauge":{"dataPoints":[{"asInt":"3890","timeUnixNano":"1700000000000000000"}]}},{"name":"mcu.ble.rssi","gauge":{"dataPoints":[{"asInt":"-58","timeUnixNano":"1700000000000000000"}]}}]}]}]}`

type fakeExporter struct {
	mu       sync.Mutex
	userID   string
	deviceID string
	points   []otlp.Point
}

func (f *fakeExporter) Export(_ context.Context, userID, deviceID string, points []otlp.Point) error {
	f.mu.Lock()
	defer f.mu.Unlock()
	f.userID = userID
	f.deviceID = deviceID
	f.points = append(f.points, points...)
	return nil
}

func TestAttestedHandshakeAndMetricsForwarding(t *testing.T) {
	now := time.Date(2026, 11, 20, 12, 0, 0, 0, time.UTC)

	// 1. Build a test P-384 Apple Root CA and Intermediate CA, plus a P-256 leaf key.
	rootKey, err := ecdsa.GenerateKey(elliptic.P384(), rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	rootTmpl := &x509.Certificate{
		SerialNumber:          big.NewInt(1),
		Subject:               pkix.Name{CommonName: "Test Apple App Attestation Root CA"},
		NotBefore:             now.Add(-time.Hour),
		NotAfter:              now.Add(24 * time.Hour),
		KeyUsage:              x509.KeyUsageCertSign | x509.KeyUsageCRLSign,
		BasicConstraintsValid: true,
		IsCA:                  true,
	}
	rootDER, err := x509.CreateCertificate(rand.Reader, rootTmpl, rootTmpl, &rootKey.PublicKey, rootKey)
	if err != nil {
		t.Fatal(err)
	}
	rootCert, err := x509.ParseCertificate(rootDER)
	if err != nil {
		t.Fatal(err)
	}

	verifier := &attest.Verifier{
		AppID:           testAppID,
		AllowUnattested: false,
		Roots:           []*x509.Certificate{rootCert},
		Store:           attest.NewMemoryStore(),
		Now:             func() time.Time { return now },
	}
	exp := &fakeExporter{}
	srv := &Server{Verifier: verifier, Exporter: exp}
	ts := httptest.NewServer(srv.Routes())
	defer ts.Close()

	// 2. Request a challenge for attestation.
	chal := fetchChallenge(t, ts.URL)

	// 3. Construct clientData and attestationObject.
	clientData := `{"challenge":"` + chal + `","deviceId":"iphone-15-pro","userId":"apple-user-1"}`
	clientHash := sha256.Sum256([]byte(clientData))

	leafKey, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	ecdhPub, err := leafKey.PublicKey.ECDH()
	if err != nil {
		t.Fatal(err)
	}
	pubBytes := ecdhPub.Bytes()
	keyIDSum := sha256.Sum256(pubBytes)
	keyID := base64.StdEncoding.EncodeToString(keyIDSum[:])

	authData := buildAttestAuthData(testAppID, keyIDSum[:])
	composite := append(append([]byte{}, authData...), clientHash[:]...)
	nonce := sha256.Sum256(composite)

	// Encode Apple nonce extension 1.2.840.113635.100.8.2: SEQUENCE { [1] OCTET STRING (32B) }
	nonceExtVal, err := asn1.Marshal(struct {
		Nonce []byte `asn1:"tag:1,explicit"`
	}{Nonce: nonce[:]})
	if err != nil {
		t.Fatal(err)
	}
	leafTmpl := &x509.Certificate{
		SerialNumber: big.NewInt(2),
		Subject:      pkix.Name{CommonName: "Test credCert"},
		NotBefore:    now.Add(-time.Hour),
		NotAfter:     now.Add(24 * time.Hour),
		KeyUsage:     x509.KeyUsageDigitalSignature,
		ExtraExtensions: []pkix.Extension{{
			Id:    asn1.ObjectIdentifier{1, 2, 840, 113635, 100, 8, 2},
			Value: nonceExtVal,
		}},
	}
	leafDER, err := x509.CreateCertificate(rand.Reader, leafTmpl, rootCert, &leafKey.PublicKey, rootKey)
	if err != nil {
		t.Fatal(err)
	}

	attObjBytes, err := cbor.Marshal(map[string]any{
		"fmt":      "apple-appattest",
		"authData": authData,
		"attStmt": map[string]any{
			"x5c":     [][]byte{leafDER},
			"receipt": []byte{0x01},
		},
	})
	if err != nil {
		t.Fatal(err)
	}

	// 4. Register the attested key via POST /v1/token.
	regBody, _ := json.Marshal(map[string]any{
		"keyId":             keyID,
		"attestationObject": base64.StdEncoding.EncodeToString(attObjBytes),
		"clientData":        clientData,
	})
	regResp := postJSON(t, ts.URL+"/v1/token", regBody, nil)
	if regResp.StatusCode != http.StatusOK {
		t.Fatalf("POST /v1/token status=%d", regResp.StatusCode)
	}

	// 5. Fetch a new challenge and sign a POST /v1/metrics assertion.
	metricsChal := fetchChallenge(t, ts.URL)
	otlpSum := sha256.Sum256([]byte(sampleOTLPJSON))
	metricsClientData := `{"action":"metrics","challenge":"` + metricsChal + `","payload":"` + hex.EncodeToString(otlpSum[:]) + `"}`
	assertionB64 := signAssertion(t, leafKey, testAppID, 1, []byte(metricsClientData))

	headers := map[string]string{
		"X-Apple-App-Attest-Key-Id":      keyID,
		"X-Apple-App-Attest-Assertion":   assertionB64,
		"X-Apple-App-Attest-Client-Data": base64.StdEncoding.EncodeToString([]byte(metricsClientData)),
	}
	mResp := postJSON(t, ts.URL+"/v1/metrics", []byte(sampleOTLPJSON), headers)
	if mResp.StatusCode != http.StatusOK {
		t.Fatalf("POST /v1/metrics status=%d", mResp.StatusCode)
	}
	if len(exp.points) != 7 {
		t.Fatalf("exported points=%d, want 7", len(exp.points))
	}
	if exp.userID != "apple-user-1" || exp.deviceID != "iphone-15-pro" {
		t.Fatalf("unexpected attested identities: user=%q device=%q", exp.userID, exp.deviceID)
	}

	// 6. Replaying the same counter or challenge must fail with 401.
	replayChal := fetchChallenge(t, ts.URL)
	staleClientData := `{"action":"metrics","challenge":"` + replayChal + `"}`
	staleAssertionB64 := signAssertion(t, leafKey, testAppID, 1, []byte(staleClientData))
	staleResp := postJSON(t, ts.URL+"/v1/metrics", []byte(sampleOTLPJSON), map[string]string{
		"X-Apple-App-Attest-Key-Id":      keyID,
		"X-Apple-App-Attest-Assertion":   staleAssertionB64,
		"X-Apple-App-Attest-Client-Data": base64.StdEncoding.EncodeToString([]byte(staleClientData)),
	})
	if staleResp.StatusCode != http.StatusUnauthorized {
		t.Fatalf("stale counter status=%d, want 401", staleResp.StatusCode)
	}
}

func TestUnattestedSimulatorMetricsFlowAndCloudMonitoringExport(t *testing.T) {
	var receivedReq []byte
	var receivedAuth string
	cmServer := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		receivedAuth = r.Header.Get("Authorization")
		var buf bytes.Buffer
		_, _ = buf.ReadFrom(r.Body)
		receivedReq = buf.Bytes()
		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte(`{}`))
	}))
	defer cmServer.Close()

	verifier, err := attest.NewVerifier(testAppID, true, attest.NewMemoryStore())
	if err != nil {
		t.Fatal(err)
	}
	exporter := &otlp.CloudMonitoringExporter{
		ProjectID:  "demo-gcp-proj",
		BaseURL:    cmServer.URL,
		HTTPClient: cmServer.Client(),
	}
	srv := &Server{Verifier: verifier, Exporter: exporter}
	ts := httptest.NewServer(srv.Routes())
	defer ts.Close()

	chal := fetchChallenge(t, ts.URL)
	unattestedBody, _ := json.Marshal(map[string]any{
		"clientData": `{"challenge":"` + chal + `","deviceId":"sim-1","userId":"sim-user"}`,
	})
	regResp := postJSON(t, ts.URL+"/v1/unattested-token", unattestedBody, nil)
	if regResp.StatusCode != http.StatusOK {
		t.Fatalf("unattested register status=%d", regResp.StatusCode)
	}

	mChal := fetchChallenge(t, ts.URL)
	mCD := `{"action":"metrics","challenge":"` + mChal + `"}`
	mResp := postJSON(t, ts.URL+"/v1/metrics", []byte(sampleOTLPJSON), map[string]string{
		"X-Apple-App-Attest-Key-Id":      "unattested:sim-1",
		"X-Apple-App-Attest-Client-Data": mCD,
	})
	if mResp.StatusCode != http.StatusOK {
		t.Fatalf("metrics status=%d", mResp.StatusCode)
	}
	_ = receivedAuth
	if !bytes.Contains(receivedReq, []byte(`"custom.googleapis.com/xiao_esp32c3/mcu/phase/duration_us"`)) {
		t.Fatalf("Cloud Monitoring request missing expected metric type: %s", string(receivedReq))
	}
	if !bytes.Contains(receivedReq, []byte(`"epd_refresh"`)) {
		t.Fatalf("Cloud Monitoring request missing epd_refresh phase label: %s", string(receivedReq))
	}
}

func fetchChallenge(t *testing.T, baseURL string) string {
	t.Helper()
	resp := postJSON(t, baseURL+"/v1/challenge", []byte(`{}`), nil)
	if resp.StatusCode != http.StatusOK {
		t.Fatalf("POST /v1/challenge status=%d", resp.StatusCode)
	}
	defer resp.Body.Close()
	var out struct {
		Challenge string `json:"challenge"`
	}
	if err := json.NewDecoder(resp.Body).Decode(&out); err != nil {
		t.Fatal(err)
	}
	return out.Challenge
}

func postJSON(t *testing.T, url string, body []byte, headers map[string]string) *http.Response {
	t.Helper()
	req, err := http.NewRequestWithContext(t.Context(), http.MethodPost, url, bytes.NewReader(body))
	if err != nil {
		t.Fatal(err)
	}
	req.Header.Set("Content-Type", "application/json")
	for k, v := range headers {
		req.Header.Set(k, v)
	}
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		t.Fatal(err)
	}
	return resp
}

func buildAttestAuthData(appID string, keyID []byte) []byte {
	rp := sha256.Sum256([]byte(appID))
	out := make([]byte, 0, 55+len(keyID))
	out = append(out, rp[:]...)
	out = append(out, 0x41) // AT | UP
	out = append(out, 0, 0, 0, 0)
	out = append(out, []byte("appattestdevelop")...)
	var credLen [2]byte
	binary.BigEndian.PutUint16(credLen[:], uint16(len(keyID)))
	out = append(out, credLen[:]...)
	out = append(out, keyID...)
	return out
}

func signAssertion(t *testing.T, key *ecdsa.PrivateKey, appID string, counter uint32, clientData []byte) string {
	t.Helper()
	rp := sha256.Sum256([]byte(appID))
	authData := make([]byte, 0, 37)
	authData = append(authData, rp[:]...)
	authData = append(authData, 0x01)
	var cnt [4]byte
	binary.BigEndian.PutUint32(cnt[:], counter)
	authData = append(authData, cnt[:]...)

	clientHash := sha256.Sum256(clientData)
	msg := append(append([]byte{}, authData...), clientHash[:]...)
	digest := sha256.Sum256(msg)
	sig, err := ecdsa.SignASN1(rand.Reader, key, digest[:])
	if err != nil {
		t.Fatal(err)
	}
	raw, err := cbor.Marshal(map[string]any{
		"authenticatorData": authData,
		"signature":         sig,
	})
	if err != nil {
		t.Fatal(err)
	}
	return base64.StdEncoding.EncodeToString(raw)
}
