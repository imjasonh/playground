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
	"github.com/imjasonh/playground/mcu-lab-backend/internal/attest"
	"github.com/imjasonh/playground/mcu-lab-backend/internal/otlp"
)

const testAppID = "TEAMID1234.com.example.playground"

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
		SerialNumber:       big.NewInt(2),
		Subject:            pkix.Name{CommonName: "Test credCert"},
		NotBefore:          now.Add(-time.Hour),
		NotAfter:           now.Add(24 * time.Hour),
		KeyUsage:           x509.KeyUsageDigitalSignature,
		SignatureAlgorithm: x509.ECDSAWithSHA256,
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
	payloadHex := hex.EncodeToString(otlpSum[:])
	metricsClientData := `{"action":"metrics","challenge":"` + metricsChal + `","payload":"` + payloadHex + `"}`
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

	// 6. Replaying the same counter or omitting the payload digest must fail with 401.
	replayChal := fetchChallenge(t, ts.URL)
	staleClientData := `{"action":"metrics","challenge":"` + replayChal + `","payload":"` + payloadHex + `"}`
	staleAssertionB64 := signAssertion(t, leafKey, testAppID, 1, []byte(staleClientData))
	staleResp := postJSON(t, ts.URL+"/v1/metrics", []byte(sampleOTLPJSON), map[string]string{
		"X-Apple-App-Attest-Key-Id":      keyID,
		"X-Apple-App-Attest-Assertion":   staleAssertionB64,
		"X-Apple-App-Attest-Client-Data": base64.StdEncoding.EncodeToString([]byte(staleClientData)),
	})
	if staleResp.StatusCode != http.StatusUnauthorized {
		t.Fatalf("stale counter status=%d, want 401", staleResp.StatusCode)
	}

	noPayloadChal := fetchChallenge(t, ts.URL)
	noPayloadCD := `{"action":"metrics","challenge":"` + noPayloadChal + `"}`
	noPayloadAssert := signAssertion(t, leafKey, testAppID, 2, []byte(noPayloadCD))
	noPayloadResp := postJSON(t, ts.URL+"/v1/metrics", []byte(sampleOTLPJSON), map[string]string{
		"X-Apple-App-Attest-Key-Id":      keyID,
		"X-Apple-App-Attest-Assertion":   noPayloadAssert,
		"X-Apple-App-Attest-Client-Data": base64.StdEncoding.EncodeToString([]byte(noPayloadCD)),
	})
	if noPayloadResp.StatusCode != http.StatusUnauthorized {
		t.Fatalf("missing payload digest status=%d, want 401", noPayloadResp.StatusCode)
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
	otlpSum := sha256.Sum256([]byte(sampleOTLPJSON))
	mCD := `{"action":"metrics","challenge":"` + mChal + `","payload":"` + hex.EncodeToString(otlpSum[:]) + `"}`
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

func TestTracesEndpointAndServerSideMetricsSpans(t *testing.T) {
	var traceRequests [][]byte
	ctServer := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		var buf bytes.Buffer
		_, _ = buf.ReadFrom(r.Body)
		traceRequests = append(traceRequests, buf.Bytes())
		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte(`{}`))
	}))
	defer ctServer.Close()

	verifier, err := attest.NewVerifier(testAppID, true, attest.NewMemoryStore())
	if err != nil {
		t.Fatal(err)
	}
	traceExp := &otlp.CloudTraceExporter{
		ProjectID:  "demo-gcp-proj",
		BaseURL:    ctServer.URL,
		HTTPClient: ctServer.Client(),
	}
	srv := &Server{
		Verifier:      verifier,
		TraceExporter: traceExp,
	}
	ts := httptest.NewServer(srv.Routes())
	defer ts.Close()

	// Register unattested simulator device.
	chal := fetchChallenge(t, ts.URL)
	regBody, _ := json.Marshal(map[string]any{
		"clientData": `{"challenge":"` + chal + `","deviceId":"sim-trace","userId":"sim-user"}`,
	})
	if resp := postJSON(t, ts.URL+"/v1/unattested-token", regBody, nil); resp.StatusCode != http.StatusOK {
		t.Fatalf("unattested register status=%d", resp.StatusCode)
	}

	// 1. POST /v1/traces with a wake waterfall.
	sampleTraceJSON := `{
		"resourceSpans": [{
			"resource": {"attributes": [
				{"key": "service.name", "value": {"stringValue": "xiao-esp32c3"}},
				{"key": "device.id", "value": {"stringValue": "xiao-c3-01"}}
			]},
			"scopeSpans": [{
				"spans": [{
					"traceId": "0123456789abcdef0123456789abcdef",
					"spanId": "1111111111111111",
					"name": "xiao.wake",
					"startTimeUnixNano": "1700000000000000000",
					"endTimeUnixNano": "1700000000478000000",
					"attributes": [
						{"key": "mcu.wake.count", "value": {"intValue": "42"}},
						{"key": "mcu.heap.free_bytes", "value": {"intValue": "210944"}}
					],
					"events": [{
						"timeUnixNano": "1700000000100000000",
						"name": "pc.hotspot",
						"attributes": [{"key": "pc", "value": {"stringValue": "0x42001234"}}]
					}]
				}, {
					"traceId": "0123456789abcdef0123456789abcdef",
					"spanId": "2222222222222222",
					"parentSpanId": "1111111111111111",
					"name": "epd.busy_wait",
					"startTimeUnixNano": "1700000000005000000",
					"endTimeUnixNano": "1700000000325000000"
				}]
			}]
		}]
	}`
	tChal := fetchChallenge(t, ts.URL)
	tSum := sha256.Sum256([]byte(sampleTraceJSON))
	tCD := `{"action":"traces","challenge":"` + tChal + `","payload":"` + hex.EncodeToString(tSum[:]) + `"}`
	tResp := postJSON(t, ts.URL+"/v1/traces", []byte(sampleTraceJSON), map[string]string{
		"X-Apple-App-Attest-Key-Id":      "unattested:sim-trace",
		"X-Apple-App-Attest-Client-Data": base64.StdEncoding.EncodeToString([]byte(tCD)),
	})
	if tResp.StatusCode != http.StatusOK {
		t.Fatalf("traces status=%d", tResp.StatusCode)
	}
	if len(traceRequests) != 1 {
		t.Fatalf("expected 1 Cloud Trace batchWrite call, got %d", len(traceRequests))
	}
	if !bytes.Contains(traceRequests[0], []byte(`"epd.busy_wait"`)) || !bytes.Contains(traceRequests[0], []byte(`"pc.hotspot"`)) {
		t.Fatalf("Cloud Trace payload missing expected spans/events: %s", string(traceRequests[0]))
	}

	// 2. POST /v1/metrics with W3C traceparent emits server-side spans under the same trace.
	mChal := fetchChallenge(t, ts.URL)
	mSum := sha256.Sum256([]byte(sampleOTLPJSON))
	mCD := `{"action":"metrics","challenge":"` + mChal + `","payload":"` + hex.EncodeToString(mSum[:]) + `"}`
	mResp := postJSON(t, ts.URL+"/v1/metrics", []byte(sampleOTLPJSON), map[string]string{
		"X-Apple-App-Attest-Key-Id":      "unattested:sim-trace",
		"X-Apple-App-Attest-Client-Data": mCD,
		"traceparent":                    "00-0123456789abcdef0123456789abcdef-1111111111111111-01",
	})
	if mResp.StatusCode != http.StatusOK {
		t.Fatalf("metrics with traceparent status=%d", mResp.StatusCode)
	}
	if len(traceRequests) != 2 {
		t.Fatalf("expected 2 Cloud Trace batchWrite calls, got %d", len(traceRequests))
	}
	if !bytes.Contains(traceRequests[1], []byte(`"mcu-lab-backend.app_attest.verify"`)) {
		t.Fatalf("server-side spans missing app_attest.verify: %s", string(traceRequests[1]))
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
	nonce := sha256.Sum256(msg)
	digest := sha256.Sum256(nonce[:])
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

func TestCoredumpsEndpoint(t *testing.T) {
	verifier, err := attest.NewVerifier(testAppID, true, attest.NewMemoryStore())
	if err != nil {
		t.Fatal(err)
	}
	srv := &Server{
		Verifier: verifier,
	}
	ts := httptest.NewServer(srv.Routes())
	defer ts.Close()

	chal := fetchChallenge(t, ts.URL)
	regBody, _ := json.Marshal(map[string]any{
		"clientData": `{"challenge":"` + chal + `","deviceId":"sim-cd","userId":"sim-user"}`,
	})
	if resp := postJSON(t, ts.URL+"/v1/unattested-token", regBody, nil); resp.StatusCode != http.StatusOK {
		t.Fatalf("unattested register status=%d", resp.StatusCode)
	}

	cdBody := []byte(`{"app":"xiao-esp32c3","board":"xiao-esp32c3","deviceId":"dev-1","pcs":["0x42001234"]}`)
	cChal := fetchChallenge(t, ts.URL)
	cSum := sha256.Sum256(cdBody)
	cCD := `{"action":"coredump","challenge":"` + cChal + `","payload":"` + hex.EncodeToString(cSum[:]) + `"}`
	resp := postJSON(t, ts.URL+"/v1/coredumps", cdBody, map[string]string{
		"X-Apple-App-Attest-Key-Id":      "unattested:sim-cd",
		"X-Apple-App-Attest-Client-Data": base64.StdEncoding.EncodeToString([]byte(cCD)),
	})
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		t.Fatalf("coredumps status=%d", resp.StatusCode)
	}
	var out struct {
		Accepted     bool     `json:"accepted"`
		ExtractedPCs []string `json:"extractedPCs"`
	}
	if err := json.NewDecoder(resp.Body).Decode(&out); err != nil {
		t.Fatal(err)
	}
	if !out.Accepted || len(out.ExtractedPCs) != 1 || out.ExtractedPCs[0] != "0x42001234" {
		t.Fatalf("unexpected coredump response: %+v", out)
	}
}
