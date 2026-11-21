// Package attest verifies Apple App Attest handshakes and per-request
// assertions for the xiao-otel Cloud Run service.
package attest

import (
	"bytes"
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/sha256"
	"crypto/sha512"
	"crypto/x509"
	"encoding/asn1"
	"encoding/base64"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"encoding/pem"
	"errors"
	"fmt"
	"strings"
	"sync"
	"time"

	"github.com/fxamacker/cbor/v2"
)

// AppleAppAttestRootPEM is Apple's official App Attestation Root CA certificate.
const AppleAppAttestRootPEM = `-----BEGIN CERTIFICATE-----
MIICITCCAaegAwIBAgIQC/O+DvHN0uD7jG5yH2IXmDAKBggqhkjOPQQDAzBSMSYw
JAYDVQQDDB1BcHBsZSBBcHAgQXR0ZXN0YXRpb24gUm9vdCBDQTETMBEGA1UECgwK
QXBwbGUgSW5jLjETMBEGA1UECAwKQ2FsaWZvcm5pYTAeFw0yMDAzMTgxODMyNTNa
Fw00NTAzMTUwMDAwMDBaMFIxJjAkBgNVBAMMHUFwcGxlIEFwcCBBdHRlc3RhdGlv
biBSb290IENBMRMwEQYDVQQKDApBcHBsZSBJbmMuMRMwEQYDVQQIDApDYWxpZm9y
bmlhMHYwEAYHKoZIzj0CAQYFK4EEACIDYgAERTHhmLW07ATaFQIEVwTtT4dyctdh
NbJhFs/Ii2FdCgAHGbpphY3+d8qjuDngIN3WVhQUBHAoMeQ/cLiP1sOUtgjqK9au
Yen1mMEvRq9Sk3Jm5X8U62H+xTD3FE9TgS41o0IwQDAPBgNVHRMBAf8EBTADAQH/
MB0GA1UdDgQWBBSskRBTM72+aEH/pwyp5frq5eWKoTAOBgNVHQ8BAf8EBAMCAQYw
CgYIKoZIzj0EAwMDaAAwZQIwQgFGnByvsiVbpTKwSga0kP0e8EeDS4+sQmTvb7vn
53O5+FRXgeLhpJ06ysC5PrOyAjEAp5U4xDgEgllF7En3VcE3iexZZtKeYnpqtijV
oyFraWVIyd/dganmrduC1bmTBGwD
-----END CERTIFICATE-----`

const (
	// ActionMetrics is the action string bound into each POST /v1/metrics assertion.
	ActionMetrics = "metrics"
	// ActionWhoami is the action string bound into each POST /v1/whoami assertion.
	ActionWhoami = "whoami"

	challengeTTL        = 5 * time.Minute
	unattestedKeyPrefix = "unattested:"
	maxClientDataBytes  = 2 * 1024
	maxAttestationBytes = 16 * 1024
	maxAssertionBytes   = 8 * 1024
	maxChallenges       = 4096
	maxDevices          = 4096
	maxFieldChars       = 128
	flagAT              = 0x40
)

var (
	aaguidProduction  = []byte("appattest\x00\x00\x00\x00\x00\x00\x00")
	aaguidDevelopment = []byte("appattestdevelop")
	nonceOID          = asn1.ObjectIdentifier{1, 2, 840, 113635, 100, 8, 2}
	oidECDSASHA256    = asn1.ObjectIdentifier{1, 2, 840, 10045, 4, 3, 2}
	oidECDSASHA384    = asn1.ObjectIdentifier{1, 2, 840, 10045, 4, 3, 3}
)

// ParseRootPEM parses a PEM-encoded X.509 root certificate.
func ParseRootPEM(pemText string) (*x509.Certificate, error) {
	block, _ := pem.Decode([]byte(pemText))
	if block == nil {
		return nil, errors.New("decode root PEM")
	}
	return x509.ParseCertificate(block.Bytes)
}

// DeviceRecord holds an attested (or Simulator unattested) device registration.
type DeviceRecord struct {
	KeyID       string    `json:"keyId"`
	UserID      string    `json:"userId"`
	DeviceID    string    `json:"deviceId"`
	PublicKey   []byte    `json:"publicKey,omitempty"`
	Counter     uint32    `json:"counter"`
	Unattested  bool      `json:"unattested"`
	Development bool      `json:"development"`
	CreatedAt   time.Time `json:"createdAt"`
}

// Store persists challenges and attested device records.
type Store interface {
	PutChallenge(challenge string, expiresAt time.Time) error
	ConsumeChallenge(challenge string, now time.Time) error
	GetDevice(keyID string) (*DeviceRecord, error)
	PutDevice(rec *DeviceRecord) error
}

// MemoryStore is an in-memory Store for Cloud Run instances and unit tests.
type MemoryStore struct {
	mu         sync.Mutex
	challenges map[string]time.Time
	devices    map[string]DeviceRecord
}

// NewMemoryStore returns an initialized MemoryStore.
func NewMemoryStore() *MemoryStore {
	return &MemoryStore{
		challenges: make(map[string]time.Time),
		devices:    make(map[string]DeviceRecord),
	}
}

// PutChallenge stores a one-time challenge nonce with its expiration time.
func (s *MemoryStore) PutChallenge(challenge string, expiresAt time.Time) error {
	s.mu.Lock()
	defer s.mu.Unlock()
	now := expiresAt.Add(-challengeTTL)
	for k, exp := range s.challenges {
		if now.After(exp) {
			delete(s.challenges, k)
		}
	}
	if len(s.challenges) >= maxChallenges {
		var oldestKey string
		var oldestExp time.Time
		for k, exp := range s.challenges {
			if oldestKey == "" || exp.Before(oldestExp) {
				oldestKey = k
				oldestExp = exp
			}
		}
		if oldestKey != "" {
			delete(s.challenges, oldestKey)
		}
	}
	s.challenges[challenge] = expiresAt
	return nil
}

// ConsumeChallenge atomically verifies and deletes a challenge nonce.
func (s *MemoryStore) ConsumeChallenge(challenge string, now time.Time) error {
	s.mu.Lock()
	defer s.mu.Unlock()
	exp, ok := s.challenges[challenge]
	if !ok {
		return errors.New("unknown or already used challenge")
	}
	delete(s.challenges, challenge)
	if now.After(exp) {
		return errors.New("challenge expired")
	}
	return nil
}

// GetDevice looks up a registered device by keyID.
func (s *MemoryStore) GetDevice(keyID string) (*DeviceRecord, error) {
	s.mu.Lock()
	defer s.mu.Unlock()
	rec, ok := s.devices[keyID]
	if !ok {
		return nil, nil
	}
	copyRec := rec
	copyRec.PublicKey = bytes.Clone(rec.PublicKey)
	return &copyRec, nil
}

// PutDevice saves or updates a registered device record.
func (s *MemoryStore) PutDevice(rec *DeviceRecord) error {
	s.mu.Lock()
	defer s.mu.Unlock()
	if _, exists := s.devices[rec.KeyID]; !exists && len(s.devices) >= maxDevices {
		var oldestKey string
		var oldestTime time.Time
		for k, v := range s.devices {
			if oldestKey == "" || v.CreatedAt.Before(oldestTime) {
				oldestKey = k
				oldestTime = v.CreatedAt
			}
		}
		if oldestKey != "" {
			delete(s.devices, oldestKey)
		}
	}
	copyRec := *rec
	copyRec.PublicKey = bytes.Clone(rec.PublicKey)
	s.devices[rec.KeyID] = copyRec
	return nil
}

// Verifier checks App Attest handshakes and per-request assertions.
type Verifier struct {
	AppID           string
	AllowUnattested bool
	Roots           []*x509.Certificate
	Store           Store
	Now             func() time.Time
	verifyMu        sync.Mutex
}

// NewVerifier creates a Verifier anchored at Apple's App Attestation Root CA.
func NewVerifier(appID string, allowUnattested bool, store Store) (*Verifier, error) {
	root, err := ParseRootPEM(AppleAppAttestRootPEM)
	if err != nil {
		return nil, err
	}
	return &Verifier{
		AppID:           appID,
		AllowUnattested: allowUnattested,
		Roots:           []*x509.Certificate{root},
		Store:           store,
		Now:             time.Now,
	}, nil
}

// IssueChallenge generates and stores a 32-byte random hex challenge.
func (v *Verifier) IssueChallenge() (string, uint64, error) {
	buf := make([]byte, 32)
	if _, err := rand.Read(buf); err != nil {
		return "", 0, err
	}
	chal := hex.EncodeToString(buf)
	now := v.Now()
	exp := now.Add(challengeTTL)
	if err := v.Store.PutChallenge(chal, exp); err != nil {
		return "", 0, err
	}
	return chal, uint64(exp.Unix()), nil
}

// ClientData is the JSON payload hashed by the iOS app during key attestation.
type ClientData struct {
	Challenge string `json:"challenge"`
	UserID    string `json:"userId"`
	DeviceID  string `json:"deviceId"`
}

// AssertionClientData is the JSON payload hashed by the iOS app for generateAssertion.
type AssertionClientData struct {
	Action    string `json:"action"`
	Challenge string `json:"challenge"`
	Payload   string `json:"payload,omitempty"`
}

func parseClientData(raw []byte) (*ClientData, error) {
	if len(raw) == 0 || len(raw) > maxClientDataBytes {
		return nil, errors.New("clientData is missing or too large")
	}
	var cd ClientData
	if err := json.Unmarshal(raw, &cd); err != nil {
		return nil, errors.New("clientData is not JSON")
	}
	for name, val := range map[string]string{
		"challenge": cd.Challenge,
		"userId":    cd.UserID,
		"deviceId":  cd.DeviceID,
	} {
		if val == "" || len(val) > maxFieldChars {
			return nil, fmt.Errorf("%s is empty or too long", name)
		}
	}
	return &cd, nil
}

func parseAssertionClientData(raw []byte, wantAction string) (*AssertionClientData, error) {
	if len(raw) == 0 || len(raw) > maxClientDataBytes {
		return nil, errors.New("clientData is missing or too large")
	}
	var acd AssertionClientData
	if err := json.Unmarshal(raw, &acd); err != nil {
		return nil, errors.New("clientData is not JSON")
	}
	if acd.Challenge == "" || len(acd.Challenge) > maxFieldChars {
		return nil, errors.New("challenge is empty or too long")
	}
	if acd.Action != wantAction {
		return nil, fmt.Errorf("clientData action %q does not match %q", acd.Action, wantAction)
	}
	return &acd, nil
}

// Register verifies a DCAppAttestService.attestKey object and stores the device public key.
func (v *Verifier) Register(keyID, attestationB64 string, clientDataRaw []byte) (*DeviceRecord, error) {
	cd, err := parseClientData(clientDataRaw)
	if err != nil {
		return nil, err
	}
	now := v.Now()
	if err := v.Store.ConsumeChallenge(cd.Challenge, now); err != nil {
		return nil, err
	}
	attBytes, err := decodeBase64(attestationB64)
	if err != nil {
		return nil, errors.New("attestationObject is not valid base64")
	}
	if len(attBytes) > maxAttestationBytes {
		return nil, errors.New("attestationObject too large")
	}
	clientHash := sha256.Sum256(clientDataRaw)
	pubKey, dev, err := v.verifyAttestationObject(keyID, attBytes, clientHash[:], now)
	if err != nil {
		return nil, err
	}
	v.verifyMu.Lock()
	defer v.verifyMu.Unlock()
	existing, err := v.Store.GetDevice(keyID)
	if err != nil {
		return nil, err
	}
	var prevCounter uint32
	if existing != nil {
		prevCounter = existing.Counter
	}
	rec := &DeviceRecord{
		KeyID:       keyID,
		UserID:      cd.UserID,
		DeviceID:    cd.DeviceID,
		PublicKey:   pubKey,
		Counter:     prevCounter,
		Unattested:  false,
		Development: dev,
		CreatedAt:   now,
	}
	if err := v.Store.PutDevice(rec); err != nil {
		return nil, err
	}
	return rec, nil
}

// RegisterUnattested registers a Simulator device when AllowUnattested is true.
func (v *Verifier) RegisterUnattested(clientDataRaw []byte) (*DeviceRecord, error) {
	if !v.AllowUnattested {
		return nil, errors.New("unattested tokens are disabled")
	}
	cd, err := parseClientData(clientDataRaw)
	if err != nil {
		return nil, err
	}
	now := v.Now()
	if err := v.Store.ConsumeChallenge(cd.Challenge, now); err != nil {
		return nil, err
	}
	rec := &DeviceRecord{
		KeyID:       unattestedKeyPrefix + cd.DeviceID,
		UserID:      cd.UserID,
		DeviceID:    cd.DeviceID,
		Counter:     0,
		Unattested:  true,
		Development: true,
		CreatedAt:   now,
	}
	if err := v.Store.PutDevice(rec); err != nil {
		return nil, err
	}
	return rec, nil
}

// VerifyAssertion checks a one-time challenge, action, and P-256 assertion signature,
// advances the stored counter, and returns the device record.
// When bodyToMatchPayload is non-empty, clientData is required to include a matching
// "payload" SHA-256 hex digest so the signed assertion cryptographically binds the HTTP body.
func (v *Verifier) VerifyAssertion(keyID, assertionB64 string, clientDataRaw, bodyToMatchPayload []byte, wantAction string) (*DeviceRecord, error) {
	acd, err := parseAssertionClientData(clientDataRaw, wantAction)
	if err != nil {
		return nil, err
	}
	if len(bodyToMatchPayload) > 0 {
		if acd.Payload == "" {
			return nil, errors.New("clientData payload digest is required")
		}
		wantSum := sha256.Sum256(bodyToMatchPayload)
		if !strings.EqualFold(acd.Payload, hex.EncodeToString(wantSum[:])) {
			return nil, errors.New("clientData payload digest does not match request metrics")
		}
	}
	now := v.Now()
	if err := v.Store.ConsumeChallenge(acd.Challenge, now); err != nil {
		return nil, err
	}
	v.verifyMu.Lock()
	defer v.verifyMu.Unlock()
	rec, err := v.Store.GetDevice(keyID)
	if err != nil {
		return nil, err
	}
	if rec == nil {
		return nil, errors.New("unknown key")
	}
	if rec.Unattested {
		if !v.AllowUnattested {
			return nil, errors.New("unattested tokens are disabled")
		}
		return rec, nil
	}
	if assertionB64 == "" {
		return nil, errors.New("assertionObject is required")
	}
	assertionBytes, err := decodeBase64(assertionB64)
	if err != nil {
		return nil, errors.New("assertionObject is not base64")
	}
	if len(assertionBytes) > maxAssertionBytes {
		return nil, errors.New("assertionObject too large")
	}
	clientHash := sha256.Sum256(clientDataRaw)
	newCounter, err := verifyAssertionObject(v.AppID, rec.PublicKey, assertionBytes, clientHash[:], rec.Counter)
	if err != nil {
		return nil, err
	}
	rec.Counter = newCounter
	if err := v.Store.PutDevice(rec); err != nil {
		return nil, err
	}
	return rec, nil
}

type cborAttestation struct {
	Fmt      string      `cbor:"fmt"`
	AttStmt  cborAttStmt `cbor:"attStmt"`
	AuthData []byte      `cbor:"authData"`
}

type cborAttStmt struct {
	X5C     [][]byte `cbor:"x5c"`
	Receipt []byte   `cbor:"receipt"`
}

type cborAssertion struct {
	AuthenticatorData []byte `cbor:"authenticatorData"`
	Signature         []byte `cbor:"signature"`
}

func (v *Verifier) verifyAttestationObject(keyID string, raw, clientHash []byte, now time.Time) ([]byte, bool, error) {
	var obj cborAttestation
	if err := cbor.Unmarshal(raw, &obj); err != nil {
		return nil, false, errors.New("attestationObject is not CBOR")
	}
	if obj.Fmt != "apple-appattest" {
		return nil, false, errors.New("fmt must be apple-appattest")
	}
	if len(obj.AttStmt.X5C) == 0 {
		return nil, false, errors.New("x5c is empty")
	}

	certs := make([]*x509.Certificate, 0, len(obj.AttStmt.X5C))
	for _, der := range obj.AttStmt.X5C {
		c, err := x509.ParseCertificate(der)
		if err != nil {
			return nil, false, errors.New("x5c certificate is not valid DER")
		}
		if now.Before(c.NotBefore) || now.After(c.NotAfter) {
			return nil, false, errors.New("certificate is not valid at this time")
		}
		certs = append(certs, c)
	}
	for i := 0; i+1 < len(certs); i++ {
		if err := verifyCertSignedBy(certs[i], certs[i+1]); err != nil {
			return nil, false, errors.New("x5c chain signature invalid")
		}
	}
	last := certs[len(certs)-1]
	anchored := false
	for _, root := range v.Roots {
		if now.Before(root.NotBefore) || now.After(root.NotAfter) {
			continue
		}
		if verifyCertSignedBy(last, root) == nil || bytes.Equal(last.RawTBSCertificate, root.RawTBSCertificate) {
			anchored = true
			break
		}
	}
	if !anchored {
		return nil, false, errors.New("chain does not anchor at a trusted root")
	}

	leaf := certs[0]
	ecPub, ok := leaf.PublicKey.(*ecdsa.PublicKey)
	if !ok || ecPub.Curve != elliptic.P256() {
		return nil, false, errors.New("leaf public key is not P-256")
	}
	uncompressed, err := ecdsaUncompressedBytes(ecPub)
	if err != nil {
		return nil, false, err
	}

	nonce, err := extractNonce(leaf)
	if err != nil {
		return nil, false, err
	}
	composite := make([]byte, 0, len(obj.AuthData)+len(clientHash))
	composite = append(composite, obj.AuthData...)
	composite = append(composite, clientHash...)
	wantNonce := sha256.Sum256(composite)
	if !bytes.Equal(nonce, wantNonce[:]) {
		return nil, false, errors.New("certificate nonce does not match clientData")
	}

	wantKeyID := sha256.Sum256(uncompressed)
	gotKeyID, err := decodeBase64(keyID)
	if err != nil || !bytes.Equal(gotKeyID, wantKeyID[:]) {
		return nil, false, errors.New("keyId does not match credCert public key")
	}

	dev, err := checkAttestAuthData(obj.AuthData, v.AppID, gotKeyID)
	if err != nil {
		return nil, false, err
	}
	return uncompressed, dev, nil
}

// verifyCertSignedBy verifies child's signature using issuer's ECDSA public key.
// Apple's credCert leaf uses ecdsa-with-SHA256 while Apple App Attestation CA 1G
// has a P-384 key; verifyCertSignedBy supports both P-256 and P-384 with SHA-256 or SHA-384
// and enforces CA basic constraints on non-leaf issuers.
func verifyCertSignedBy(child, issuer *x509.Certificate) error {
	if !bytes.Equal(child.RawTBSCertificate, issuer.RawTBSCertificate) && (!issuer.BasicConstraintsValid || !issuer.IsCA) {
		return errors.New("issuer certificate is not a CA")
	}
	if err := child.CheckSignatureFrom(issuer); err == nil {
		return nil
	}
	pub, ok := issuer.PublicKey.(*ecdsa.PublicKey)
	if !ok {
		return errors.New("issuer public key is not ECDSA")
	}
	var sigAlgOID asn1.ObjectIdentifier
	var seq struct {
		TBS []byte
		Alg struct {
			OID asn1.ObjectIdentifier
		}
	}
	if _, err := asn1.Unmarshal(child.Raw, &seq); err == nil {
		sigAlgOID = seq.Alg.OID
	}
	var digest []byte
	switch {
	case sigAlgOID.Equal(oidECDSASHA256) || child.SignatureAlgorithm == x509.ECDSAWithSHA256:
		sum := sha256.Sum256(child.RawTBSCertificate)
		digest = sum[:]
	case sigAlgOID.Equal(oidECDSASHA384) || child.SignatureAlgorithm == x509.ECDSAWithSHA384:
		sum := sha512.Sum384(child.RawTBSCertificate)
		digest = sum[:]
	default:
		return errors.New("unsupported certificate signature algorithm")
	}
	if !ecdsa.VerifyASN1(pub, digest, child.Signature) {
		return errors.New("certificate ECDSA signature invalid")
	}
	return nil
}

func checkAttestAuthData(authData []byte, appID string, keyIDRaw []byte) (bool, error) {
	if len(authData) < 55 {
		return false, errors.New("authenticatorData too short")
	}
	wantRP := sha256.Sum256([]byte(appID))
	if !bytes.Equal(authData[:32], wantRP[:]) {
		return false, errors.New("rpIdHash does not match APP_ID")
	}
	if authData[32]&flagAT == 0 {
		return false, errors.New("attested credential data missing")
	}
	counter := binary.BigEndian.Uint32(authData[33:37])
	if counter != 0 {
		return false, errors.New("attestation counter must be 0")
	}
	aaguid := authData[37:53]
	isProd := bytes.Equal(aaguid, aaguidProduction)
	isDev := bytes.Equal(aaguid, aaguidDevelopment)
	if !isProd && !isDev {
		return false, errors.New("unexpected aaguid")
	}
	credLen := int(binary.BigEndian.Uint16(authData[53:55]))
	if len(authData) < 55+credLen {
		return false, errors.New("credential id truncated")
	}
	if !bytes.Equal(authData[55:55+credLen], keyIDRaw) {
		return false, errors.New("credential id does not match keyId")
	}
	return isDev, nil
}

func verifyAssertionObject(appID string, pubKeyBytes, assertionRaw, clientHash []byte, prevCounter uint32) (uint32, error) {
	var obj cborAssertion
	if err := cbor.Unmarshal(assertionRaw, &obj); err != nil {
		return 0, errors.New("assertionObject is not CBOR")
	}
	if len(obj.AuthenticatorData) < 37 {
		return 0, errors.New("authenticatorData too short")
	}
	if len(obj.Signature) == 0 {
		return 0, errors.New("signature missing")
	}
	wantRP := sha256.Sum256([]byte(appID))
	if !bytes.Equal(obj.AuthenticatorData[:32], wantRP[:]) {
		return 0, errors.New("rpIdHash does not match APP_ID")
	}
	counter := binary.BigEndian.Uint32(obj.AuthenticatorData[33:37])
	if counter <= prevCounter {
		return 0, errors.New("counter must increase")
	}
	pub, err := parseP256Uncompressed(pubKeyBytes)
	if err != nil {
		return 0, err
	}
	nonceInput := make([]byte, 0, len(obj.AuthenticatorData)+len(clientHash))
	nonceInput = append(nonceInput, obj.AuthenticatorData...)
	nonceInput = append(nonceInput, clientHash...)
	digest := sha256.Sum256(nonceInput)
	if !ecdsa.VerifyASN1(pub, digest[:], obj.Signature) {
		return 0, errors.New("invalid assertion signature")
	}
	return counter, nil
}

func ecdsaUncompressedBytes(pub *ecdsa.PublicKey) ([]byte, error) {
	ecdhKey, err := pub.ECDH()
	if err != nil {
		return nil, err
	}
	return ecdhKey.Bytes(), nil
}

func parseP256Uncompressed(raw []byte) (*ecdsa.PublicKey, error) {
	// ecdsa.ParseUncompressedPublicKey is standard in Go 1.25+, or use elliptic/x509.
	// Using x509 PKIX wrapping or crypto/ecdh ensures zero deprecated calls.
	if len(raw) != 65 || raw[0] != 0x04 {
		return nil, errors.New("invalid P-256 uncompressed key")
	}
	// ASN.1 SPKI header for P-256 uncompressed public key (26 bytes) + 65 bytes = 91 bytes.
	spkiPrefix := []byte{
		0x30, 0x59, 0x30, 0x13, 0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01,
		0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07, 0x03, 0x42, 0x00,
	}
	spki := append(spkiPrefix, raw...)
	parsed, err := x509.ParsePKIXPublicKey(spki)
	if err != nil {
		return nil, err
	}
	ecPub, ok := parsed.(*ecdsa.PublicKey)
	if !ok {
		return nil, errors.New("not an ECDSA public key")
	}
	return ecPub, nil
}

func extractNonce(leaf *x509.Certificate) ([]byte, error) {
	for _, ext := range leaf.Extensions {
		if ext.Id.Equal(nonceOID) {
			if b := find32ByteOctetString(ext.Value); len(b) == 32 {
				return b, nil
			}
			return nil, errors.New("nonce extension missing 32-byte value")
		}
	}
	return nil, errors.New("nonce extension missing")
}

func find32ByteOctetString(der []byte) []byte {
	var raw asn1.RawValue
	rest, err := asn1.Unmarshal(der, &raw)
	if err != nil {
		return nil
	}
	if raw.Class == asn1.ClassUniversal && raw.Tag == asn1.TagOctetString && len(raw.Bytes) == 32 {
		return raw.Bytes
	}
	if len(raw.Bytes) == 32 && !raw.IsCompound {
		return raw.Bytes
	}
	if len(raw.Bytes) > 0 {
		if found := find32ByteOctetString(raw.Bytes); found != nil {
			return found
		}
	}
	if len(rest) > 0 {
		return find32ByteOctetString(rest)
	}
	return nil
}

func decodeBase64(s string) ([]byte, error) {
	trimmed := strings.TrimSpace(s)
	for _, enc := range []*base64.Encoding{
		base64.StdEncoding,
		base64.RawStdEncoding,
		base64.URLEncoding,
		base64.RawURLEncoding,
	} {
		if b, err := enc.DecodeString(trimmed); err == nil {
			return b, nil
		}
	}
	return nil, errors.New("invalid base64")
}
