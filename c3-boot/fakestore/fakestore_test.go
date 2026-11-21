package main

import (
	"bytes"
	"crypto/ed25519"
	"crypto/rand"
	"crypto/sha256"
	"crypto/x509"
	"encoding/asn1"
	"encoding/base64"
	"encoding/binary"
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"slices"
	"strings"
	"testing"
	"time"

	"github.com/digitorus/pkcs7"
	"github.com/digitorus/timestamp"
	protobundle "github.com/sigstore/protobuf-specs/gen/pb-go/bundle/v1"
	protocommon "github.com/sigstore/protobuf-specs/gen/pb-go/common/v1"
	prototrustroot "github.com/sigstore/protobuf-specs/gen/pb-go/trustroot/v1"
	rekortilespb "github.com/sigstore/rekor-tiles/v2/pkg/generated/protobuf"
	"github.com/sigstore/rekor-tiles/v2/pkg/types/hashedrekord"
	"github.com/transparency-dev/merkle/compact"
	"github.com/transparency-dev/merkle/proof"
	"github.com/transparency-dev/merkle/rfc6962"
	"golang.org/x/mod/sumdb/note"
	"google.golang.org/protobuf/encoding/protojson"
)

const conformanceDir = "../testdata/conformance"

// cli runs the fakestore command line and fails the test unless it exits
// with code want. It returns standard output and standard error.
func cli(t *testing.T, want int, args ...string) (string, string) {
	t.Helper()
	var stdout, stderr bytes.Buffer
	if got := run(args, &stdout, &stderr); got != want {
		t.Fatalf("fakestore %s: exit %d, want %d\nstdout: %s\nstderr: %s", strings.Join(args, " "), got, want, stdout.String(), stderr.String())
	}
	return stdout.String(), stderr.String()
}

type fixture struct {
	dir, artifact, bundle string
}

func (f fixture) trustedRoot() string { return filepath.Join(f.dir, trustedRootFile) }

// newFixture runs init into a temporary directory and signs a random
// artifact with extra sign flags.
func newFixture(t *testing.T, signArgs ...string) fixture {
	t.Helper()
	tmp := t.TempDir()
	f := fixture{
		dir:      filepath.Join(tmp, "instance"),
		artifact: filepath.Join(tmp, "artifact.bin"),
		bundle:   filepath.Join(tmp, "bundle.json"),
	}
	data := make([]byte, 4096)
	if _, err := rand.Read(data); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(f.artifact, data, 0o644); err != nil {
		t.Fatal(err)
	}
	cli(t, 0, "init", "-dir", f.dir)
	cli(t, 0, append([]string{"sign", "-dir", f.dir, "-artifact", f.artifact, "-out", f.bundle}, signArgs...)...)
	return f
}

func loadBundle(t *testing.T, path string) *protobundle.Bundle {
	t.Helper()
	data, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	var b protobundle.Bundle
	if err := protojson.Unmarshal(data, &b); err != nil {
		t.Fatal(err)
	}
	return &b
}

func writeBundle(t *testing.T, b *protobundle.Bundle) string {
	t.Helper()
	data, err := protojson.Marshal(b)
	if err != nil {
		t.Fatal(err)
	}
	path := filepath.Join(t.TempDir(), "tampered.json")
	if err := os.WriteFile(path, data, 0o644); err != nil {
		t.Fatal(err)
	}
	return path
}

func TestSignVerify(t *testing.T) {
	for _, tc := range []struct {
		name string
		args []string
	}{
		{"defaults", nil},
		{"past time", []string{"-time", "2025-06-12T12:02:20Z"}},
		{"one leaf", []string{"-tree-size", "1"}},
		{"conformance tree shape", []string{"-tree-size", "736", "-leaf-index", "735"}},
		{"first of many", []string{"-tree-size", "1000", "-leaf-index", "0"}},
		{"middle", []string{"-tree-size", "13", "-leaf-index", "6"}},
		{
			"other identity",
			[]string{
				"-issuer", "https://token.actions.example.com",
				"-build-signer-uri", "https://github.com/example/firmware/.github/workflows/release.yaml@refs/tags/v1.2.3",
				"-repository-id", "42", "-owner-id", "43", "-trigger", "workflow_dispatch",
				"-commit", "0123456789abcdef0123456789abcdef01234567",
			},
		},
	} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t, tc.args...)
			issuer, san := defaultIssuer, defaultBuildSignerURI
			for i := 0; i+1 < len(tc.args); i++ {
				switch tc.args[i] {
				case "-issuer":
					issuer = tc.args[i+1]
				case "-build-signer-uri":
					san = tc.args[i+1]
				}
			}
			out, _ := cli(t, 0, "verify", "-trusted-root", f.trustedRoot(), "-bundle", f.bundle, "-artifact", f.artifact, "-issuer", issuer, "-build-signer-uri", san)
			if out != "OK\n" {
				t.Errorf("verify printed %q, want %q", out, "OK\n")
			}
		})
	}
}

func TestVerifyRejects(t *testing.T) {
	f := newFixture(t)
	other := newFixture(t)

	wrongArtifact := filepath.Join(t.TempDir(), "wrong.bin")
	data, err := os.ReadFile(f.artifact)
	if err != nil {
		t.Fatal(err)
	}
	data[0] ^= 1
	if err := os.WriteFile(wrongArtifact, data, 0o644); err != nil {
		t.Fatal(err)
	}

	// Flip a bit in the last byte of s, which keeps the DER valid, so
	// rejection comes from the signature check rather than from parsing.
	b := loadBundle(t, f.bundle)
	b.GetMessageSignature().Signature[len(b.GetMessageSignature().GetSignature())-1] ^= 1
	badSignature := writeBundle(t, b)

	b = loadBundle(t, f.bundle)
	proofPB := b.GetVerificationMaterial().GetTlogEntries()[0].GetInclusionProof()
	lines := strings.Split(proofPB.GetCheckpoint().GetEnvelope(), "\n")
	root, err := base64.StdEncoding.DecodeString(lines[2])
	if err != nil {
		t.Fatal(err)
	}
	root[0] ^= 1
	lines[2] = base64.StdEncoding.EncodeToString(root)
	proofPB.Checkpoint.Envelope = strings.Join(lines, "\n")
	proofPB.RootHash = root
	badCheckpointRoot := writeBundle(t, b)

	for _, tc := range []struct {
		name                          string
		trustedRoot, bundle, artifact string
		issuer, san                   string
		wantErr                       string
	}{
		{"wrong artifact", f.trustedRoot(), f.bundle, wrongArtifact, defaultIssuer, defaultBuildSignerURI, "verifying bundle"},
		{"tampered signature", f.trustedRoot(), badSignature, f.artifact, defaultIssuer, defaultBuildSignerURI, "verifying bundle"},
		{"tampered checkpoint root", f.trustedRoot(), badCheckpointRoot, f.artifact, defaultIssuer, defaultBuildSignerURI, "checkpoint"},
		{"trusted root from another init", other.trustedRoot(), f.bundle, f.artifact, defaultIssuer, defaultBuildSignerURI, "verifying bundle"},
		{"wrong issuer", f.trustedRoot(), f.bundle, f.artifact, "https://accounts.example.com", defaultBuildSignerURI, "issuer"},
		{"wrong SAN", f.trustedRoot(), f.bundle, f.artifact, defaultIssuer, defaultBuildSignerURI + "x", "SAN"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			_, stderr := cli(t, 1, "verify", "-trusted-root", tc.trustedRoot, "-bundle", tc.bundle, "-artifact", tc.artifact, "-issuer", tc.issuer, "-build-signer-uri", tc.san)
			t.Logf("verify: %s", stderr)
			if !strings.Contains(stderr, tc.wantErr) {
				t.Errorf("verify error %q doesn't contain %q", stderr, tc.wantErr)
			}
		})
	}
}

// TestVerifyConformanceBundle checks that the verify command's policy
// accepts a real Rekor v2 bundle from Sigstore staging.
func TestVerifyConformanceBundle(t *testing.T) {
	dir := filepath.Join(conformanceDir, "rekor2-happy-path")
	cli(t, 0, "verify",
		"-trusted-root", filepath.Join(dir, "trusted_root.json"),
		"-bundle", filepath.Join(dir, "bundle.sigstore.json"),
		"-artifact", filepath.Join(conformanceDir, "a.txt"),
		"-build-signer-uri", "https://github.com/sigstore-conformance/extremely-dangerous-public-oidc-beacon/.github/workflows/extremely-dangerous-oidc-beacon.yml@refs/heads/main",
	)
}

// TestRekorV2LogIDMatchesStaging checks the log ID derivation against
// Sigstore staging's Rekor v2 log in the conformance trusted root.
func TestRekorV2LogIDMatchesStaging(t *testing.T) {
	data, err := os.ReadFile(filepath.Join(conformanceDir, "rekor2-happy-path", "trusted_root.json"))
	if err != nil {
		t.Fatal(err)
	}
	var tr prototrustroot.TrustedRoot
	if err := protojson.Unmarshal(data, &tr); err != nil {
		t.Fatal(err)
	}
	found := false
	for _, tl := range tr.GetTlogs() {
		if tl.GetPublicKey().GetKeyDetails() != protocommon.PublicKeyDetails_PKIX_ED25519 {
			continue
		}
		found = true
		pub, err := x509.ParsePKIXPublicKey(tl.GetPublicKey().GetRawBytes())
		if err != nil {
			t.Fatal(err)
		}
		origin := strings.TrimPrefix(tl.GetBaseUrl(), "https://")
		if got, want := rekorV2LogID(origin, pub.(ed25519.PublicKey)), tl.GetLogId().GetKeyId(); !bytes.Equal(got, want) {
			t.Errorf("rekorV2LogID(%q) = %x, want %x", origin, got, want)
		}
	}
	if !found {
		t.Fatal("no Ed25519 log in the conformance trusted root")
	}
}

// TestEntryBody checks that canonicalizedBody is the entry that rekor-tiles
// reconstructs and that its leaf is the one the inclusion proof proves, so a
// verifier that hashes the body, like the c3-boot bootloader, and one that
// rebuilds it, like sigstore-go, agree.
func TestEntryBody(t *testing.T) {
	f := newFixture(t, "-tree-size", "37", "-leaf-index", "20")
	b := loadBundle(t, f.bundle)
	entry := b.GetVerificationMaterial().GetTlogEntries()[0]
	body := entry.GetCanonicalizedBody()

	want, err := hashedrekord.ToEntryHash(b.GetMessageSignature().GetMessageDigest().GetDigest(), &rekortilespb.Signature{
		Content: b.GetMessageSignature().GetSignature(),
		Verifier: &rekortilespb.Verifier{
			Verifier:   &rekortilespb.Verifier_X509Certificate{X509Certificate: &protocommon.X509Certificate{RawBytes: b.GetVerificationMaterial().GetCertificate().GetRawBytes()}},
			KeyDetails: protocommon.PublicKeyDetails_PKIX_ECDSA_P256_SHA_256,
		},
	})
	if err != nil {
		t.Fatal(err)
	}
	if got := rfc6962.DefaultHasher.HashLeaf(body); !bytes.Equal(got, want) {
		t.Errorf("leaf hash of canonicalizedBody = %x, rekor-tiles reconstructs %x\nbody: %s", got, want, body)
	}

	var parsed rekortilespb.Entry
	if err := protojson.Unmarshal(body, &parsed); err != nil {
		t.Fatalf("canonicalizedBody isn't a Rekor v2 entry: %v", err)
	}

	ip := entry.GetInclusionProof()
	if err := proof.VerifyInclusion(rfc6962.DefaultHasher, uint64(entry.GetLogIndex()), uint64(ip.GetTreeSize()), rfc6962.DefaultHasher.HashLeaf(body), ip.GetHashes(), ip.GetRootHash()); err != nil {
		t.Errorf("inclusion proof: %v", err)
	}
	if entry.GetLogIndex() != 20 || ip.GetLogIndex() != 20 || ip.GetTreeSize() != 37 {
		t.Errorf("logIndex %d, proof logIndex %d, treeSize %d; want 20, 20, 37", entry.GetLogIndex(), ip.GetLogIndex(), ip.GetTreeSize())
	}
}

func TestCheckpoint(t *testing.T) {
	f := newFixture(t, "-tree-size", "9")
	b := loadBundle(t, f.bundle)
	ip := b.GetVerificationMaterial().GetTlogEntries()[0].GetInclusionProof()
	env := ip.GetCheckpoint().GetEnvelope()

	logKey, err := readEd25519Key(filepath.Join(f.dir, logKeyFile))
	if err != nil {
		t.Fatal(err)
	}
	pub := logKey.Public().(ed25519.PublicKey)
	vkey := fmt.Sprintf("%s+%x+%s", defaultOrigin, rekorV2LogID(defaultOrigin, pub)[:4], base64.StdEncoding.EncodeToString(append([]byte{0x01}, pub...)))
	v, err := note.NewVerifier(vkey)
	if err != nil {
		t.Fatal(err)
	}
	n, err := note.Open([]byte(env), note.VerifierList(v))
	if err != nil {
		t.Fatalf("opening checkpoint: %v", err)
	}
	want := defaultOrigin + "\n9\n" + base64.StdEncoding.EncodeToString(ip.GetRootHash()) + "\n"
	if n.Text != want {
		t.Errorf("checkpoint text %q, want %q", n.Text, want)
	}
	sigLine := strings.TrimPrefix(strings.TrimSuffix(env[len(want)+1:], "\n"), "— "+defaultOrigin+" ")
	sig, err := base64.StdEncoding.DecodeString(sigLine)
	if err != nil {
		t.Fatalf("signature line %q: %v", sigLine, err)
	}
	if len(sig) != 68 || !bytes.Equal(sig[:4], rekorV2LogID(defaultOrigin, pub)[:4]) || !ed25519.Verify(pub, []byte(want), sig[4:]) {
		t.Errorf("signature line %q isn't a key ID and an Ed25519 signature over the note text", sigLine)
	}
}

func TestTree(t *testing.T) {
	for size := uint64(1); size <= 70; size++ {
		tr := tree{size: size, leaf: func(i uint64) []byte {
			var b [8]byte
			binary.BigEndian.PutUint64(b[:], i)
			return hashLeaf(b[:])
		}}
		cr := (&compact.RangeFactory{Hash: rfc6962.DefaultHasher.HashChildren}).NewEmptyRange(0)
		for i := uint64(0); i < size; i++ {
			if err := cr.Append(tr.leaf(i), nil); err != nil {
				t.Fatal(err)
			}
		}
		want, err := cr.GetRootHash(nil)
		if err != nil {
			t.Fatal(err)
		}
		root := tr.root()
		if !bytes.Equal(root, want) {
			t.Fatalf("size %d: root %x, want %x", size, root, want)
		}
		for m := uint64(0); m < size; m++ {
			if err := proof.VerifyInclusion(rfc6962.DefaultHasher, m, size, tr.leaf(m), tr.inclusionProof(m), root); err != nil {
				t.Fatalf("size %d, index %d: %v", size, m, err)
			}
		}
	}
}

type extShape struct {
	oid      string
	critical bool
	utf8     bool
}

func extShapes(t *testing.T, cert *x509.Certificate) []extShape {
	t.Helper()
	var shapes []extShape
	for _, e := range cert.Extensions {
		var raw asn1.RawValue
		rest, err := asn1.Unmarshal(e.Value, &raw)
		utf8 := err == nil && len(rest) == 0 && raw.Class == asn1.ClassUniversal && raw.Tag == asn1.TagUTF8String
		shapes = append(shapes, extShape{e.Id.String(), e.Critical, utf8})
	}
	return shapes
}

// TestLeafCertificateProfile compares the leaf certificate with the one in
// the real conformance bundle: the same extensions in the same order with
// the same criticality and encodings, and the same algorithms, issuer, and
// validity length.
func TestLeafCertificateProfile(t *testing.T) {
	realBundle := loadBundle(t, filepath.Join(conformanceDir, "rekor2-happy-path", "bundle.sigstore.json"))
	real, err := x509.ParseCertificate(realBundle.GetVerificationMaterial().GetCertificate().GetRawBytes())
	if err != nil {
		t.Fatal(err)
	}
	f := newFixture(t, "-time", "2026-03-04T05:06:07Z")
	fake, err := x509.ParseCertificate(loadBundle(t, f.bundle).GetVerificationMaterial().GetCertificate().GetRawBytes())
	if err != nil {
		t.Fatal(err)
	}

	if got, want := extShapes(t, fake), extShapes(t, real); !slices.Equal(got, want) {
		t.Errorf("extensions differ\n got: %v\nwant: %v", got, want)
	}
	if !bytes.Equal(fake.RawIssuer, real.RawIssuer) {
		t.Errorf("issuer %q, want %q", fake.Issuer, real.Issuer)
	}
	if !bytes.Equal(fake.RawSubject, real.RawSubject) {
		t.Errorf("subject %x, want %x", fake.RawSubject, real.RawSubject)
	}
	if fake.SignatureAlgorithm != real.SignatureAlgorithm || fake.PublicKeyAlgorithm != real.PublicKeyAlgorithm {
		t.Errorf("algorithms %v/%v, want %v/%v", fake.SignatureAlgorithm, fake.PublicKeyAlgorithm, real.SignatureAlgorithm, real.PublicKeyAlgorithm)
	}
	if got, want := fake.NotAfter.Sub(fake.NotBefore), real.NotAfter.Sub(real.NotBefore); got != want {
		t.Errorf("validity %v, want %v", got, want)
	}
	if want := time.Date(2026, 3, 4, 5, 5, 7, 0, time.UTC); !fake.NotBefore.Equal(want) {
		t.Errorf("notBefore %v, want %v", fake.NotBefore, want)
	}
	if len(fake.SerialNumber.Bytes()) > 20 || fake.SerialNumber.Sign() <= 0 {
		t.Errorf("serial %x isn't positive and at most 20 bytes", fake.SerialNumber)
	}
}

// TestTimestampProfile compares the timestamp with the one in the real
// conformance bundle.
func TestTimestampProfile(t *testing.T) {
	realBundle := loadBundle(t, filepath.Join(conformanceDir, "rekor2-happy-path", "bundle.sigstore.json"))
	realTS := realBundle.GetVerificationMaterial().GetTimestampVerificationData().GetRfc3161Timestamps()[0].GetSignedTimestamp()
	at := time.Date(2026, 3, 4, 5, 6, 7, 0, time.UTC)
	f := newFixture(t, "-time", at.Format(time.RFC3339))
	b := loadBundle(t, f.bundle)
	fakeTS := b.GetVerificationMaterial().GetTimestampVerificationData().GetRfc3161Timestamps()[0].GetSignedTimestamp()

	ts, err := timestamp.ParseResponse(fakeTS)
	if err != nil {
		t.Fatal(err)
	}
	digest := sha256.Sum256(b.GetMessageSignature().GetSignature())
	if !ts.Time.Equal(at) || !bytes.Equal(ts.HashedMessage, digest[:]) || !ts.Policy.Equal(oidTSAPolicy) {
		t.Errorf("genTime %v, imprint %x, policy %v; want %v, %x, %v", ts.Time, ts.HashedMessage, ts.Policy, at, digest, oidTSAPolicy)
	}

	type shape struct {
		certs          int
		signerVersion  int
		signedAttrs    []string
		signatureAlg   string
		tstHasNonce    bool
		tstHasAccuracy bool
	}
	shapeOf := func(resp []byte) (shape, time.Time) {
		t.Helper()
		ts, err := timestamp.ParseResponse(resp)
		if err != nil {
			t.Fatal(err)
		}
		p7, err := pkcs7.Parse(ts.RawToken)
		if err != nil {
			t.Fatal(err)
		}
		s := p7.Signers[0]
		var attrs []string
		var signingTime time.Time
		for _, a := range s.AuthenticatedAttributes {
			attrs = append(attrs, a.Type.String())
			if a.Type.Equal(pkcs7.OIDAttributeSigningTime) {
				if _, err := asn1.Unmarshal(a.Value.Bytes, &signingTime); err != nil {
					t.Fatal(err)
				}
			}
		}
		return shape{
			certs:          len(p7.Certificates),
			signerVersion:  s.Version,
			signedAttrs:    attrs,
			signatureAlg:   s.DigestEncryptionAlgorithm.Algorithm.String(),
			tstHasNonce:    ts.Nonce != nil,
			tstHasAccuracy: ts.Accuracy != 0,
		}, signingTime
	}
	got, signingTime := shapeOf(fakeTS)
	want, _ := shapeOf(realTS)
	if !reflect.DeepEqual(got, want) {
		t.Errorf("timestamp shape differs\n got: %+v\nwant: %+v", got, want)
	}
	if !signingTime.Equal(at) {
		t.Errorf("signingTime %v, want %v", signingTime, at)
	}
}
