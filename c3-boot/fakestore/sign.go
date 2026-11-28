package main

import (
	"crypto"
	"crypto/ecdsa"
	"crypto/ed25519"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/sha256"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/asn1"
	"encoding/base64"
	"encoding/binary"
	"encoding/hex"
	"errors"
	"flag"
	"fmt"
	"io"
	"math/big"
	"net/url"
	"os"
	"path"
	"path/filepath"
	"strconv"
	"strings"
	"time"

	"github.com/digitorus/pkcs7"
	"github.com/digitorus/timestamp"
	ct "github.com/google/certificate-transparency-go"
	cttls "github.com/google/certificate-transparency-go/tls"
	ctx509 "github.com/google/certificate-transparency-go/x509"
	protobundle "github.com/sigstore/protobuf-specs/gen/pb-go/bundle/v1"
	protocommon "github.com/sigstore/protobuf-specs/gen/pb-go/common/v1"
	protorekor "github.com/sigstore/protobuf-specs/gen/pb-go/rekor/v1"
	prototrustroot "github.com/sigstore/protobuf-specs/gen/pb-go/trustroot/v1"
	"golang.org/x/mod/sumdb/note"
	"google.golang.org/protobuf/encoding/protojson"
)

const (
	bundleMediaType       = "application/vnd.dev.sigstore.bundle.v0.3+json"
	defaultIssuer         = "https://token.actions.githubusercontent.com"
	defaultBuildSignerURI = "https://github.com/imjasonh/playground/.github/workflows/c3-release.yml@refs/heads/main"
)

var (
	oidCTPoison  = asn1.ObjectIdentifier{1, 3, 6, 1, 4, 1, 11129, 2, 4, 3}
	oidCTSCTList = asn1.ObjectIdentifier{1, 3, 6, 1, 4, 1, 11129, 2, 4, 2}

	// The Sigstore TSA policy, which Sigstore's timestamp-authority puts in
	// every TSTInfo it signs with an ECDSA key.
	oidTSAPolicy = asn1.ObjectIdentifier{1, 3, 6, 1, 4, 1, 57264, 2}

	oidSigningCertificateV2 = asn1.ObjectIdentifier{1, 2, 840, 113549, 1, 9, 16, 2, 47}
	oidTSTInfo              = asn1.ObjectIdentifier{1, 2, 840, 113549, 1, 9, 16, 1, 4}
)

// fulcioOID returns the OID of Fulcio certificate extension 1.3.6.1.4.1.57264.1.n.
func fulcioOID(n int) asn1.ObjectIdentifier {
	return asn1.ObjectIdentifier{1, 3, 6, 1, 4, 1, 57264, 1, n}
}

// githubIdentity holds the claims that Fulcio copies from a GitHub Actions
// OIDC token into the leaf certificate.
type githubIdentity struct {
	issuer         string
	buildSignerURI string
	repositoryID   uint64
	ownerID        uint64
	trigger        string
	commit         string
}

type signParams struct {
	identity  githubIdentity
	time      time.Time
	treeSize  uint64
	leafIndex uint64
}

func runSign(args []string, stderr io.Writer) error {
	fs := flag.NewFlagSet("sign", flag.ContinueOnError)
	fs.SetOutput(stderr)
	dir := fs.String("dir", "", "directory that init wrote (required)")
	artifact := fs.String("artifact", "", "file to sign (required)")
	out := fs.String("out", "", "path to write the bundle JSON to (required)")
	issuer := fs.String("issuer", defaultIssuer, "OIDC issuer, for extensions 1.3.6.1.4.1.57264.1.1 and .1.8")
	buildSignerURI := fs.String("build-signer-uri", defaultBuildSignerURI, "workflow identity, https://github.com/OWNER/REPO/PATH@REF, for the SAN URI and extension .1.9")
	repositoryID := fs.Uint64("repository-id", 1234, "source repository ID, for extension .1.15")
	ownerID := fs.Uint64("owner-id", 5678, "source repository owner ID, for extension .1.17")
	trigger := fs.String("trigger", "push", "workflow trigger event, for extensions .1.2 and .1.20")
	commit := fs.String("commit", "", "40-digit hex commit SHA for the digest extensions (default random)")
	at := fs.String("time", "", "signing time, RFC 3339 (default now); the TSA time and the middle of the leaf validity")
	treeSize := fs.Uint64("tree-size", 8, "size of the log tree that the checkpoint signs")
	leafIndex := fs.Int64("leaf-index", -1, "log index of the entry (default tree-size minus 1)")
	if err := fs.Parse(args); err != nil {
		return err
	}
	if fs.NArg() != 0 {
		return fmt.Errorf("sign: unexpected arguments %q", fs.Args())
	}
	if *dir == "" || *artifact == "" || *out == "" {
		return errors.New("sign: -dir, -artifact, and -out are required")
	}

	p := signParams{
		identity: githubIdentity{
			issuer:         *issuer,
			buildSignerURI: *buildSignerURI,
			repositoryID:   *repositoryID,
			ownerID:        *ownerID,
			trigger:        *trigger,
			commit:         *commit,
		},
		time:     time.Now(),
		treeSize: *treeSize,
	}
	if *at != "" {
		t, err := time.Parse(time.RFC3339, *at)
		if err != nil {
			return fmt.Errorf("sign: -time: %w", err)
		}
		p.time = t
	}
	if p.treeSize == 0 {
		return errors.New("sign: -tree-size must be at least 1")
	}
	switch {
	case *leafIndex == -1:
		p.leafIndex = p.treeSize - 1
	case *leafIndex < 0 || uint64(*leafIndex) >= p.treeSize:
		return fmt.Errorf("sign: -leaf-index %d is outside a tree of size %d", *leafIndex, p.treeSize)
	default:
		p.leafIndex = uint64(*leafIndex)
	}

	data, err := os.ReadFile(*artifact)
	if err != nil {
		return err
	}
	b, err := signArtifact(*dir, data, p)
	if err != nil {
		return err
	}
	return os.WriteFile(*out, append(b, '\n'), 0o644)
}

// instance holds the keys and certificates that init wrote.
type instance struct {
	origin          string
	intermediate    *x509.Certificate
	intermediateKey *ecdsa.PrivateKey
	tsaLeaf         *x509.Certificate
	tsaKey          *ecdsa.PrivateKey
	logKey          ed25519.PrivateKey
	ctLogKey        *ecdsa.PrivateKey
}

func loadInstance(dir string) (*instance, error) {
	var in instance
	var err error
	if in.intermediate, err = readCert(filepath.Join(dir, fulcioIntermediateCertFile)); err != nil {
		return nil, err
	}
	if in.intermediateKey, err = readECDSAKey(filepath.Join(dir, fulcioIntermediateKeyFile)); err != nil {
		return nil, err
	}
	if in.tsaLeaf, err = readCert(filepath.Join(dir, tsaLeafCertFile)); err != nil {
		return nil, err
	}
	if in.tsaKey, err = readECDSAKey(filepath.Join(dir, tsaLeafKeyFile)); err != nil {
		return nil, err
	}
	if in.logKey, err = readEd25519Key(filepath.Join(dir, logKeyFile)); err != nil {
		return nil, err
	}
	if in.ctLogKey, err = readECDSAKey(filepath.Join(dir, ctLogKeyFile)); err != nil {
		return nil, err
	}

	// The origin lives only in trusted_root.json, as the host of the log's
	// baseUrl, which is where sigstore-go reads it from.
	trJSON, err := os.ReadFile(filepath.Join(dir, trustedRootFile))
	if err != nil {
		return nil, err
	}
	var tr prototrustroot.TrustedRoot
	if err := protojson.Unmarshal(trJSON, &tr); err != nil {
		return nil, fmt.Errorf("%s: %w", trustedRootFile, err)
	}
	if len(tr.GetTlogs()) != 1 {
		return nil, fmt.Errorf("%s: want 1 tlog, got %d", trustedRootFile, len(tr.GetTlogs()))
	}
	u, err := url.Parse(tr.GetTlogs()[0].GetBaseUrl())
	if err != nil {
		return nil, fmt.Errorf("%s: %w", trustedRootFile, err)
	}
	in.origin = u.Hostname()
	return &in, nil
}

// signArtifact returns the JSON of a Sigstore bundle for data.
func signArtifact(dir string, data []byte, p signParams) ([]byte, error) {
	in, err := loadInstance(dir)
	if err != nil {
		return nil, err
	}
	b, err := in.sign(data, p)
	if err != nil {
		return nil, err
	}
	return protojson.Marshal(b)
}

func (in *instance) sign(data []byte, p signParams) (*protobundle.Bundle, error) {
	t := p.time.UTC().Truncate(time.Second)

	signingKey, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		return nil, err
	}
	leaf, err := in.issueLeaf(p.identity, &signingKey.PublicKey, t)
	if err != nil {
		return nil, fmt.Errorf("issuing leaf certificate: %w", err)
	}

	digest := sha256.Sum256(data)
	sig, err := ecdsa.SignASN1(rand.Reader, signingKey, digest[:])
	if err != nil {
		return nil, err
	}

	tsr, err := in.timestamp(sig, t)
	if err != nil {
		return nil, fmt.Errorf("timestamping signature: %w", err)
	}

	body := rekorV2Entry(digest[:], sig, leaf.Raw)
	seed := make([]byte, 32)
	if _, err := rand.Read(seed); err != nil {
		return nil, err
	}
	entryLeaf := hashLeaf(body)
	tr := tree{size: p.treeSize, leaf: func(i uint64) []byte {
		if i == p.leafIndex {
			return entryLeaf
		}
		return fillerLeaf(seed, i)
	}}
	rootHash := tr.root()
	checkpoint, err := in.checkpoint(p.treeSize, rootHash)
	if err != nil {
		return nil, fmt.Errorf("signing checkpoint: %w", err)
	}

	return &protobundle.Bundle{
		MediaType: bundleMediaType,
		VerificationMaterial: &protobundle.VerificationMaterial{
			Content: &protobundle.VerificationMaterial_Certificate{
				Certificate: &protocommon.X509Certificate{RawBytes: leaf.Raw},
			},
			TlogEntries: []*protorekor.TransparencyLogEntry{{
				LogIndex:    int64(p.leafIndex),
				LogId:       &protocommon.LogId{KeyId: rekorV2LogID(in.origin, in.logKey.Public().(ed25519.PublicKey))},
				KindVersion: &protorekor.KindVersion{Kind: "hashedrekord", Version: "0.0.2"},
				InclusionProof: &protorekor.InclusionProof{
					LogIndex:   int64(p.leafIndex),
					RootHash:   rootHash,
					TreeSize:   int64(p.treeSize),
					Hashes:     tr.inclusionProof(p.leafIndex),
					Checkpoint: &protorekor.Checkpoint{Envelope: checkpoint},
				},
				CanonicalizedBody: body,
			}},
			TimestampVerificationData: &protobundle.TimestampVerificationData{
				Rfc3161Timestamps: []*protocommon.RFC3161SignedTimestamp{{SignedTimestamp: tsr}},
			},
		},
		Content: &protobundle.Bundle_MessageSignature{
			MessageSignature: &protocommon.MessageSignature{
				MessageDigest: &protocommon.HashOutput{
					Algorithm: protocommon.HashAlgorithm_SHA2_256,
					Digest:    digest[:],
				},
				Signature: sig,
			},
		},
	}, nil
}

// issueLeaf issues a leaf certificate the way Fulcio does: it signs a
// precertificate with the CT poison extension, gets an SCT for it from the
// CT log, and signs the final certificate with the SCT list in place of the
// poison. The validity runs from one minute before t through nine minutes
// after it, 10 minutes in all.
func (in *instance) issueLeaf(id githubIdentity, pub *ecdsa.PublicKey, t time.Time) (*x509.Certificate, error) {
	san, err := url.Parse(id.buildSignerURI)
	if err != nil {
		return nil, fmt.Errorf("-build-signer-uri: %w", err)
	}
	exts, err := id.extensions()
	if err != nil {
		return nil, err
	}
	serial, err := randomSerial()
	if err != nil {
		return nil, err
	}
	ski, err := subjectKeyID(pub)
	if err != nil {
		return nil, err
	}
	notBefore := t.Add(-time.Minute)
	template := func(last pkix.Extension) *x509.Certificate {
		return &x509.Certificate{
			SerialNumber:    serial,
			NotBefore:       notBefore,
			NotAfter:        t.Add(9 * time.Minute),
			KeyUsage:        x509.KeyUsageDigitalSignature,
			ExtKeyUsage:     []x509.ExtKeyUsage{x509.ExtKeyUsageCodeSigning},
			SubjectKeyId:    ski,
			URIs:            []*url.URL{san},
			ExtraExtensions: append(append([]pkix.Extension(nil), exts...), last),
		}
	}

	poison := pkix.Extension{Id: oidCTPoison, Critical: true, Value: asn1.NullBytes}
	precertDER, err := x509.CreateCertificate(rand.Reader, template(poison), in.intermediate, pub, in.intermediateKey)
	if err != nil {
		return nil, err
	}
	precert, err := x509.ParseCertificate(precertDER)
	if err != nil {
		return nil, err
	}
	sctList, err := in.sctList(precert, notBefore.Add(500*time.Millisecond))
	if err != nil {
		return nil, fmt.Errorf("issuing SCT: %w", err)
	}
	der, err := x509.CreateCertificate(rand.Reader, template(pkix.Extension{Id: oidCTSCTList, Value: sctList}), in.intermediate, pub, in.intermediateKey)
	if err != nil {
		return nil, err
	}
	return x509.ParseCertificate(der)
}

// sctList returns the value of the embedded SCT list extension: a DER OCTET
// STRING holding the TLS-encoded SignedCertificateTimestampList with one SCT
// from the CT log over precert.
func (in *instance) sctList(precert *x509.Certificate, at time.Time) ([]byte, error) {
	tbs, err := ctx509.BuildPrecertTBS(precert.RawTBSCertificate, nil)
	if err != nil {
		return nil, err
	}
	ctSPKI, err := x509.MarshalPKIXPublicKey(&in.ctLogKey.PublicKey)
	if err != nil {
		return nil, err
	}
	ms := uint64(at.UnixMilli())
	sct := ct.SignedCertificateTimestamp{
		SCTVersion: ct.V1,
		LogID:      ct.LogID{KeyID: sha256.Sum256(ctSPKI)},
		Timestamp:  ms,
	}
	input, err := ct.SerializeSCTSignatureInput(sct, ct.LogEntry{Leaf: ct.MerkleTreeLeaf{
		Version:  ct.V1,
		LeafType: ct.TimestampedEntryLeafType,
		TimestampedEntry: &ct.TimestampedEntry{
			Timestamp: ms,
			EntryType: ct.PrecertLogEntryType,
			PrecertEntry: &ct.PreCert{
				IssuerKeyHash:  sha256.Sum256(in.intermediate.RawSubjectPublicKeyInfo),
				TBSCertificate: tbs,
			},
		},
	}})
	if err != nil {
		return nil, err
	}
	h := sha256.Sum256(input)
	sig, err := ecdsa.SignASN1(rand.Reader, in.ctLogKey, h[:])
	if err != nil {
		return nil, err
	}
	sct.Signature = ct.DigitallySigned{
		Algorithm: cttls.SignatureAndHashAlgorithm{Hash: cttls.SHA256, Signature: cttls.ECDSA},
		Signature: sig,
	}
	sctBytes, err := cttls.Marshal(sct)
	if err != nil {
		return nil, err
	}
	list, err := cttls.Marshal(ctx509.SignedCertificateTimestampList{SCTList: []ctx509.SerializedSCT{{Val: sctBytes}}})
	if err != nil {
		return nil, err
	}
	return asn1.Marshal(list)
}

// extensions returns the Fulcio identity extensions for a GitHub Actions
// token, in Fulcio's order. Extensions .1.1 through .1.6 are deprecated and
// hold raw bytes; .1.8 and later hold DER UTF8Strings.
func (id githubIdentity) extensions() ([]pkix.Extension, error) {
	u, err := url.Parse(id.buildSignerURI)
	if err != nil {
		return nil, fmt.Errorf("-build-signer-uri: %w", err)
	}
	workflowPath, ref, ok := strings.Cut(u.Path, "@")
	parts := strings.SplitN(strings.TrimPrefix(workflowPath, "/"), "/", 3)
	if u.Scheme != "https" || u.Host == "" || !ok || ref == "" || len(parts) != 3 || parts[0] == "" || parts[1] == "" {
		return nil, fmt.Errorf("-build-signer-uri %q isn't of the form https://HOST/OWNER/REPO/WORKFLOW_PATH@REF", id.buildSignerURI)
	}
	server := u.Scheme + "://" + u.Host
	repository := parts[0] + "/" + parts[1]
	repositoryURL := server + "/" + repository
	workflowName := strings.TrimSuffix(path.Base(parts[2]), path.Ext(parts[2]))

	commit := id.commit
	if commit == "" {
		b := make([]byte, 20)
		if _, err := rand.Read(b); err != nil {
			return nil, err
		}
		commit = hex.EncodeToString(b)
	} else if b, err := hex.DecodeString(commit); err != nil || len(b) != 20 {
		return nil, fmt.Errorf("-commit %q isn't a 40-digit hex SHA", commit)
	}
	var b [8]byte
	if _, err := rand.Read(b[:]); err != nil {
		return nil, err
	}
	runID := 10_000_000_000 + binary.BigEndian.Uint64(b[:])%90_000_000_000

	raw := func(n int, v string) pkix.Extension {
		return pkix.Extension{Id: fulcioOID(n), Value: []byte(v)}
	}
	exts := []pkix.Extension{
		raw(1, id.issuer),
		raw(2, id.trigger),
		raw(3, commit),
		raw(4, workflowName),
		raw(5, repository),
		raw(6, ref),
	}
	for _, e := range []struct {
		n int
		v string
	}{
		{8, id.issuer},
		{9, id.buildSignerURI},
		{10, commit},
		{11, "github-hosted"},
		{12, repositoryURL},
		{13, commit},
		{14, ref},
		{15, strconv.FormatUint(id.repositoryID, 10)},
		{16, server + "/" + parts[0]},
		{17, strconv.FormatUint(id.ownerID, 10)},
		{18, id.buildSignerURI},
		{19, commit},
		{20, id.trigger},
		{21, fmt.Sprintf("%s/actions/runs/%d/attempts/1", repositoryURL, runID)},
		{22, "public"},
	} {
		v, err := asn1.MarshalWithParams(e.v, "utf8")
		if err != nil {
			return nil, err
		}
		exts = append(exts, pkix.Extension{Id: fulcioOID(e.n), Value: v})
	}
	return exts, nil
}

// timestamp returns a DER TimeStampResp, status granted, over the SHA-256
// digest of sig at time t.
//
// Sigstore's timestamp-authority builds its response with
// digitorus/timestamp, which takes genTime from Timestamp.Time but gets
// signingTime from the wall clock inside digitorus/pkcs7. To give both the
// requested time, as a real response has, this keeps the TSTInfo and the
// signingCertificateV2 attribute that digitorus/timestamp produced and
// signs them again with digitorus/pkcs7 the same way, with an explicit
// signingTime.
func (in *instance) timestamp(sig []byte, t time.Time) ([]byte, error) {
	digest := sha256.Sum256(sig)
	nonce, err := rand.Int(rand.Reader, new(big.Int).Lsh(big.NewInt(1), 64))
	if err != nil {
		return nil, err
	}
	ts := timestamp.Timestamp{
		HashAlgorithm:     crypto.SHA256,
		HashedMessage:     digest[:],
		Time:              t,
		Accuracy:          time.Second,
		Nonce:             nonce,
		Policy:            oidTSAPolicy,
		AddTSACertificate: true,
	}
	resp, err := ts.CreateResponseWithOpts(in.tsaLeaf, in.tsaKey, crypto.SHA256)
	if err != nil {
		return nil, err
	}

	var parsed struct {
		Status asn1.RawValue
		Token  asn1.RawValue
	}
	if rest, err := asn1.Unmarshal(resp, &parsed); err != nil || len(rest) != 0 {
		return nil, fmt.Errorf("parsing digitorus/timestamp response: %v", err)
	}
	p7, err := pkcs7.Parse(parsed.Token.FullBytes)
	if err != nil {
		return nil, err
	}
	if len(p7.Signers) != 1 {
		return nil, fmt.Errorf("digitorus/timestamp response has %d signers", len(p7.Signers))
	}
	var signingCertV2 []byte
	for _, a := range p7.Signers[0].AuthenticatedAttributes {
		if a.Type.Equal(oidSigningCertificateV2) {
			signingCertV2 = a.Value.Bytes
		}
	}
	if signingCertV2 == nil {
		return nil, errors.New("digitorus/timestamp response has no signingCertificateV2 attribute")
	}

	sd, err := pkcs7.NewSignedData(p7.Content)
	if err != nil {
		return nil, err
	}
	sd.SetDigestAlgorithm(pkcs7.OIDDigestAlgorithmSHA256)
	sd.SetContentType(oidTSTInfo)
	sd.GetSignedData().Version = 3
	if err := sd.AddSigner(in.tsaLeaf, in.tsaKey, pkcs7.SignerInfoConfig{
		ExtraSignedAttributes: []pkcs7.Attribute{
			{Type: oidSigningCertificateV2, Value: asn1.RawValue{FullBytes: signingCertV2}},
			{Type: pkcs7.OIDAttributeSigningTime, Value: t.UTC()},
		},
	}); err != nil {
		return nil, err
	}
	token, err := sd.Finish()
	if err != nil {
		return nil, err
	}
	return asn1.Marshal(struct {
		Status asn1.RawValue
		Token  asn1.RawValue
	}{parsed.Status, asn1.RawValue{FullBytes: token}})
}

// rekorV2Entry returns the canonical JSON of a Rekor v2 hashedrekord 0.0.2
// entry: the RFC 8785 form of its protobuf JSON encoding.
func rekorV2Entry(digest, sig, cert []byte) []byte {
	enc := base64.StdEncoding.EncodeToString
	return []byte(`{"apiVersion":"0.0.2","kind":"hashedrekord","spec":{"hashedRekordV002":{"data":{"algorithm":"SHA2_256","digest":"` +
		enc(digest) + `"},"signature":{"content":"` + enc(sig) +
		`","verifier":{"keyDetails":"PKIX_ECDSA_P256_SHA_256","x509Certificate":{"rawBytes":"` + enc(cert) + `"}}}}}}`)
}

// checkpoint returns a C2SP checkpoint for the tree, signed by the log key
// as a C2SP signed note.
func (in *instance) checkpoint(size uint64, rootHash []byte) (string, error) {
	pub := in.logKey.Public().(ed25519.PublicKey)
	keyID := rekorV2LogID(in.origin, pub)[:4]
	skey := fmt.Sprintf("PRIVATE+KEY+%s+%x+%s", in.origin, keyID,
		base64.StdEncoding.EncodeToString(append([]byte{0x01}, in.logKey.Seed()...)))
	signer, err := note.NewSigner(skey)
	if err != nil {
		return "", err
	}
	text := fmt.Sprintf("%s\n%d\n%s\n", in.origin, size, base64.StdEncoding.EncodeToString(rootHash))
	msg, err := note.Sign(&note.Note{Text: text}, signer)
	if err != nil {
		return "", err
	}
	return string(msg), nil
}
