package main

import (
	"crypto"
	"crypto/ecdsa"
	"crypto/ed25519"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/sha1"
	"crypto/sha256"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/asn1"
	"encoding/pem"
	"errors"
	"flag"
	"fmt"
	"io"
	"math/big"
	"net/url"
	"os"
	"path/filepath"
	"time"

	protocommon "github.com/sigstore/protobuf-specs/gen/pb-go/common/v1"
	prototrustroot "github.com/sigstore/protobuf-specs/gen/pb-go/trustroot/v1"
	"google.golang.org/protobuf/encoding/protojson"
	"google.golang.org/protobuf/types/known/timestamppb"
)

// Files that init writes and sign reads, relative to the -dir directory.
const (
	fulcioRootCertFile         = "fulcio_root.crt.pem"
	fulcioRootKeyFile          = "fulcio_root.key.pem"
	fulcioIntermediateCertFile = "fulcio_intermediate.crt.pem"
	fulcioIntermediateKeyFile  = "fulcio_intermediate.key.pem"
	tsaRootCertFile            = "tsa_root.crt.pem"
	tsaRootKeyFile             = "tsa_root.key.pem"
	tsaLeafCertFile            = "tsa_leaf.crt.pem"
	tsaLeafKeyFile             = "tsa_leaf.key.pem"
	logKeyFile                 = "log.key.pem"
	ctLogKeyFile               = "ctlog.key.pem"
	trustedRootFile            = "trusted_root.json"
)

const (
	trustedRootMediaType = "application/vnd.dev.sigstore.trustedroot+json;version=0.1"
	fulcioURI            = "https://fulcio.c3-boot.test"
	tsaURI               = "https://timestamp.c3-boot.test/api/v1/timestamp"
	ctLogURL             = "https://ctfe.c3-boot.test/test"
	defaultOrigin        = "log.c3-boot.test"
	defaultNotBefore     = "2020-01-01T00:00:00Z"
	defaultNotAfter      = "2040-12-31T23:59:59Z"
)

func runInit(args []string, stderr io.Writer) error {
	fs := flag.NewFlagSet("init", flag.ContinueOnError)
	fs.SetOutput(stderr)
	dir := fs.String("dir", "", "directory to write keys, certificates, and trusted_root.json to (required)")
	origin := fs.String("origin", defaultOrigin, "checkpoint origin of the Rekor v2 log; also the host name of its baseUrl")
	notBefore := fs.String("not-before", defaultNotBefore, "start of every certificate and trusted root validity window, RFC 3339")
	notAfter := fs.String("not-after", defaultNotAfter, "end of every certificate and trusted root validity window, RFC 3339")
	if err := fs.Parse(args); err != nil {
		return err
	}
	if fs.NArg() != 0 {
		return fmt.Errorf("init: unexpected arguments %q", fs.Args())
	}
	if *dir == "" {
		return errors.New("init: -dir is required")
	}
	nb, err := time.Parse(time.RFC3339, *notBefore)
	if err != nil {
		return fmt.Errorf("init: -not-before: %w", err)
	}
	na, err := time.Parse(time.RFC3339, *notAfter)
	if err != nil {
		return fmt.Errorf("init: -not-after: %w", err)
	}
	if !nb.Before(na) {
		return errors.New("init: -not-before must be earlier than -not-after")
	}
	return initInstance(*dir, *origin, nb.UTC(), na.UTC())
}

// initInstance generates every key and certificate of a fake Sigstore
// instance and writes them, and its trusted root, to dir.
func initInstance(dir, origin string, notBefore, notAfter time.Time) error {
	if u, err := url.Parse("https://" + origin); err != nil || u.Hostname() != origin {
		return fmt.Errorf("init: origin %q must be a bare host name, because sigstore-go takes the checkpoint origin from the log's baseUrl host", origin)
	}
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return err
	}

	fulcioRootKey, err := ecdsa.GenerateKey(elliptic.P384(), rand.Reader)
	if err != nil {
		return err
	}
	// Unlike the TSA root, Sigstore's Fulcio root names itself in an
	// authority key identifier.
	fulcioRootSKI, err := subjectKeyID(&fulcioRootKey.PublicKey)
	if err != nil {
		return err
	}
	fulcioRoot, err := issueCert(&x509.Certificate{
		Subject:               pkix.Name{Organization: []string{"sigstore.dev"}, CommonName: "sigstore"},
		NotBefore:             notBefore,
		NotAfter:              notAfter,
		KeyUsage:              x509.KeyUsageCertSign | x509.KeyUsageCRLSign,
		BasicConstraintsValid: true,
		IsCA:                  true,
		MaxPathLen:            -1,
		SubjectKeyId:          fulcioRootSKI,
		AuthorityKeyId:        fulcioRootSKI,
	}, nil, &fulcioRootKey.PublicKey, fulcioRootKey)
	if err != nil {
		return fmt.Errorf("init: Fulcio root: %w", err)
	}

	fulcioIntermediateKey, err := ecdsa.GenerateKey(elliptic.P384(), rand.Reader)
	if err != nil {
		return err
	}
	fulcioIntermediate, err := issueCert(&x509.Certificate{
		Subject:               pkix.Name{Organization: []string{"sigstore.dev"}, CommonName: "sigstore-intermediate"},
		NotBefore:             notBefore,
		NotAfter:              notAfter,
		KeyUsage:              x509.KeyUsageCertSign | x509.KeyUsageCRLSign,
		ExtKeyUsage:           []x509.ExtKeyUsage{x509.ExtKeyUsageCodeSigning},
		BasicConstraintsValid: true,
		IsCA:                  true,
		MaxPathLenZero:        true,
	}, fulcioRoot, &fulcioIntermediateKey.PublicKey, fulcioRootKey)
	if err != nil {
		return fmt.Errorf("init: Fulcio intermediate: %w", err)
	}

	tsaRootKey, err := ecdsa.GenerateKey(elliptic.P384(), rand.Reader)
	if err != nil {
		return err
	}
	tsaRoot, err := issueCert(&x509.Certificate{
		Subject:               pkix.Name{Organization: []string{"sigstore.dev"}, CommonName: "sigstore-tsa-selfsigned"},
		NotBefore:             notBefore,
		NotAfter:              notAfter,
		KeyUsage:              x509.KeyUsageCertSign | x509.KeyUsageCRLSign,
		BasicConstraintsValid: true,
		IsCA:                  true,
		MaxPathLenZero:        true,
	}, nil, &tsaRootKey.PublicKey, tsaRootKey)
	if err != nil {
		return fmt.Errorf("init: TSA root: %w", err)
	}

	// The TSA leaf lists extKeyUsage last and critical, after the key
	// identifiers, as Sigstore's TSA certificate does. crypto/x509 writes its
	// own extKeyUsage before the key identifiers and never marks it critical,
	// so the extension goes in ExtraExtensions instead.
	tsaEKU, err := asn1.Marshal([]asn1.ObjectIdentifier{oidExtKeyUsageTimeStamping})
	if err != nil {
		return err
	}
	tsaLeafKey, err := ecdsa.GenerateKey(elliptic.P384(), rand.Reader)
	if err != nil {
		return err
	}
	tsaLeaf, err := issueCert(&x509.Certificate{
		Subject:         pkix.Name{Organization: []string{"sigstore.dev"}, CommonName: "sigstore-tsa"},
		NotBefore:       notBefore,
		NotAfter:        notAfter,
		KeyUsage:        x509.KeyUsageDigitalSignature,
		ExtraExtensions: []pkix.Extension{{Id: oidExtensionExtKeyUsage, Critical: true, Value: tsaEKU}},
	}, tsaRoot, &tsaLeafKey.PublicKey, tsaRootKey)
	if err != nil {
		return fmt.Errorf("init: TSA leaf: %w", err)
	}

	logPub, logKey, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		return err
	}
	ctLogKey, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		return err
	}

	for name, key := range map[string]crypto.PrivateKey{
		fulcioRootKeyFile:         fulcioRootKey,
		fulcioIntermediateKeyFile: fulcioIntermediateKey,
		tsaRootKeyFile:            tsaRootKey,
		tsaLeafKeyFile:            tsaLeafKey,
		logKeyFile:                logKey,
		ctLogKeyFile:              ctLogKey,
	} {
		if err := writeKey(filepath.Join(dir, name), key); err != nil {
			return err
		}
	}
	for name, cert := range map[string]*x509.Certificate{
		fulcioRootCertFile:         fulcioRoot,
		fulcioIntermediateCertFile: fulcioIntermediate,
		tsaRootCertFile:            tsaRoot,
		tsaLeafCertFile:            tsaLeaf,
	} {
		if err := writeCert(filepath.Join(dir, name), cert); err != nil {
			return err
		}
	}

	tr, err := trustedRoot(trustedRootParams{
		origin:             origin,
		notBefore:          notBefore,
		notAfter:           notAfter,
		fulcioRoot:         fulcioRoot,
		fulcioIntermediate: fulcioIntermediate,
		tsaRoot:            tsaRoot,
		tsaLeaf:            tsaLeaf,
		logKey:             logPub,
		ctLogKey:           &ctLogKey.PublicKey,
	})
	if err != nil {
		return err
	}
	out, err := protojson.MarshalOptions{Multiline: true, Indent: "  "}.Marshal(tr)
	if err != nil {
		return err
	}
	return os.WriteFile(filepath.Join(dir, trustedRootFile), append(out, '\n'), 0o644)
}

var (
	oidExtensionExtKeyUsage    = asn1.ObjectIdentifier{2, 5, 29, 37}
	oidExtKeyUsageTimeStamping = asn1.ObjectIdentifier{1, 3, 6, 1, 5, 5, 7, 3, 8}
)

// issueCert creates a certificate from template with a random 20-byte
// serial number and, unless template sets one, an RFC 5280 method 1 subject
// key identifier, as Fulcio and Sigstore's TSA do. If parent is nil, the
// certificate is self-signed.
func issueCert(template, parent *x509.Certificate, pub crypto.PublicKey, signer crypto.Signer) (*x509.Certificate, error) {
	serial, err := randomSerial()
	if err != nil {
		return nil, err
	}
	template.SerialNumber = serial
	if template.SubjectKeyId == nil {
		ski, err := subjectKeyID(pub)
		if err != nil {
			return nil, err
		}
		template.SubjectKeyId = ski
	}
	if parent == nil {
		parent = template
	}
	der, err := x509.CreateCertificate(rand.Reader, template, parent, pub, signer)
	if err != nil {
		return nil, err
	}
	return x509.ParseCertificate(der)
}

// randomSerial returns a positive serial number of at most 20 bytes.
func randomSerial() (*big.Int, error) {
	return rand.Int(rand.Reader, new(big.Int).Lsh(big.NewInt(1), 159))
}

// subjectKeyID returns the SHA-1 digest of the subjectPublicKey bits.
func subjectKeyID(pub crypto.PublicKey) ([]byte, error) {
	der, err := x509.MarshalPKIXPublicKey(pub)
	if err != nil {
		return nil, err
	}
	var spki struct {
		Algorithm pkix.AlgorithmIdentifier
		PublicKey asn1.BitString
	}
	if _, err := asn1.Unmarshal(der, &spki); err != nil {
		return nil, err
	}
	sum := sha1.Sum(spki.PublicKey.Bytes)
	return sum[:], nil
}

// rekorV2LogID returns the log ID of a Rekor v2 log with an Ed25519 key:
// SHA-256(origin || 0x0A || 0x01 || key). Its first four bytes are the C2SP
// signed-note key ID of the checkpoint signature.
func rekorV2LogID(origin string, key ed25519.PublicKey) []byte {
	h := sha256.New()
	h.Write([]byte(origin))
	h.Write([]byte{'\n', 0x01})
	h.Write(key)
	return h.Sum(nil)
}

type trustedRootParams struct {
	origin              string
	notBefore, notAfter time.Time
	fulcioRoot          *x509.Certificate
	fulcioIntermediate  *x509.Certificate
	tsaRoot, tsaLeaf    *x509.Certificate
	logKey              ed25519.PublicKey
	ctLogKey            *ecdsa.PublicKey
}

func trustedRoot(p trustedRootParams) (*prototrustroot.TrustedRoot, error) {
	validFor := &protocommon.TimeRange{
		Start: timestamppb.New(p.notBefore),
		End:   timestamppb.New(p.notAfter),
	}
	logSPKI, err := x509.MarshalPKIXPublicKey(p.logKey)
	if err != nil {
		return nil, err
	}
	ctSPKI, err := x509.MarshalPKIXPublicKey(p.ctLogKey)
	if err != nil {
		return nil, err
	}
	ctLogID := sha256.Sum256(ctSPKI)
	return &prototrustroot.TrustedRoot{
		MediaType: trustedRootMediaType,
		Tlogs: []*prototrustroot.TransparencyLogInstance{{
			BaseUrl:       "https://" + p.origin,
			HashAlgorithm: protocommon.HashAlgorithm_SHA2_256,
			PublicKey: &protocommon.PublicKey{
				RawBytes:   logSPKI,
				KeyDetails: protocommon.PublicKeyDetails_PKIX_ED25519,
				ValidFor:   validFor,
			},
			LogId: &protocommon.LogId{KeyId: rekorV2LogID(p.origin, p.logKey)},
		}},
		CertificateAuthorities: []*prototrustroot.CertificateAuthority{{
			Subject:   &protocommon.DistinguishedName{Organization: "sigstore.dev", CommonName: "sigstore"},
			Uri:       fulcioURI,
			CertChain: certChain(p.fulcioIntermediate, p.fulcioRoot),
			ValidFor:  validFor,
		}},
		Ctlogs: []*prototrustroot.TransparencyLogInstance{{
			BaseUrl:       ctLogURL,
			HashAlgorithm: protocommon.HashAlgorithm_SHA2_256,
			PublicKey: &protocommon.PublicKey{
				RawBytes:   ctSPKI,
				KeyDetails: protocommon.PublicKeyDetails_PKIX_ECDSA_P256_SHA_256,
				ValidFor:   validFor,
			},
			LogId: &protocommon.LogId{KeyId: ctLogID[:]},
		}},
		TimestampAuthorities: []*prototrustroot.CertificateAuthority{{
			Subject:   &protocommon.DistinguishedName{Organization: "sigstore.dev", CommonName: "sigstore-tsa-selfsigned"},
			Uri:       tsaURI,
			CertChain: certChain(p.tsaLeaf, p.tsaRoot),
			ValidFor:  validFor,
		}},
	}, nil
}

func certChain(certs ...*x509.Certificate) *protocommon.X509CertificateChain {
	chain := &protocommon.X509CertificateChain{}
	for _, c := range certs {
		chain.Certificates = append(chain.Certificates, &protocommon.X509Certificate{RawBytes: c.Raw})
	}
	return chain
}

func writeKey(path string, key crypto.PrivateKey) error {
	der, err := x509.MarshalPKCS8PrivateKey(key)
	if err != nil {
		return err
	}
	return os.WriteFile(path, pem.EncodeToMemory(&pem.Block{Type: "PRIVATE KEY", Bytes: der}), 0o600)
}

func writeCert(path string, cert *x509.Certificate) error {
	return os.WriteFile(path, pem.EncodeToMemory(&pem.Block{Type: "CERTIFICATE", Bytes: cert.Raw}), 0o644)
}

func readPEM(path, blockType string) ([]byte, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	block, _ := pem.Decode(data)
	if block == nil || block.Type != blockType {
		return nil, fmt.Errorf("%s: no %s PEM block", path, blockType)
	}
	return block.Bytes, nil
}

func readCert(path string) (*x509.Certificate, error) {
	der, err := readPEM(path, "CERTIFICATE")
	if err != nil {
		return nil, err
	}
	return x509.ParseCertificate(der)
}

func readECDSAKey(path string) (*ecdsa.PrivateKey, error) {
	der, err := readPEM(path, "PRIVATE KEY")
	if err != nil {
		return nil, err
	}
	key, err := x509.ParsePKCS8PrivateKey(der)
	if err != nil {
		return nil, fmt.Errorf("%s: %w", path, err)
	}
	k, ok := key.(*ecdsa.PrivateKey)
	if !ok {
		return nil, fmt.Errorf("%s: %T is not an ECDSA key", path, key)
	}
	return k, nil
}

func readEd25519Key(path string) (ed25519.PrivateKey, error) {
	der, err := readPEM(path, "PRIVATE KEY")
	if err != nil {
		return nil, err
	}
	key, err := x509.ParsePKCS8PrivateKey(der)
	if err != nil {
		return nil, fmt.Errorf("%s: %w", path, err)
	}
	k, ok := key.(ed25519.PrivateKey)
	if !ok {
		return nil, fmt.Errorf("%s: %T is not an Ed25519 key", path, key)
	}
	return k, nil
}
