// Package certs makes the certificates that a webhook server needs: a
// certificate authority, and serving certificates that it signs for the names
// the API server uses to reach the server.
package certs

import (
	"bytes"
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/tls"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/pem"
	"errors"
	"fmt"
	"math/big"
	"net"
	"time"
)

// Validity periods. A serving certificate is renewed when less than Renew of
// its validity remains.
const (
	CAValidity      = 10 * 365 * 24 * time.Hour
	ServingValidity = 365 * 24 * time.Hour
	Renew           = 30 * 24 * time.Hour
)

// Pair is a PEM-encoded certificate and private key.
type Pair struct {
	Cert, Key []byte
}

// NewCA returns a self-signed certificate authority.
func NewCA(name string, now time.Time) (Pair, error) {
	tmpl := &x509.Certificate{
		Subject:               pkix.Name{CommonName: name},
		NotBefore:             now.Add(-time.Hour),
		NotAfter:              now.Add(CAValidity),
		KeyUsage:              x509.KeyUsageCertSign | x509.KeyUsageDigitalSignature,
		BasicConstraintsValid: true,
		IsCA:                  true,
	}
	return issue(tmpl, nil, nil)
}

// NewServing returns a serving certificate for hosts, which are DNS names or
// IP addresses, signed by ca.
func NewServing(ca Pair, hosts []string, now time.Time) (Pair, error) {
	caCert, caKey, err := parse(ca)
	if err != nil {
		return Pair{}, fmt.Errorf("reading the certificate authority: %w", err)
	}
	tmpl := &x509.Certificate{
		Subject:     pkix.Name{CommonName: hosts[0]},
		NotBefore:   now.Add(-time.Hour),
		NotAfter:    now.Add(ServingValidity),
		KeyUsage:    x509.KeyUsageDigitalSignature,
		ExtKeyUsage: []x509.ExtKeyUsage{x509.ExtKeyUsageServerAuth},
	}
	for _, h := range hosts {
		if ip := net.ParseIP(h); ip != nil {
			tmpl.IPAddresses = append(tmpl.IPAddresses, ip)
		} else {
			tmpl.DNSNames = append(tmpl.DNSNames, h)
		}
	}
	return issue(tmpl, caCert, caKey)
}

// Usable reports whether serving is signed by ca, covers every host, and
// stays valid for at least Renew after now.
func Usable(ca, serving Pair, hosts []string, now time.Time) bool {
	caCert, _, err := parse(ca)
	if err != nil {
		return false
	}
	cert, _, err := parse(serving)
	if err != nil || now.Add(Renew).After(cert.NotAfter) {
		return false
	}
	if _, err := tls.X509KeyPair(serving.Cert, serving.Key); err != nil {
		return false
	}
	if cert.CheckSignatureFrom(caCert) != nil {
		return false
	}
	for _, h := range hosts {
		if cert.VerifyHostname(h) != nil {
			return false
		}
	}
	return true
}

// ExpiresSoon reports whether ca expires within its renewal period, after
// which the framework replaces it.
func ExpiresSoon(ca Pair, now time.Time) bool {
	cert, _, err := parse(ca)
	return err != nil || now.Add(CAValidity/10).After(cert.NotAfter)
}

// ValidAt reports whether the PEM certificate certPEM is valid at now.
func ValidAt(certPEM []byte, now time.Time) bool {
	b, _ := pem.Decode(certPEM)
	if b == nil || b.Type != "CERTIFICATE" {
		return false
	}
	cert, err := x509.ParseCertificate(b.Bytes)
	return err == nil && !now.Before(cert.NotBefore) && now.Before(cert.NotAfter)
}

func issue(tmpl, parent *x509.Certificate, parentKey *ecdsa.PrivateKey) (Pair, error) {
	key, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		return Pair{}, err
	}
	serial, err := rand.Int(rand.Reader, new(big.Int).Lsh(big.NewInt(1), 127))
	if err != nil {
		return Pair{}, err
	}
	tmpl.SerialNumber = serial
	if parent == nil {
		parent, parentKey = tmpl, key
	}
	der, err := x509.CreateCertificate(rand.Reader, tmpl, parent, &key.PublicKey, parentKey)
	if err != nil {
		return Pair{}, err
	}
	keyDER, err := x509.MarshalECPrivateKey(key)
	if err != nil {
		return Pair{}, err
	}
	return Pair{
		Cert: pem.EncodeToMemory(&pem.Block{Type: "CERTIFICATE", Bytes: der}),
		Key:  pem.EncodeToMemory(&pem.Block{Type: "EC PRIVATE KEY", Bytes: keyDER}),
	}, nil
}

func parse(p Pair) (*x509.Certificate, *ecdsa.PrivateKey, error) {
	cb, _ := pem.Decode(p.Cert)
	if cb == nil || cb.Type != "CERTIFICATE" {
		return nil, nil, errors.New("no PEM certificate")
	}
	cert, err := x509.ParseCertificate(cb.Bytes)
	if err != nil {
		return nil, nil, err
	}
	kb, _ := pem.Decode(p.Key)
	if kb == nil {
		return nil, nil, errors.New("no PEM private key")
	}
	key, err := x509.ParseECPrivateKey(kb.Bytes)
	if err != nil {
		return nil, nil, err
	}
	if !bytes.Equal(cert.RawSubjectPublicKeyInfo, mustPKIX(&key.PublicKey)) {
		return nil, nil, errors.New("the private key doesn't match the certificate")
	}
	return cert, key, nil
}

func mustPKIX(pub *ecdsa.PublicKey) []byte {
	b, _ := x509.MarshalPKIXPublicKey(pub)
	return b
}
