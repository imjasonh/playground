// Package userca mints short-lived SSH user certificates for gateway→app hops.
package userca

import (
	"crypto/ed25519"
	"crypto/rand"
	"encoding/pem"
	"fmt"
	"os"
	"path/filepath"
	"time"

	"golang.org/x/crypto/ssh"
)

// CA signs SSH user certificates asserting a platform username.
type CA struct {
	signer ssh.Signer
}

// Generate creates a new ed25519 user CA.
func Generate() (*CA, []byte, error) {
	_, priv, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		return nil, nil, err
	}
	signer, err := ssh.NewSignerFromKey(priv)
	if err != nil {
		return nil, nil, err
	}
	block, err := ssh.MarshalPrivateKey(priv, "sshcloud-user-ca")
	if err != nil {
		return nil, nil, err
	}
	return &CA{signer: signer}, pem.EncodeToMemory(block), nil
}

// LoadOrGenerate loads a CA private key from path or creates one.
func LoadOrGenerate(path string) (*CA, error) {
	if path == "" {
		ca, _, err := Generate()
		return ca, err
	}
	data, err := os.ReadFile(path)
	if err == nil {
		signer, err := ssh.ParsePrivateKey(data)
		if err != nil {
			return nil, err
		}
		return &CA{signer: signer}, nil
	}
	if !os.IsNotExist(err) {
		return nil, err
	}
	ca, pemBytes, err := Generate()
	if err != nil {
		return nil, err
	}
	dir := filepath.Dir(path)
	if dir != "." && dir != "" {
		if err := os.MkdirAll(dir, 0o755); err != nil {
			return nil, err
		}
	}
	if err := os.WriteFile(path, pemBytes, 0o600); err != nil {
		return nil, err
	}
	pubPath := path + ".pub"
	_ = os.WriteFile(pubPath, ssh.MarshalAuthorizedKey(ca.signer.PublicKey()), 0o644)
	return ca, nil
}

// PublicKey returns the CA public key (for injection into app VMs).
func (c *CA) PublicKey() ssh.PublicKey {
	return c.signer.PublicKey()
}

// PublicAuthorizedKey is the authorized_keys-format CA public key line.
func (c *CA) PublicAuthorizedKey() []byte {
	return ssh.MarshalAuthorizedKey(c.PublicKey())
}

// Cert is a minted user certificate plus the ephemeral private key signer.
type Cert struct {
	Signer    ssh.Signer // certificate signer for ssh.PublicKeys
	Principal string
	Serial    uint64
}

// Mint issues a user cert for principal valid for ttl (session-bound / minutes).
func (c *CA) Mint(principal string, ttl time.Duration) (*Cert, error) {
	if principal == "" {
		return nil, fmt.Errorf("principal required")
	}
	if ttl <= 0 {
		ttl = 5 * time.Minute
	}
	_, priv, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		return nil, err
	}
	pub, err := ssh.NewPublicKey(priv.Public().(ed25519.PublicKey))
	if err != nil {
		return nil, err
	}
	serial := uint64(time.Now().UnixNano())
	now := time.Now().UTC()
	cert := &ssh.Certificate{
		Key:             pub,
		Serial:          serial,
		CertType:        ssh.UserCert,
		KeyId:           principal,
		ValidPrincipals: []string{principal},
		ValidAfter:      uint64(now.Add(-1 * time.Minute).Unix()),
		ValidBefore:     uint64(now.Add(ttl).Unix()),
		Permissions: ssh.Permissions{
			Extensions: map[string]string{
				"permit-pty": "",
			},
		},
	}
	if err := cert.SignCert(rand.Reader, c.signer); err != nil {
		return nil, err
	}
	signer, err := ssh.NewCertSigner(cert, mustSigner(priv))
	if err != nil {
		return nil, err
	}
	return &Cert{Signer: signer, Principal: principal, Serial: serial}, nil
}

func mustSigner(priv ed25519.PrivateKey) ssh.Signer {
	s, err := ssh.NewSignerFromKey(priv)
	if err != nil {
		panic(err)
	}
	return s
}
