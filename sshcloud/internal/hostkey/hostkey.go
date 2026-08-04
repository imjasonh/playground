// Package hostkey loads or creates the gateway SSH host key.
package hostkey

import (
	"crypto/ed25519"
	"crypto/rand"
	"encoding/pem"
	"fmt"
	"os"
	"path/filepath"

	"golang.org/x/crypto/ssh"
)

// LoadOrGenerate returns a Signer from path, creating an ed25519 OpenSSH key if missing.
// If path is empty, a ephemeral in-memory key is generated (not persisted).
func LoadOrGenerate(path string) (ssh.Signer, error) {
	if path == "" {
		_, signer, err := Generate()
		return signer, err
	}
	data, err := os.ReadFile(path)
	if err == nil {
		return ssh.ParsePrivateKey(data)
	}
	if !os.IsNotExist(err) {
		return nil, err
	}
	pem, signer, err := Generate()
	if err != nil {
		return nil, err
	}
	dir := filepath.Dir(path)
	if dir != "." && dir != "" {
		if err := os.MkdirAll(dir, 0o755); err != nil {
			return nil, err
		}
	}
	if err := os.WriteFile(path, pem, 0o600); err != nil {
		return nil, fmt.Errorf("write host key: %w", err)
	}
	return signer, nil
}

// Generate creates a new ed25519 host key (PEM bytes + Signer).
func Generate() ([]byte, ssh.Signer, error) {
	_, priv, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		return nil, nil, err
	}
	signer, err := ssh.NewSignerFromKey(priv)
	if err != nil {
		return nil, nil, err
	}
	block, err := ssh.MarshalPrivateKey(priv, "")
	if err != nil {
		return nil, nil, fmt.Errorf("marshal host key: %w", err)
	}
	return pem.EncodeToMemory(block), signer, nil
}
