// Package hostkey loads or creates the gateway SSH host key.
package hostkey

import (
	"crypto/ed25519"
	"crypto/rand"
	"encoding/pem"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"sync"

	"golang.org/x/crypto/ssh"
)

const maxPrivateKeyBytes = 64 << 10

var loadMu sync.Mutex

// LoadOrGenerate returns a Signer from path, creating an ed25519 OpenSSH key if missing.
// If path is empty, a ephemeral in-memory key is generated (not persisted).
func LoadOrGenerate(path string) (ssh.Signer, error) {
	if path == "" {
		_, signer, err := Generate()
		return signer, err
	}
	loadMu.Lock()
	defer loadMu.Unlock()

	dir := filepath.Dir(path)
	if dir != "." && dir != "" {
		if err := os.MkdirAll(dir, 0o755); err != nil {
			return nil, err
		}
	}
	file, err := os.OpenFile(path, os.O_WRONLY|os.O_CREATE|os.O_EXCL, 0o600)
	if os.IsExist(err) {
		return loadExisting(path)
	}
	if err != nil {
		return nil, fmt.Errorf("create host key: %w", err)
	}
	createdInfo, statErr := file.Stat()
	if statErr != nil {
		_ = file.Close()
		_ = os.Remove(path)
		return nil, fmt.Errorf("stat new host key: %w", statErr)
	}
	ok := false
	defer func() {
		_ = file.Close()
		if !ok {
			if current, err := os.Lstat(path); err == nil && os.SameFile(createdInfo, current) {
				_ = os.Remove(path)
			}
		}
	}()
	pemBytes, signer, err := Generate()
	if err != nil {
		return nil, err
	}
	if err := file.Chmod(0o600); err != nil {
		return nil, fmt.Errorf("set host key mode: %w", err)
	}
	if n, err := file.Write(pemBytes); err != nil {
		return nil, fmt.Errorf("write host key: %w", err)
	} else if n != len(pemBytes) {
		return nil, fmt.Errorf("write host key: %w", io.ErrShortWrite)
	}
	if err := file.Sync(); err != nil {
		return nil, fmt.Errorf("sync host key: %w", err)
	}
	if err := file.Close(); err != nil {
		return nil, fmt.Errorf("close host key: %w", err)
	}
	ok = true
	return signer, nil
}

func loadExisting(path string) (ssh.Signer, error) {
	file, err := os.Open(path)
	if err != nil {
		return nil, fmt.Errorf("open host key: %w", err)
	}
	defer file.Close()
	info, err := file.Stat()
	if err != nil {
		return nil, fmt.Errorf("stat host key: %w", err)
	}
	if !info.Mode().IsRegular() {
		return nil, fmt.Errorf("host key is not a regular file")
	}
	if info.Mode().Perm()&0o077 != 0 {
		return nil, fmt.Errorf("host key permissions %04o permit group or other access", info.Mode().Perm())
	}
	data, err := io.ReadAll(io.LimitReader(file, maxPrivateKeyBytes+1))
	if err != nil {
		return nil, fmt.Errorf("read host key: %w", err)
	}
	if len(data) > maxPrivateKeyBytes {
		return nil, fmt.Errorf("host key exceeds %d bytes", maxPrivateKeyBytes)
	}
	signer, err := ssh.ParsePrivateKey(data)
	if err != nil {
		return nil, fmt.Errorf("parse host key: %w", err)
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
