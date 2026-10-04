package git

import (
	"bytes"
	"encoding/binary"
	"encoding/pem"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
)

// SigningKey is an SSH private key that signs commits. fmt prints a
// placeholder instead of the key, so it stays out of logs and errors.
type SigningKey struct {
	data []byte
}

// NewSigningKey returns the key in data, an unencrypted private key in
// OpenSSH format, such as ssh-keygen writes. Its errors never include data.
func NewSigningKey(data []byte) (*SigningKey, error) {
	notOpenSSH := errors.New("the key isn't a private key in OpenSSH format, such as ssh-keygen writes")
	block, _ := pem.Decode(data)
	if block == nil || block.Type != "OPENSSH PRIVATE KEY" {
		return nil, notOpenSSH
	}
	rest, ok := bytes.CutPrefix(block.Bytes, []byte("openssh-key-v1\x00"))
	if !ok || len(rest) < 4 {
		return nil, notOpenSSH
	}
	n := binary.BigEndian.Uint32(rest)
	if uint64(n) > uint64(len(rest)-4) {
		return nil, notOpenSSH
	}
	if cipher := string(rest[4 : 4+n]); cipher != "none" {
		return nil, errors.New("the key is encrypted; signing needs a key without a passphrase")
	}
	// ssh-keygen needs the PEM armor's line breaks and trailing newline, which
	// a key pasted into a Secret can lose.
	return &SigningKey{data: pem.EncodeToMemory(block)}, nil
}

// Format prints a placeholder instead of the key.
func (SigningKey) Format(f fmt.State, _ rune) {
	io.WriteString(f, "SigningKey(redacted)")
}

// write writes the key to a file in a new directory and returns the file's
// path and a function that deletes the directory. The directory is 0700 and
// the file 0600: ssh-keygen refuses a key that other users can read.
func (k *SigningKey) write() (string, func(), error) {
	dir, err := os.MkdirTemp("", "git-k8s-signing-")
	if err != nil {
		return "", nil, err
	}
	remove := func() { os.RemoveAll(dir) }
	path := filepath.Join(dir, "key")
	if err := os.WriteFile(path, k.data, 0o600); err != nil {
		remove()
		return "", nil, err
	}
	return path, remove, nil
}
