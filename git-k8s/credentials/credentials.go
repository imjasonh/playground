// Package credentials reads the URL and credentials of a repository.
//
// Reading the Secret makes kube's generate grant a program get access to
// Secrets in every namespace, because generate grants what a program's
// packages call. Only the programs that fetch from or push to a repository
// import this package, so the others never get that access.
package credentials

import (
	"bytes"
	"context"
	"encoding/binary"
	"encoding/pem"
	"errors"
	"fmt"
	"strings"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

// Remote returns a repository's URL and credentials. It reads the Secret
// that SecretRef names with kube.Fetch, so it must run in a reconcile, and
// the Secret isn't cached.
func Remote(ctx context.Context, repo *gitk8s.Repository) (git.Remote, error) {
	r := git.Remote{URL: repo.Spec.URL}
	var err error
	switch ref := repo.Spec.SecretRef; {
	case ref != nil && git.IsSSH(r.URL):
		r.SSH, err = sshKey(ctx, repo.Namespace, ref.Name)
	case ref != nil:
		r.Auth, err = basicAuth(ctx, repo.Namespace, ref.Name)
	case git.IsSSH(r.URL):
		err = errors.New("SSH URLs need a secretRef with ssh-privatekey and known_hosts keys")
	}
	return r, err
}

// basicAuth reads a username and password for HTTP basic authentication
// from a Secret, such as a kubernetes.io/basic-auth Secret.
func basicAuth(ctx context.Context, namespace, name string) (*git.Auth, error) {
	s, err := secret(ctx, namespace, name)
	if err != nil {
		return nil, err
	}
	password := string(s.Data["password"])
	if password == "" {
		return nil, fmt.Errorf("Secret %s has no password key", name)
	}
	username := string(s.Data["username"])
	if username == "" {
		username = "git"
	}
	return &git.Auth{Username: username, Password: password}, nil
}

// sshKey reads a private key and the host keys to accept from a Secret,
// such as a kubernetes.io/ssh-auth Secret with a known_hosts key added.
func sshKey(ctx context.Context, namespace, name string) (*git.SSHKey, error) {
	s, err := secret(ctx, namespace, name)
	if err != nil {
		return nil, err
	}
	key := &git.SSHKey{PrivateKey: s.Data["ssh-privatekey"], KnownHosts: s.Data["known_hosts"]}
	switch {
	case len(key.PrivateKey) == 0:
		return nil, fmt.Errorf("Secret %s has no ssh-privatekey key", name)
	case len(bytes.TrimSpace(key.KnownHosts)) == 0:
		return nil, fmt.Errorf("Secret %s has no known_hosts key, which lists the host keys to accept", name)
	}
	if err := checkPrivateKey(key.PrivateKey); err != nil {
		return nil, fmt.Errorf("ssh-privatekey in Secret %s %w", name, err)
	}
	return key, nil
}

// checkPrivateKey reports keys that ssh can't use. ssh fails on these with
// errors that don't say what's wrong, such as "error in libcrypto" or
// "Permission denied". The errors never include the key.
func checkPrivateKey(key []byte) error {
	if bytes.ContainsRune(key, '\r') || !bytes.HasSuffix(key, []byte("\n")) {
		return errors.New("must end with a newline and have no carriage returns")
	}
	block, _ := pem.Decode(key)
	if block == nil || !strings.HasSuffix(block.Type, "PRIVATE KEY") {
		return errors.New("isn't a PEM-encoded private key")
	}
	// pem.Decode skips text before a block, but ssh reads an OpenSSH key
	// only if the block starts at the first byte.
	if !bytes.HasPrefix(key, []byte("-----BEGIN ")) {
		return errors.New("must start with -----BEGIN")
	}
	encrypted := block.Type == "ENCRYPTED PRIVATE KEY" || strings.Contains(block.Headers["Proc-Type"], "ENCRYPTED")
	// An OpenSSH key names its cipher right after a magic string.
	if rest, ok := bytes.CutPrefix(block.Bytes, []byte("openssh-key-v1\x00")); ok && len(rest) >= 4 {
		if n := binary.BigEndian.Uint32(rest); uint64(n) <= uint64(len(rest)-4) {
			encrypted = string(rest[4:4+n]) != "none"
		}
	}
	if encrypted {
		return errors.New("needs a passphrase, which git-k8s can't enter")
	}
	return nil
}

func secret(ctx context.Context, namespace, name string) (*k8s.Secret, error) {
	s, err := kube.Fetch[k8s.Secret](ctx, namespace, name)
	if err != nil {
		return nil, fmt.Errorf("reading Secret %s: %w", name, err)
	}
	if s == nil {
		return nil, fmt.Errorf("Secret %s doesn't exist", name)
	}
	return s, nil
}
