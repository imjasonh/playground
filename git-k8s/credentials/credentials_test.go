package credentials_test

import (
	"bytes"
	"crypto/ecdsa"
	"crypto/ed25519"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/x509"
	"encoding/pem"
	"reflect"
	"strings"
	"testing"

	"golang.org/x/crypto/ssh"
	"golang.org/x/crypto/ssh/knownhosts"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/credentials"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

const (
	httpsURL = "https://git.example.com/app.git"
	sshURL   = "ssh://git@git.example.com:2222/app.git"
	scpURL   = "git@git.example.com:app.git"
)

func TestRemote(t *testing.T) {
	key, hosts := newKey(t), knownHosts(t)
	pkcs8 := newPKCS8Key(t)
	for _, c := range []struct {
		name string
		url  string
		data map[string][]byte
		want git.Remote
	}{
		{"no Secret", httpsURL, nil, git.Remote{URL: httpsURL}},
		{"basic auth", httpsURL, map[string][]byte{"username": []byte("me"), "password": []byte("pw")},
			git.Remote{URL: httpsURL, Auth: &git.Auth{Username: "me", Password: "pw"}}},
		{"password only", httpsURL, map[string][]byte{"password": []byte("pw")},
			git.Remote{URL: httpsURL, Auth: &git.Auth{Username: "git", Password: "pw"}}},
		{"ssh URL", sshURL, map[string][]byte{"ssh-privatekey": key, "known_hosts": hosts},
			git.Remote{URL: sshURL, SSH: &git.SSHKey{PrivateKey: key, KnownHosts: hosts}}},
		{"scp-like URL", scpURL, map[string][]byte{"ssh-privatekey": key, "known_hosts": hosts, "username": []byte("me")},
			git.Remote{URL: scpURL, SSH: &git.SSHKey{PrivateKey: key, KnownHosts: hosts}}},
		{"PKCS #8 key", scpURL, map[string][]byte{"ssh-privatekey": pkcs8, "known_hosts": hosts},
			git.Remote{URL: scpURL, SSH: &git.SSHKey{PrivateKey: pkcs8, KnownHosts: hosts}}},
	} {
		t.Run(c.name, func(t *testing.T) {
			got, err := remote(t, c.url, c.data)
			if err != nil {
				t.Fatal(err)
			}
			if !reflect.DeepEqual(got, c.want) {
				t.Errorf("Remote() = %+v, want %+v", got, c.want)
			}
		})
	}
}

func TestRemoteErrors(t *testing.T) {
	key, hosts := newKey(t), knownHosts(t)
	withKey := func(key []byte) map[string][]byte {
		return map[string][]byte{"ssh-privatekey": key, "known_hosts": hosts}
	}
	_, ed, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	public, err := ssh.NewPublicKey(ed.Public())
	if err != nil {
		t.Fatal(err)
	}
	passphrase, err := ssh.MarshalPrivateKeyWithPassphrase(ed, "", []byte("secret"))
	if err != nil {
		t.Fatal(err)
	}
	legacy := &pem.Block{
		Type:    "RSA PRIVATE KEY",
		Headers: map[string]string{"Proc-Type": "4,ENCRYPTED", "DEK-Info": "AES-128-CBC,00112233445566778899AABBCCDDEEFF"},
		Bytes:   []byte("ciphertext"),
	}
	for _, c := range []struct {
		name string
		url  string
		data map[string][]byte
		want string
	}{
		{"ssh URL without a Secret", sshURL, nil, "SSH URLs need a secretRef"},
		{"scp-like URL without a Secret", scpURL, nil, "SSH URLs need a secretRef"},
		{"no password", httpsURL, map[string][]byte{"username": []byte("me")}, "Secret creds has no password key"},
		{"basic auth over SSH", sshURL, map[string][]byte{"password": []byte("pw")}, "Secret creds has no ssh-privatekey key"},
		{"no known hosts", sshURL, map[string][]byte{"ssh-privatekey": key}, "Secret creds has no known_hosts key"},
		{"blank known hosts", sshURL, map[string][]byte{"ssh-privatekey": key, "known_hosts": []byte(" \n")}, "has no known_hosts key"},
		{"no final newline", sshURL, withKey(bytes.TrimSuffix(key, []byte("\n"))), "must end with a newline"},
		{"carriage returns", sshURL, withKey(bytes.ReplaceAll(key, []byte("\n"), []byte("\r\n"))), "no carriage returns"},
		{"public key", sshURL, withKey(ssh.MarshalAuthorizedKey(public)), "isn't a PEM-encoded private key"},
		{"PEM public key", sshURL, withKey(pem.EncodeToMemory(&pem.Block{Type: "PUBLIC KEY", Bytes: public.Marshal()})), "isn't a PEM-encoded private key"},
		{"passphrase", scpURL, withKey(pem.EncodeToMemory(passphrase)), "needs a passphrase"},
		{"encrypted PKCS #8 key", scpURL, withKey(pem.EncodeToMemory(&pem.Block{Type: "ENCRYPTED PRIVATE KEY", Bytes: []byte("ciphertext")})), "needs a passphrase"},
		{"encrypted PEM key", scpURL, withKey(pem.EncodeToMemory(legacy)), "needs a passphrase"},
	} {
		t.Run(c.name, func(t *testing.T) {
			_, err := remote(t, c.url, c.data)
			if err == nil || !strings.Contains(err.Error(), c.want) {
				t.Fatalf("err = %v, want one that says %q", err, c.want)
			}
			for _, data := range c.data {
				for line := range strings.SplitSeq(string(data), "\n") {
					if line = strings.TrimSpace(line); len(line) > 16 && !strings.HasPrefix(line, "-") && strings.Contains(err.Error(), line) {
						t.Errorf("the error includes the Secret's data")
					}
				}
			}
		})
	}
}

func TestRemoteNeedsSecret(t *testing.T) {
	repo := repository(sshURL)
	repo.Spec.SecretRef = &gitk8s.SecretRef{Name: "creds"}
	ctx, _ := kube.Fake(t.Context(), repo)
	if _, err := credentials.Remote(ctx, repo); err == nil || !strings.Contains(err.Error(), "Secret creds doesn't exist") {
		t.Errorf("err = %v, want one that says the Secret doesn't exist", err)
	}
}

// remote calls credentials.Remote for a repository at url whose secretRef
// names a Secret that holds data, or that has no secretRef if data is nil.
func remote(t *testing.T, url string, data map[string][]byte) (git.Remote, error) {
	t.Helper()
	repo := repository(url)
	var world []any
	if data != nil {
		repo.Spec.SecretRef = &gitk8s.SecretRef{Name: "creds"}
		secret := &k8s.Secret{Object: kube.Meta("creds", nil), Data: data}
		secret.Namespace = "default"
		world = append(world, secret)
	}
	ctx, _ := kube.Fake(t.Context(), repo, world...)
	return credentials.Remote(ctx, repo)
}

func repository(url string) *gitk8s.Repository {
	repo := &gitk8s.Repository{Object: kube.Meta("app", nil), Spec: gitk8s.GitRepositorySpec{URL: url}}
	repo.Namespace = "default"
	return repo
}

func newKey(t *testing.T) []byte {
	t.Helper()
	_, key, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	block, err := ssh.MarshalPrivateKey(key, "")
	if err != nil {
		t.Fatal(err)
	}
	return pem.EncodeToMemory(block)
}

func newPKCS8Key(t *testing.T) []byte {
	t.Helper()
	key, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	der, err := x509.MarshalPKCS8PrivateKey(key)
	if err != nil {
		t.Fatal(err)
	}
	return pem.EncodeToMemory(&pem.Block{Type: "PRIVATE KEY", Bytes: der})
}

func knownHosts(t *testing.T) []byte {
	t.Helper()
	public, _, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	key, err := ssh.NewPublicKey(public)
	if err != nil {
		t.Fatal(err)
	}
	return []byte(knownhosts.Line([]string{"git.example.com:2222"}, key) + "\n")
}
