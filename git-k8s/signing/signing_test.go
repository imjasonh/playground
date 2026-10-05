package signing_test

import (
	"os/exec"
	"path"
	"slices"
	"strings"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/git-k8s/signing"
	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

func TestKey(t *testing.T) {
	signer := gittest.NewSigner(t, "git-k8s@example.com")
	repository := func() *gitk8s.Repository {
		r := &gitk8s.Repository{Object: kube.Meta("app", nil), Spec: gitk8s.GitRepositorySpec{URL: "http://git.example.com/app.git"}}
		r.Namespace = "default"
		return r
	}
	secret := func(data map[string][]byte) *k8s.Secret {
		s := &k8s.Secret{Object: kube.Meta("app-signing", nil), Data: data}
		s.Namespace = "default"
		return s
	}

	repo := repository()
	ctx, _ := kube.Fake(t.Context(), repo)
	if key, err := signing.Key(ctx, repo); key != nil || err != nil {
		t.Errorf("Key without signingKeyRef = %v, %v; want nil, nil", key, err)
	}

	for _, tc := range []struct {
		name  string
		world []any
		err   string
	}{
		{"missing", nil, "Secret app-signing doesn't exist"},
		{"no key", []any{secret(map[string][]byte{"username": []byte("git")})}, "Secret app-signing has no ssh-privatekey key"},
		{"not a key", []any{secret(map[string][]byte{"ssh-privatekey": []byte("hunter2")})}, "Secret app-signing: the key isn't a private key in OpenSSH format"},
	} {
		repo := repository()
		repo.Spec.SigningKeyRef = &gitk8s.SecretRef{Name: "app-signing"}
		ctx, _ := kube.Fake(t.Context(), repo, tc.world...)
		key, err := signing.Key(ctx, repo)
		if key != nil || err == nil || !strings.Contains(err.Error(), tc.err) || strings.Contains(err.Error(), "hunter2") {
			t.Errorf("%s: Key = %v, %v; want an error that says %q", tc.name, key, err, tc.err)
		}
	}

	repo = repository()
	repo.Spec.SigningKeyRef = &gitk8s.SecretRef{Name: "app-signing"}
	ctx, _ = kube.Fake(t.Context(), repo, secret(map[string][]byte{"ssh-privatekey": signer.Key}))
	if key, err := signing.Key(ctx, repo); key == nil || err != nil {
		t.Errorf("Key = %v, %v; want the key", key, err)
	}

	repo.Spec.SecretRef = &gitk8s.SecretRef{Name: "app-signing"}
	if key, err := signing.Key(ctx, repo); key != nil || err == nil || !strings.Contains(err.Error(), "put the signing key in a Secret of its own") {
		t.Errorf("Key with secretRef and signingKeyRef naming the same Secret = %v, %v; want an error that says to use separate Secrets", key, err)
	}
}

// TestOnlyCommitMakersImport checks that only the programs that make commits
// link this package. Add a program here only if it makes commits.
func TestOnlyCommitMakersImport(t *testing.T) {
	const pkg = "github.com/imjasonh/playground/git-k8s/signing"
	out, err := exec.Command("go", "list", "-f", "{{.ImportPath}} {{join .Deps \" \"}}", "../cmd/...").Output()
	if err != nil {
		t.Fatalf("go list: %v", err)
	}
	var got []string
	for line := range strings.Lines(string(out)) {
		fields := strings.Fields(line)
		if len(fields) > 0 && slices.Contains(fields[1:], pkg) {
			got = append(got, path.Base(fields[0]))
		}
	}
	if want := []string{"check-base", "check-gofmt", "check-review", "git-k8s"}; !slices.Equal(got, want) {
		t.Errorf("programs that import %s = %v, want %v", pkg, got, want)
	}
}
