// Package credentials reads the URL and credentials of an external
// repository, for the mirror.
//
// Reading the Secret makes kube's generate grant a program get access to
// Secrets in every namespace, because generate grants what a program's
// packages call. The mirror is the only part of git-k8s that reaches
// external repositories, so only the core program imports this package, and
// checks never get that access.
package credentials

import (
	"context"
	"fmt"

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
	if repo.Spec.SecretRef == nil {
		return r, nil
	}
	name := repo.Spec.SecretRef.Name
	s, err := kube.Fetch[k8s.Secret](ctx, repo.Namespace, name)
	if err != nil {
		return r, fmt.Errorf("reading Secret %s: %w", name, err)
	}
	if s == nil {
		return r, fmt.Errorf("Secret %s doesn't exist", name)
	}
	password := string(s.Data["password"])
	if password == "" {
		return r, fmt.Errorf("Secret %s has no password key", name)
	}
	username := string(s.Data["username"])
	if username == "" {
		username = "git"
	}
	r.Auth = &git.Auth{Username: username, Password: password}
	return r, nil
}
