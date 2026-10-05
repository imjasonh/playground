// Package credentials reads the URL and credentials of an external
// repository, or gets a GitHub token for it from Octo STS.
//
// Reading the Secret makes kube's generate grant a program get access to
// Secrets in every namespace, and exchanging tokens makes it grant the
// program permission to request tokens for its own service account, because
// generate grants what a program's packages call. Only the core program
// imports this package, for the mirror and for check runs, so checks never
// get that access.
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
// that SecretRef names with kube.Fetch, or exchanges a token for the
// program's service account for a token for OctoSTS.GitIdentity, so it must
// run in a reconcile. The Secret isn't cached, and the GitHub token is
// cached until shortly before it expires.
func Remote(ctx context.Context, repo *gitk8s.Repository) (git.Remote, error) {
	if sts := repo.Spec.OctoSTS; sts != nil && sts.GitIdentity != "" {
		return octoSTSRemote(ctx, repo)
	}
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
