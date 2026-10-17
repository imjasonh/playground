// Package signing reads the key that signs a repository's commits.
//
// As with the credentials package, reading the Secret makes kube's generate
// grant a program get access to every Secret in the namespaces that it
// watches. Only the programs that make commits import this package, so the
// others don't read the key. The checks among them reach repositories
// through the mirror, so this package is the only reason that they can read
// Secrets.
package signing

import (
	"context"
	"fmt"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

// Key returns the key that signs a repository's commits, or nil if the
// repository doesn't name one. It reads the Secret that SigningKeyRef names
// with kube.Fetch, so it must run in a reconcile, and the Secret isn't
// cached. It returns an error if SigningKeyRef names the SecretRef Secret.
func Key(ctx context.Context, repo *gitk8s.RepositoryView) (*git.SigningKey, error) {
	if repo.Spec.SigningKeyRef == nil {
		return nil, nil
	}
	name := repo.Spec.SigningKeyRef.Name
	if ref := repo.Spec.SecretRef; ref != nil && ref.Name == name {
		return nil, fmt.Errorf("signingKeyRef names Secret %s, which secretRef also names; put the signing key in a Secret of its own, so that the checks that sign commits never hold the external repository's credentials", name)
	}
	s, err := kube.Fetch[k8s.Secret](ctx, repo.Namespace, name)
	if err != nil {
		return nil, fmt.Errorf("reading Secret %s: %w", name, err)
	}
	if s == nil {
		return nil, fmt.Errorf("Secret %s doesn't exist", name)
	}
	data := s.Data["ssh-privatekey"]
	if len(data) == 0 {
		return nil, fmt.Errorf("Secret %s has no ssh-privatekey key", name)
	}
	key, err := git.NewSigningKey(data)
	if err != nil {
		return nil, fmt.Errorf("Secret %s: %w", name, err)
	}
	return key, nil
}
