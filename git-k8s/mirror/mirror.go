// Package mirror reaches a repository's copy on the mirror, the git server in
// the core program, from other programs such as checks.
//
// Remote asks kube.RequestToken for a token whose audience is the constant
// gitk8s.MirrorAudience, so kube's generate mounts a token for the mirror in
// the Pods of each program that imports this package. Only the programs that
// fetch from or push to a repository import it, so the others get no token.
package mirror

import (
	"context"
	"flag"
	"fmt"
	"strings"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/kube"
)

var base = flag.String("mirror", gitk8s.MirrorURL, "base URL of the git-k8s mirror")

// Remote returns the URL of a repository's copy on the mirror, from the
// -mirror flag, and a token that the mirror accepts. It needs a kube
// context, such as a reconcile's.
func Remote(ctx context.Context, repo *gitk8s.RepositoryView) (git.Remote, error) {
	token, _, err := kube.RequestToken(ctx, gitk8s.MirrorAudience)
	if err != nil {
		return git.Remote{}, fmt.Errorf("getting a token for the mirror: %w", err)
	}
	url := strings.TrimSuffix(*base, "/") + gitk8s.MirrorPath(repo.Namespace, repo.Name)
	return git.Remote{URL: url, Auth: &git.Auth{Token: token}}, nil
}
