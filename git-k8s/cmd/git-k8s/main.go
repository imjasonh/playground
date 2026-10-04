// Command git-k8s runs the core git-k8s controllers.
//
// The repositories controller lists each GitRepository's branches with git
// ls-remote and owns a GitBranch for every branch that the repository's
// rules select. The merge controller reads the check results on each
// GitBranch, and when the parent's merge policy passes, fast-forwards the
// parent to the branch.
//
// Check controllers run as separate programs, such as check-gofmt. They
// send their results to this program's results endpoint, and the results
// controller writes each one to the entry of the check whose token sent it.
package main

import (
	"flag"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/kube"
)

func main() {
	g := &git.Git{}
	cache := &gitk8s.Cache{Git: g}
	rs := &results{timeout: 10 * time.Second, poll: 100 * time.Millisecond}
	flag.StringVar(&g.Bin, "git", "git", "git executable")
	flag.StringVar(&cache.Dir, "cache-dir", gitk8s.DefaultCacheDir, "writable directory for local copies of repositories")
	kube.Main(
		kube.For[gitk8s.GitRepository](&repositories{git: g}, kube.Named("repositories")),
		kube.For[gitk8s.GitBranch](&merger{cache: cache}, kube.Named("merge")),
		kube.For[resultsBranch](rs, kube.Named("results")),
		kube.Serve(rs.handler()),
	)
}
