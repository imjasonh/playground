// Command git-k8s runs the core git-k8s controllers.
//
// The repositories controller lists each GitRepository's branches with git
// ls-remote and owns a GitBranch for every branch that the repository's
// rules select. The merge controller reads the check results on each
// GitBranch, and when the parent's merge policy passes, fast-forwards the
// parent to the branch. Unless -install-policies=false, the program installs
// the admission policies in config/policy.yaml when it starts.
//
// Check controllers run as separate programs, such as check-gofmt.
package main

import (
	"flag"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/config"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/kube"
)

func main() {
	g := &git.Git{}
	cache := &gitk8s.Cache{Git: g}
	repos := &repositories{git: g}
	flag.StringVar(&g.Bin, "git", "git", "git executable")
	flag.StringVar(&cache.Dir, "cache-dir", gitk8s.DefaultCacheDir, "writable directory for local copies of repositories")
	flag.BoolVar(&repos.installPolicies, "install-policies", true, "install the admission policies in config/policy.yaml when the program starts")
	kube.Main(
		kube.Install(func() []byte {
			if !repos.installPolicies {
				return nil
			}
			return config.Policy
		}),
		kube.For[gitk8s.GitRepository](repos, kube.Named("repositories")),
		kube.For[gitk8s.GitBranch](&merger{cache: cache}, kube.Named("merge")),
	)
}
