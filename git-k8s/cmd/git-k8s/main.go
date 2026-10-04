// Command git-k8s runs the core git-k8s controllers and the mirror.
//
// The mirror keeps a copy of each GitRepository on a persistent volume and
// serves it over git's smart HTTP protocol. Checks fetch from it and push
// fixes to it, and it refuses the pushes that their merge policies don't
// allow.
//
// The repositories controller syncs each copy with the external repository
// and owns a GitBranch for every branch that the repository's rules select,
// and a NetworkPolicy that limits what check-gotest's test Pods in the
// repository's namespace can reach. The merge controller reads the check
// results on each GitBranch, and when the parent's merge policy passes,
// fast-forwards the parent to the branch.
//
// Check controllers run as separate programs, such as check-gofmt.
package main

import (
	"flag"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/mirror"
	"github.com/imjasonh/playground/kube"
)

// mirrorDir is where the installation mounts the mirror's volume.
const mirrorDir = "/var/lib/git-k8s"

func main() {
	g := &git.Git{}
	m := &mirror.Mirror{Git: g}
	flag.StringVar(&g.Bin, "git", "git", "git executable")
	flag.StringVar(&m.Dir, "mirror-dir", mirrorDir, "writable directory for the mirror's copies of repositories, which one process at a time may use")
	flag.Func("branch-prefix", "let a controller start branches, as NAMESPACE/SERVICEACCOUNT=PREFIX, such as git-k8s-deps/git-k8s-deps=deps/; repeat for more", func(s string) error {
		p, err := mirror.ParsePrefix(s)
		if err != nil {
			return err
		}
		m.Prefixes = append(m.Prefixes, p)
		return nil
	})
	kube.Main(
		kube.For[gitk8s.GitRepository](&repositories{mirror: m}, kube.Named("repositories")),
		kube.For[gitk8s.GitBranch](&merger{mirror: m}, kube.Named("merge")),
		kube.Serve(m),
		kube.Volume(mirrorDir),
	)
}
