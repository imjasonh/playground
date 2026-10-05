// Command git-k8s runs the core git-k8s controllers, the mirror, and the
// results endpoint.
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
// lands the branch on the parent in the copy. It fast-forwards the parent
// to the branch, or squashes or rebases the branch onto the parent.
//
// The check-runs controller copies the check results on each GitBranch to
// GitHub as check runs, for repositories that name an Octo STS identity for
// them.
//
// Unless -install-policies=false, the program installs the admission policies
// in config/policy.yaml when it starts.
//
// Check controllers run as separate programs, such as check-gofmt. They
// send their results to this program's results endpoint, and the results
// controller writes each one to the entry of the check whose token sent it.
// The results endpoint and the mirror share the program's HTTP server, and
// each accepts only tokens for its own audience.
package main

import (
	"flag"
	"log/slog"
	"net/http"
	"os"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/config"
	"github.com/imjasonh/playground/git-k8s/internal/caller"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/mirror"
	"github.com/imjasonh/playground/kube"
)

// mirrorDir is where the installation mounts the mirror's volume.
const mirrorDir = "/var/lib/git-k8s"

func main() {
	g := &git.Git{}
	checks := &caller.Checks{}
	m := &mirror.Mirror{Git: g, Checks: checks}
	repos := &repositories{mirror: m}
	merge := &merger{mirror: m}
	rs := &results{timeout: 10 * time.Second, poll: 100 * time.Millisecond, checks: checks}
	flag.StringVar(&g.Bin, "git", "git", "git executable")
	flag.StringVar(&m.Dir, "mirror-dir", mirrorDir, "writable directory for the mirror's copies of repositories, which one process at a time may use")
	flag.StringVar(&merge.ident.Name, "identity-name", "git-k8s", "committer name of the commits that squash and rebase landings make")
	flag.StringVar(&merge.ident.Email, "identity-email", "git-k8s@users.noreply.github.com", "committer email of the commits that squash and rebase landings make")
	flag.BoolVar(&repos.installPolicies, "install-policies", true, "install the admission policies in config/policy.yaml when the program starts")
	flag.Func("branch-prefix", "let a controller start branches, as NAMESPACE/SERVICEACCOUNT=PREFIX, such as git-k8s-deps/git-k8s-deps=deps/; repeat for more", func(s string) error {
		p, err := mirror.ParsePrefix(s)
		if err != nil {
			return err
		}
		m.Prefixes = append(m.Prefixes, p)
		return nil
	})
	// A container that's killed while a landing signs a commit leaves the
	// key in os.TempDir, which generate puts on a volume that outlives the
	// container. Outside a Pod, as in generate or a run with -kubeconfig,
	// other processes can be signing in the same directory.
	if os.Getenv("KUBERNETES_SERVICE_HOST") != "" {
		if err := git.RemoveSigningKeys(); err != nil {
			slog.Warn("removing signing keys that an earlier run left", "err", err)
		}
	}
	kube.Main(
		kube.Install(func() []byte {
			if !repos.installPolicies {
				return nil
			}
			return config.Policy
		}),
		kube.For[gitk8s.GitRepository](repos, kube.Named("repositories")),
		kube.For[gitk8s.GitBranch](merge, kube.Named("merge")),
		kube.For[resultsBranch](rs, kube.Named("results")),
		kube.For[branchResults](&checkRuns{}, kube.Named("check-runs")),
		kube.Serve(serve(m, rs)),
		kube.Volume(mirrorDir),
	)
}

// serve routes check results to the results endpoint and every other
// request to the mirror, because a program serves one handler. git's smart
// HTTP protocol sends no PUT requests, so the mirror still serves a
// repository in a namespace named results.
func serve(m http.Handler, rs *results) http.Handler {
	mux := http.NewServeMux()
	mux.Handle("PUT /results/", rs.handler())
	mux.Handle("/", m)
	return mux
}
