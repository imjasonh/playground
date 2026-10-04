# git-k8s

git-k8s runs a branch workflow on Kubernetes. It tracks a remote git
repository's branches as `GitBranch` objects and runs checks on branches
that propose changes to another branch. Checks can push commits that fix
what they find. When the parent's merge policy passes, git-k8s fast-forwards
the parent to the branch.

It's a rewrite of [imjasonh/git-k8s](https://github.com/imjasonh/git-k8s)
on [`kube`](../kube/), the controller framework in this repository. The
module imports `kube` at head with `replace github.com/imjasonh/playground/kube => ../kube`.

## How it works

You write a `GitRepository`:

```yaml
apiVersion: git-k8s.imjasonh.com/v1alpha1
kind: GitRepository
metadata:
  name: app
spec:
  url: https://git.example.com/app.git
  secretRef:
    name: app-creds         # username and password keys, for HTTP basic auth
  pollInterval: 30s
  branches:
    - match: main
      merge:
        checks:
          - name: base
            mayPush: true
          - name: gofmt
            mayPush: true
          - name: risk
          - name: approval
        when: >-
          checks.base.passed && checks.gofmt.passed &&
          (checks.risk.outputs.level == "low" || checks.approval.passed)
        deleteMergedBranches: true
    - match: c/**
      parent: main
```

For each remote branch, the first rule whose `match` glob matches applies,
and branches that match no rule aren't tracked. A branch whose rule names a
`parent` is a proposal to that parent. The parent's rule says what a proposal
needs before it lands.

The `git-k8s` program runs two controllers, and each check runs as its own
program. Each controller is a `kube.For` reconciler:

- The **repositories** controller lists each repository's branches with
  `git ls-remote` and declares a `GitBranch` for each tracked branch with
  `kube.Own`. The spec holds the branch's head, its parent's head, and the
  parent's merge policy. When a branch disappears from the remote, kube
  deletes its `GitBranch`, because the reconcile stops declaring it. A remote
  can't be watched, so the controller asks to run again after `pollInterval`.
- Each **check** controller is its own program. It reconciles `GitBranch`
  objects through a view type that declares only the check's own entry in
  `status.checks`. kube writes the view's status with server-side apply, so
  each check manages one map key and never sees or rewrites another check's
  result. Results record the commits they're for, and the merge controller
  ignores results for older commits.
- The **merge** controller evaluates the merge policy's `when` expression
  over the fresh results. When it passes, the controller fast-forwards the
  parent with `git push --force-with-lease`, so a parent that moved in the
  meantime is never overwritten. It then deletes the branch if the policy
  says to.

The checks and the merge controller read each branch's repository as a
`gitk8s.Repository`, a `GitRepository` without its status, so the
repositories controller's status writes don't run them again.

Git objects stay in local bare repositories, one for each `GitRepository`
in each program. Only commit SHAs go into Kubernetes objects, and no object
records a single push or check run, so the API server holds a bounded amount
of state.

After a branch lands, `kubectl get gitbranches` shows what's still open:

```
NAME                    BRANCH   HEAD                                       PARENT   STATE              AGE
app-c-auth-f684729ccf   c/auth   d28547a6c959905ea8dc037ac37541167a50638c   main     WaitingForChecks   9s
app-main-9157892a7c     main     610a7734a0b4d1bc1991a669d9feb35fd159219b                               48s
```

The `Merged` condition's message explains a `WaitingForChecks` state, for
example `checks: approval Failed, base Passed, gofmt Passed, risk Passed (high)`.

## Checks

| Program | Check | What it does |
| --- | --- | --- |
| `check-base` | `base` | Passes when the branch contains its parent's head, or the parent already contains the branch. Otherwise it merges the parent in with `git merge-tree`, and fails with the conflicting paths if the merge conflicts. |
| `check-gofmt` | `gofmt` | Formats every `.go` file outside `vendor` and `testdata` directories with `go/format`, and passes when nothing changes. |
| `check-risk` | `risk` | Always passes, and sets `outputs.level` to `high` when the change is larger than `-max-lines` or touches a path that matches a `-sensitive` glob, and to `low` otherwise. |
| `check-approval` | `approval` | Passes when the `git-k8s.imjasonh.com/approve` annotation on the `GitBranch` names the branch's head. A push after the approval needs a new one. |
| `check-gotest` | `gotest` | Runs `go test ./...` in a Pod that it declares with `kube.Own`, and fails with the end of the test output. See [Sandboxed checks](#sandboxed-checks). |

A check with `mayPush: true` pushes its fix commit to the branch, which moves
the head and runs the checks again. Fix commits have a `Git-K8s-Fixer:
CHECK` trailer, and `maxAutomatedCommits` (default 5) limits how many a
branch can have, so two checks that undo each other's fixes stop. The same
inputs always produce the same fix commit, so two retries of one fix push the
same commit.

To approve a branch:

```sh
kubectl annotate gitbranch GITBRANCH git-k8s.imjasonh.com/approve=SHA
```

### Write a check

A check is a `checks.Check` and a view type that names its key in
`status.checks`. This `main` package, next to the others in `cmd/`, is a
complete check that fails branches without a `README.md`:

```go
type Branch struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=GitBranch,plural=gitbranches,scope=Namespaced"`
	Spec        gitk8s.GitBranchSpec `json:"spec"`
	Status      struct {
		Checks struct {
			Result *gitk8s.CheckResult `json:"readme,omitempty"`
		} `json:"checks,omitzero"`
	} `json:"status,omitzero"`
}

func (b *Branch) Parts() (*kube.ObjectMeta, *gitk8s.GitBranchSpec, **gitk8s.CheckResult) {
	return &b.ObjectMeta, &b.Spec, &b.Status.Checks.Result
}

func run(ctx context.Context, in *checks.Input) (checks.Verdict, error) {
	repo, err := in.Repo(ctx)
	if err != nil {
		return checks.Verdict{}, err
	}
	files, err := repo.LsTree(ctx, in.Spec.Head)
	if err != nil {
		return checks.Verdict{}, err
	}
	for _, f := range files {
		if f.Path == "README.md" {
			return checks.Pass("has a README.md"), nil
		}
	}
	return checks.Fail("needs a README.md"), nil
}

func main() {
	checks.Main[Branch](checks.Check{Name: "readme", Remote: credentials.Remote, Run: run})
}
```

`in.Repo` fetches the branch and its parent into the program's local
repository. A verdict with a `Fix` commit asks the framework to push it.
Both need `Remote: credentials.Remote`, which reads the repository's
Secret. `generate` grants a program what its packages call, so a check that
reads only the `GitBranch`, such as `check-approval`, leaves `Remote` out,
and its program can't read Secrets.

### Sandboxed checks

The checks that read files run in their controller's process. A check that
runs the branch's code, such as `go test`, runs it in a Pod instead.
`check-gotest` declares one Pod for each head with `kube.Own`, and reports
`Running` until the Pod finishes:

- An init container fetches the head from the repository. It's the only
  container that gets the repository's credentials, as environment
  variables from the Secret.
- The test container runs `go test ./...` as user 65532 with no service
  account token, no privileges, and a read-only root file system. It has
  `GOPROXY=off`, so tests can't download modules, unless you
  [share modules and build outputs](#share-modules-and-build-outputs).
- If fetching fails, the check starts a new Pod, up to three times.
- At most `-max-pods` test Pods, 10 by default, run at once across all
  namespaces. A branch that would start another reports `Running` and waits
  until one finishes.

kube deletes a Pod when the check stops declaring it: after the check records
the Pod's result, or when the branch moves to a new head. Owner references
delete the Pods with their `GitBranch`. Set `-runtime-class` to run the Pods
under a sandboxing runtime such as gVisor, and `-go-image`, `-git-image`,
`-timeout`, and `-goproxy` to change the rest.

### Share modules and build outputs

Each test Pod starts with an empty Go build cache, so it compiles every
package that its tests use, including the standard library's. With
`GOPROXY=off`, it also can't test a module that has dependencies.
`go-cache`, a program in this module, fixes both for the test Pods that use
it:

- Its module proxy, at `/mod/`, fetches modules from `-upstream`,
  `https://proxy.golang.org` by default, and keeps each version's files,
  which never change. Test Pods download modules from it, so they don't
  need the internet.
- Its build caches, one at `/cache/NAMESPACE/REPOSITORY/` for each
  `GitRepository`, hold what the go command compiled, by action ID. The go
  command derives an action ID from everything that goes into a build step,
  such as the source files, the compiler and its flags, and the step's
  dependencies.

Install `go-cache` with `generate`, apply `config/go-cache.yaml`, and set
`check-gotest`'s `-go-cache` flag to `go-cache`'s URL:

```sh
go run ./cmd/go-cache generate -registry=REGISTRY \
  -base=cgr.dev/chainguard/static:latest -replicas=1 -tmp-size=10Gi \
  -- -max-size=8Gi | kubectl apply -f -
kubectl apply -f config/go-cache.yaml
go run ./cmd/check-gotest generate -registry=REGISTRY \
  -base=cgr.dev/chainguard/git:latest \
  -- -go-cache=http://go-cache.go-cache | kubectl apply -f -
```

`go-cache` keeps modules and build outputs on the `emptyDir` volume at
`/tmp`, and keeps their total size, with the writes in progress, under
`-max-size`, 4Gi by default. Before it writes a file, `go-cache` reserves
room for it, and removes the least recently used files to make room. It
writes at most 16 uploads at once, and at most 16 fetched modules in
slots of their own. When writes in progress hold the room, or fetches
hold all 16 fetch slots, `go-cache` serves a module that it doesn't have
from `-upstream` without keeping it. When writes in progress hold the
room, or uploads hold all 16 upload slots, `go-cache` answers an upload
with `503 Service Unavailable`. An upload waits up to 30 seconds for a
slot first. After a 503, the test Pod stops uploading, which only means that
later Pods compile those outputs again. `go-cache` doesn't keep build
outputs larger than 256 MiB. The kubelet evicts a Pod whose volume passes
`-tmp-size`, so keep `-max-size` a little below it.
Each replica would have its own store, so `-replicas=1` runs one. The
volume survives restarts of `go-cache`'s container, but a new Pod, such as
one that replaces a deleted or evicted Pod, starts with an empty store.
That costs test Pods only the time to download and compile again.

`generate` can't make what `config/go-cache.yaml` holds. It makes Services
only for webhooks, so the file adds the Service that test Pods reach
`go-cache` through. `generate` grants what a program calls through kube,
and `go-cache` sends TokenReviews to the API server itself, so the file
adds a ClusterRole that allows creating TokenReviews and nothing else.

With `-go-cache`, `check-gotest` adds three init containers to each test
Pod, after the one that fetches the head:

1. `cacheprog` runs `check-gotest`'s own image, which `generate` names in
   the `KUBE_IMAGE` environment variable, and copies the `check-gotest`
   binary to a volume. The binary is the Pod's `GOCACHEPROG`, the program
   that the go command asks for build outputs.
2. `build` runs the `check-gotest` binary from the volume in the Go image,
   with the test container's environment. It lists the packages that
   `go test` needs, and compiles the ones from GOROOT and the module cache
   with `go list -export`, which neither links nor runs anything. Its
   `GOCACHEPROG` reads outputs from the repository's build cache, with a
   service account token that can only read it.
3. `upload` sends what `build` compiled to the build cache, with a token
   that can write to it. It runs `check-gotest`'s image, and doesn't mount
   the branch's files.

Test Pods run in the `GitBranch`'s namespace as its `default` service
account and don't set `imagePullSecrets`, so each namespace that has a
`GitRepository` must be able to pull `check-gotest`'s image. If pulling
from `REGISTRY` needs credentials that the nodes don't have, add an image
pull secret to the `default` service account in each of those namespaces.
Without the secret, test Pods wait in `Init:ImagePullBackOff` until
`-timeout` ends them, and the check fails.

The test container downloads modules from `go-cache`, whatever `-goproxy`
says. Its `GOCACHEPROG` reads the outputs that `build` left in the volume,
and doesn't connect to `go-cache`. The test container compiles the
packages that `build` didn't, such as the module's own packages, vendored
packages, and modules that a `replace` directive points at a directory. It
also links the test binaries and runs the `go vet` checks that `go test`
runs. Test results stay in the Pod, so every test runs. If the go command
fails in `build`, for example because `go.mod` doesn't parse, the check
fails with its output. If `go-cache` is down, test Pods compile everything
themselves, but can't download modules.

#### Threat model

Test Pods run untrusted code. Anyone who can push a branch controls its
tests and the packages that they import. A shared build cache must not let
that code change what another branch's Pod compiles, which could, for
example, make a failing test on `main` pass. `go-cache` and `check-gotest`
defend against that as follows:

- Only what the go command compiles goes into the build cache. `build`
  reads the branch's `go.mod`, `go.sum`, and imports, compiles packages
  from GOROOT and the module cache, and runs nothing. `check-gotest` sets
  `CGO_ENABLED=0` and `GOTOOLCHAIN=local`, so the go command runs no C
  compiler and no toolchain that the branch asks for. `upload` sends only
  what `build` compiled, before any of the branch's code runs.
- Test code can't write to the build cache. The test container gets no
  token, and its `GOCACHEPROG` doesn't connect to `go-cache`. Nothing
  uploads after the tests start.
- Only outputs that no branch can change are shared. An action ID covers
  the files that the go command lists for a package, but not every file
  that a build step reads. An assembly file can include a header from
  another directory, so two branches can compile different outputs for one
  action ID. `build` shares a package's outputs only when the package is in
  GOROOT, which the Go image fixes, or in the module cache, where the go
  command puts a module only after checking it against `go.sum`. The
  package's assembly must include no file from outside its directory, and
  every package that it imports must be shared too. The test container
  compiles the rest itself, so a branch can't change what another branch's
  Pod compiles. `go-cache` never replaces an entry, and answers an upload
  of another output for an action ID that it has with `409 Conflict`.
- Tokens name a repository and an access. Each token is a projected service
  account token whose audience names the namespace, the repository, and
  either reading or writing. It expires after 10 minutes, the shortest
  lifetime that Kubernetes allows. `go-cache` checks each request's token
  with a TokenReview for the audience that the request needs, and checks
  that the token's service account is in the namespace in the URL.
- The namespace is the trust boundary. Anyone who can create Pods in a
  namespace can get a token for any audience, so they can write the build
  caches of the namespace's repositories. They can already mount the
  namespace's Secrets, including the repositories' credentials, so the
  build cache doesn't let them do more. Namespaces don't share build
  caches.

The design leaves these risks:

- The defense relies on the go command not running code from the files
  that it reads. A bug that let a branch run code in `build` would let it
  store any output under action IDs that the build cache doesn't have yet.
- Sharing relies on action IDs covering every input but the files that
  assembly includes. If a Go release let another build step read files
  from outside a package's directory, `build` would have to leave out the
  packages that do.
- The module proxy doesn't check tokens. Any Pod that can reach `go-cache`
  can download modules, and make `go-cache` fetch a module from
  `-upstream`. The go command checks each module that it downloads against
  `go.sum`, so a changed module fails the build. `proxy.golang.org` fetches
  a module that it doesn't have from its origin, so a test can send data
  out in module paths. If that matters, set `-upstream` to a proxy that
  serves only the modules that you allow.
- `go-cache` serves plain HTTP. Anyone who can watch the Pod network can
  read build outputs, and use a token that writes until it expires.
- `go-cache` remembers a token's review for a minute, so a token works for
  up to a minute after its Pod is deleted. It denies a token that isn't a
  JWT for the request's audience without a TokenReview, remembers denials
  apart from the tokens that it accepts, and sends at most 8 TokenReviews
  at once. A flood of bad tokens can hold up reviews of new tokens, but
  not requests with tokens that it accepted in the last minute.
- A namespace can fill the store and push other namespaces' entries out,
  which slows their builds. Its tokens can name any repository, even one
  that doesn't exist, so it can write as many entries as it likes.
  Eviction doesn't change results, because a Pod that compiles an evicted
  output again compiles the same output.
- A write holds its room in the store until it ends. A namespace that
  uploads slowly can take all 16 upload slots for up to 5 minutes,
  `go-cache`'s read timeout, and hold up to 256 MiB of room with each,
  4Gi in all. Meanwhile `go-cache` answers other uploads with 503. Module
  fetches have slots of their own, but the uploads can hold all of the
  default `-max-size` of 4Gi, and then `go-cache` serves modules that it
  doesn't have without keeping them. That slows other namespaces' test
  Pods, but doesn't fail them. A `-max-size` above 4Gi leaves room for
  modules.

### Restrict test Pods' network

`check-gotest` doesn't add a NetworkPolicy, so a test can reach anything
that the namespace's Pods can, including the internet. A test Pod needs to
reach only DNS, the git remote, and `go-cache`, if you use it. This
NetworkPolicy, in each namespace that has a `GitRepository`, allows that
and nothing else:

```yaml
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: test-pods
  namespace: NAMESPACE
spec:
  podSelector:
    matchLabels:
      app.kubernetes.io/name: check-gotest
  policyTypes: [Ingress, Egress]
  egress:
    - to:
        - namespaceSelector:
            matchLabels:
              kubernetes.io/metadata.name: kube-system
          podSelector:
            matchLabels:
              k8s-app: kube-dns
      ports:
        - {protocol: UDP, port: 53}
        - {protocol: TCP, port: 53}
    - to:
        - namespaceSelector:
            matchLabels:
              kubernetes.io/metadata.name: go-cache
          podSelector:
            matchLabels:
              app.kubernetes.io/name: go-cache
      ports:
        - {protocol: TCP, port: 8080}
    - to:
        - ipBlock:
            cidr: GIT_REMOTE_IP/32
      ports:
        - {protocol: TCP, port: 443}
```

Replace `NAMESPACE`, and replace `GIT_REMOTE_IP` and `443` with the git
remote's address and port. A remote whose address changes needs a wider
block. Leave out the `go-cache` rule if you don't use it, and change the
DNS rule if your cluster's DNS Pods have other labels. NetworkPolicies
match the port that a Service forwards to, so the `go-cache` rule allows
port 8080, which `go-cache` listens on, instead of the Service's port 80.

The policy applies to the whole Pod, and the init container that fetches
the head needs the remote, so tests can reach the remote too, without the
credentials. A NetworkPolicy has no effect unless the cluster's network
plugin enforces NetworkPolicies. The end-to-end test applies this policy,
and reports whether the cluster enforced it.

## Merge gates

`when` is a [CEL](https://cel.dev) expression. It has one variable,
`checks`, which maps each check that the policy lists to an object with
`passed` (bool), `state` (string), and `outputs` (map of strings). A check
without a result for the branch's current commits has state `Pending`. All of
CEL works, for example `int(checks.risk.outputs.lines) < 500` or
`checks.all(c, checks[c].passed)`. In CEL, `&&` and `||` give a result when
one side decides it, even if the other side is an error, such as a missing
output. Without `when`, every listed check must pass.

The repository controller compiles each `when` when it reads the
`GitRepository`, so a syntax error or a misspelled field, such as
`checks.gofmt.pased`, makes the `GitRepository` not `Ready` instead of
holding branches back later. Each evaluation can cost at most 100,000, which
stops an expression that loops over the checks many times.

## Install

Each program installs with kube's `generate` command, which builds an image,
pushes it, and writes the YAML for its namespace, service account, RBAC
rules, and Deployment. The programs run `git`, so build them on an image
that has it. They keep local copies of repositories in `/tmp/git-k8s`, on
the `emptyDir` volume that `generate` mounts at `/tmp`:

```sh
for program in git-k8s check-base check-gofmt check-risk check-approval check-gotest; do
  go run "./cmd/${program}" generate -registry=REGISTRY -base=cgr.dev/chainguard/git:latest | kubectl apply -f -
done
kubectl apply -f config/policy.yaml
```

Replace `REGISTRY` with a registry and repository prefix that your cluster
can pull from, such as `ghcr.io/you`. To pass flags to a program, add them
after `--`, as in `go run ./cmd/check-risk generate -registry=REGISTRY -- -sensitive='auth/**'`.
To give test Pods a module proxy and a shared build cache, also install
`go-cache`. [Share modules and build outputs](#share-modules-and-build-outputs)
shows how.

`config/policy.yaml` holds two ValidatingAdmissionPolicies. The first lets
the service account of `check-NAME` change only `status.checks.NAME`, and
stops every other service account, including the core program's, from
changing `status.checks`. A check must run as the service account
`check-NAME` in the namespace `check-NAME`, as `generate` installs it, to
write results. Server-side apply already keeps the controllers' writes
apart; the policy stops a buggy or compromised check from writing another
check's result. The second stops every git-k8s service account from setting
the approve annotation, which is for people, and stops checks from changing
`GitBranch` objects at all.

Without the policies, none of that holds, so the repositories controller
sets a `PoliciesInstalled` condition on each `GitRepository`. It's `False`
until both policies are installed with bindings that deny.

## Test

The unit tests call each reconciler with `kube.Fake` and a real git server
that runs in the test process:

```sh
go test -race ./...
```

The end-to-end test installs every program with `generate` in a
[kind](https://kind.sigs.k8s.io/) cluster with a local registry. It runs a
git server on this machine, which Pods reach through the kind network's
gateway, and pushes branches to it. A module proxy on this machine serves
`go-cache` a module that isn't on the internet. The test reads `go-cache`'s
metrics to check that a test Pod got the module through it, and that a later
Pod read its build outputs instead of compiling them. The test needs Docker,
`kubectl`, and `git`, and installs kind if it's missing:

```sh
GIT_K8S_KIND_E2E=1 go test -v -count=1 ./e2e/kind/
```

CI runs it when `git-k8s/` or `kube/` changes. To keep the cluster
afterward, set `GIT_K8S_KIND_KEEP=1`. If your network can't reach `cgr.dev`,
set `GIT_K8S_KIND_CHAINGUARD=docker.io/chainguard`.

## Limitations

- The controllers poll remotes; they don't receive webhooks. A check's status
  write runs the repositories controller again, so a check's fix is listed
  soon after the check pushes it. The controller lists a repository at most
  once every 5 seconds, or every `pollInterval` if that's shorter.
- Remotes authenticate with HTTP basic auth only.
- `check-gotest` runs Pods in the `GitBranch`'s namespace and doesn't add a
  NetworkPolicy, so a test can reach anything that the namespace's Pods can
  until you [add one](#restrict-test-pods-network).

[`future-work.md`](future-work.md) proposes fixes for these, and lists the
other known gaps.
