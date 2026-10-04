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

The `git-k8s` program runs three controllers, and each check runs as its own
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

The `git-k8s` program's third controller, **check-runs**, copies check
results to GitHub as check runs. See [Check runs](#check-runs).

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

## GitHub repositories

For a repository on github.com, a `GitRepository` can name
[Octo STS](https://github.com/octo-sts/app) identities instead of a Secret:

```yaml
spec:
  url: https://github.com/OWNER/REPO.git
  octoSTS:
    gitIdentity: git-k8s              # instead of secretRef
    checkRunsIdentity: git-k8s-checks
```

Octo STS exchanges a Kubernetes service account token for a GitHub token
that works for one repository, expires within an hour, and has the
permissions that a trust policy in the repository grants. Each identity is
the name of a trust policy, `.github/chainguard/IDENTITY.sts.yaml`, on the
repository's default branch. git-k8s uses the public Octo STS service at
`https://octo-sts.dev`, which issues tokens only for github.com, so a
repository on GitHub Enterprise Server needs a `secretRef`.

`gitIdentity` replaces `secretRef`, so set only one of the two. The programs
that fetch or push use tokens for it: `git-k8s`, `check-base`, `check-gofmt`,
and `check-risk`. `check-gotest`'s test Pods fetch without credentials, so
with Octo STS, `gotest` works only for a public repository. The `git-k8s`
program publishes [check runs](#check-runs) with tokens for
`checkRunsIdentity`, and publishes none without it. The URL must have the
form `https://github.com/OWNER/REPO`, with or without `.git`.

### Set up Octo STS

1. Install the [Octo STS GitHub App](https://github.com/apps/octo-sts) on the
   repository's owner, with access to the repository.
2. Find the cluster's OIDC issuer, which is the `issuer` field in the output
   of this command:

   ```sh
   kubectl get --raw /.well-known/openid-configuration
   ```

   Octo STS downloads the issuer's discovery document and keys to verify
   tokens, so the issuer must be a public HTTPS URL, as it is on GKE and EKS.

3. On the repository's default branch, add a trust policy for each identity.
   For `gitIdentity: git-k8s`, add `.github/chainguard/git-k8s.sts.yaml`:

   ```yaml
   issuer: ISSUER
   subject_pattern: system:serviceaccount:(git-k8s:git-k8s|check-base:check-base|check-gofmt:check-gofmt|check-risk:check-risk)
   audience: octo-sts.dev/NAMESPACE
   permissions:
     contents: write
   ```

   For `checkRunsIdentity: git-k8s-checks`, add
   `.github/chainguard/git-k8s-checks.sts.yaml`:

   ```yaml
   issuer: ISSUER
   subject: system:serviceaccount:git-k8s:git-k8s
   audience: octo-sts.dev/NAMESPACE
   permissions:
     checks: write
   ```

   Replace the following:

   - `ISSUER`: the cluster's issuer
   - `NAMESPACE`: the `GitRepository`'s namespace

4. Apply the `GitRepository`.

A service account token's subject is `system:serviceaccount:NAMESPACE:NAME`.
When you install the programs with `generate`, as [Install](#install)
describes, each one runs as the service account with the program's name, in
the namespace with the same name. The trust policy in `git-k8s.sts.yaml`
lists the service account of every program that fetches or pushes. Octo STS
matches `subject_pattern` against the whole subject.

Each token's audience is `octo-sts.dev/` followed by the `GitRepository`'s
namespace. The programs use the same service accounts for every
`GitRepository`, so the audience is the part of a token that names the
namespace it's for. A trust policy that requires your namespace's audience
refuses the tokens that git-k8s requests for a `GitRepository` in another
namespace, even one that names your repository and identities. Without an
`audience`, a trust policy accepts only `octo-sts.dev`, which git-k8s never
requests.

`contents: write` lets the programs fetch and push. To land changes to files
in `.github/workflows`, also grant `workflows: write`, because GitHub refuses
a push that changes those files without it. `checks: write` lets the
`git-k8s` program create and update check runs.

The programs keep each GitHub token in memory and get a new one 10 minutes
before it expires. If an exchange fails, they use the old token until a
minute before it expires, and ask Octo STS again after 30 seconds. When the
`git-k8s` program can't get a token, the `GitRepository`'s `Ready` condition
is `False` with the reason `CredentialsUnavailable`. When a check can't, it
reports an `Error` result. Both messages include Octo STS's answer, such as
`unable to find trust policy for "git-k8s"`. Octo STS caches each trust
policy, and the lack of one, for 5 minutes, so a change to a trust policy can
take that long to apply.

### Check runs

When a `GitRepository` names a `checkRunsIdentity`, the `git-k8s` program's
check-runs controller copies each check's result to GitHub as a check run on
the commit that the result is for. GitHub shows a commit's check runs on the
commit and on its pull requests. Each check run is named `git-k8s/CHECK`,
after its check, and the controller updates it as the result changes:

- A `Running` result shows as in progress.
- `Passed` completes the check run as `success`.
- `Failed` and `Error` complete it as `failure`.
- `Fixed` completes it as `neutral`. The check pushed a fix commit, and the
  check run on that commit decides.

When a check starts again on a commit where it finished, the controller
creates a new check run with the same name, because GitHub doesn't support
starting a completed one again. GitHub shows the newest.

The check run's title is the result's state, its summary is the result's
message, and its text lists the result's outputs.

When a branch moves before a check finishes on its old head, the controller
completes the old commit's check run as `cancelled` when it publishes the
check's first result on the new head. The controller remembers its check
runs only in memory, so if the program restarts, or another replica takes
over the branch, between those two results, the old commit's check run stays
in progress. So does the check run of a check that's running when its branch
is deleted or its `GitRepository` loses its `checkRunsIdentity`. Branch
protection reads only the check runs on a pull request's head commit, so an
old commit's check run doesn't block a merge.

Check runs only copy results. The controller reads a check run only to see
whether it already shows the result, so nothing that happens on GitHub, such
as re-running a check run, changes a result or a merge. GitHub lets only the
app that created a check run update it, so the controller creates its own
beside a check run with the same name from another app. The controller
remembers what it wrote, and writes a check run again only when the result
changes or the program restarts, so a change that someone else makes to a
check run can stay until then.

GitHub limits the requests that each installation of a GitHub App can make.
When GitHub answers that the Octo STS app's installation reached its limit,
the controller stops publishing for that repository owner until the time
that GitHub gives, or for a minute. It logs other errors from GitHub and
tries again later. Neither holds back checks or landings. To show whether
the check-runs identity works, the repositories controller sets the
`CheckRunsTokenIssued` condition on the `GitRepository`, which is `False`
with Octo STS's answer when Octo STS doesn't issue a token. The
`GitRepository` stays `Ready` either way.

### Security

The programs keep GitHub tokens in memory and pass them to git in its
environment, so the tokens don't appear in process arguments, Kubernetes
objects, or logs. The service account tokens that the programs send to Octo
STS are bound to the programs' Pods. `generate` lets each program that
fetches or pushes request tokens for its own service account, and for no
other.

The programs send service account tokens only to Octo STS, and GitHub tokens
only to GitHub. For tests, the `-fake-github` flag points them at a fake
GitHub and Octo STS instead. It's a flag and not a `GitRepository` field, so
only whoever installs a program can choose where its tokens go. The
end-to-end test's git server runs such a fake, which checks each service
account token with a TokenReview, because Octo STS can't reach a kind
cluster's issuer.

A trust policy's audience ties it to one namespace, so anyone who can create
a `GitRepository` in that namespace can use the trust policy's permissions.
Grant that only to people who may push to the repository.

GitHub grants `contents: write` for a whole repository, not for branches.
Every program that fetches with `gitIdentity` can therefore push to any
branch, including the checks without `mayPush: true`.

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
  account token, no privileges, a read-only root file system, and
  `GOPROXY=off`, so tests can't download modules.
- If fetching fails, the check starts a new Pod, up to three times.
- At most `-max-pods` test Pods, 10 by default, run at once across all
  namespaces. A branch that would start another reports `Running` and waits
  until one finishes.

kube deletes a Pod when the check stops declaring it: after the check records
the Pod's result, or when the branch moves to a new head. Owner references
delete the Pods with their `GitBranch`. Set `-runtime-class` to run the Pods
under a sandboxing runtime such as gVisor, and `-go-image`, `-git-image`,
`-timeout`, and `-goproxy` to change the rest.

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
gateway, and pushes branches to it. It needs Docker, `kubectl`, and `git`,
and installs kind if it's missing:

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
  NetworkPolicy, so a test can reach anything that the namespace's Pods can.

[`future-work.md`](future-work.md) proposes fixes for these, and lists the
other known gaps.
