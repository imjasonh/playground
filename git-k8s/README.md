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
creates a new check run with the same name instead of starting the
completed one again, which GitHub's documentation doesn't describe. GitHub
shows the newest, and the old one keeps its result.

A check run belongs to a commit, not to a branch. When two branches of a
`GitRepository` are at the same commit, they share the check run for each
check, and it shows the result that changed last, for either branch.

The check run's title is the result's state. Its summary is the result's
message, or the state when the result has no message, and its text lists the
result's outputs. The controller puts the message and the outputs in code
blocks, so GitHub shows what a check writes as it is, not as Markdown.

Check controllers don't finish a check on a commit that its branch left. So
when a branch moves, is deleted, or no longer has a result for a check
before the check finishes, the controller updates the check run on the
commit that the branch left. If another branch at that commit has a result
for the check, the check run shows it, or the one that changed last if
several do. Otherwise, the controller completes the check run as
`cancelled`. A completed check run doesn't start again or become
`cancelled`, so for another branch's result in progress, the controller
creates a new check run. Every change to one of a repository's branches
reconciles all of them, so this happens right away, unless the deleted
branch was the repository's last.

The controller keeps what it wrote only in memory. If the program restarts,
or another replica takes over, after a branch leaves a commit and before the
controller reconciles the change, the check run on that commit stays in
progress. So does a check run that's in progress when the last of a
repository's `GitBranch` objects is deleted or the `GitRepository` loses its
`checkRunsIdentity`. After a restart, the controller finds each branch's
check run on GitHub again, and writes the branch's result if the check run
shows something else. Until the controller learns its app, it writes the
result even to a check run that shows it, because the check run that it
finds can be another app's. Branch protection reads only the check runs on
a pull request's head commit, so a check run on a commit that no branch is
at doesn't block a merge.

The controller assumes that one replica of the `git-k8s` program reconciles
at a time, which is how `generate` installs it. With more than one replica,
`generate` runs the program with `-leader-elect`, so the replicas take
turns. Don't run `git-k8s` with `-shards`. Shards can split one repository's
branches across replicas, and each replica keeps its own record of the check
runs that the branches share. Then a check run can keep showing a result
that another branch's result replaced, or stay in progress after a branch
leaves its commit.

Check runs only copy results. The controller reads a check run only to see
whether it already shows the result, so nothing that happens on GitHub, such
as re-running a check run, changes a result or a merge. GitHub lets only the
app that created a check run update it, so the controller creates its own
beside a check run with the same name from another app. The controller
remembers what it wrote, and writes a check run again only when a result
changes, a branch leaves the check run's commit, or the program restarts, so
a change that someone else makes to a check run can stay until then.

Octo STS can have several GitHub Apps and issue the tokens for each
repository and identity for a different one. So the controller learns each
repository and identity's app from the check runs that it creates and
updates. Octo STS's
[sticky store](https://github.com/octo-sts/app#sticky-store) keeps a
repository and identity on one app. If Octo STS moves them to another app,
which can't update the old app's check runs, the controller creates new
ones beside them.

GitHub limits the requests that each installation of a GitHub App can make,
and an installation is one owner's. When GitHub answers that an installation
reached its limit, the controller stops publishing for that repository
owner, for every app, until the time that GitHub gives, or for a minute. It
logs other errors from GitHub and tries again later. When GitHub refuses
with a `4xx` status to update the check run on a commit that a branch left,
the controller logs the error and doesn't try again, so that the error
doesn't delay the check run on the branch's new commit. Rate limits and
errors don't hold back checks or landings. To show whether the check-runs
identity works, the repositories controller sets the `CheckRunsTokenIssued`
condition on the `GitRepository`, which is `False` with Octo STS's answer
when Octo STS doesn't issue a token. The `GitRepository` stays `Ready`
either way.

### Security

The programs keep GitHub tokens in memory and pass them to git in its
environment, so the tokens don't appear in process arguments, Kubernetes
objects, or logs. The service account tokens that the programs send to Octo
STS are bound to the programs' Pods and last an hour. `generate` lets each
program that fetches or pushes request tokens for its own service account,
and for no other.

The programs send service account tokens only to Octo STS, and GitHub tokens
only to GitHub. For tests, the `-fake-github` flag points them at a fake
GitHub and Octo STS instead. It's a flag and not a `GitRepository` field, so
only whoever installs a program can choose where its tokens go. The
end-to-end test's git server runs such a fake, which checks each service
account token with a TokenReview, because Octo STS can't reach a kind
cluster's issuer.

A trust policy's audience ties it to one namespace, so anyone who can create
a `GitRepository` in that namespace can use the trust policy's permissions.
Grant that only to people who may push to the repository. The audience holds
only the namespace's name, so a namespace that's deleted and created again
with the same name gets the trust policies that named the old one.

The rule that lets each program request tokens, `create` on
`serviceaccounts/token` for its own service account, also lets anyone who
holds one of the program's service account tokens create more. Someone who
can run `kubectl exec` in the program's Pod, create Pods in its namespace,
or read files on its node can get such a token. The tokens that they create
can have any audience, needn't be bound to the Pod, and can last as long as
the API server allows. A token with the audience
`octo-sts.dev/` followed by a namespace gets the permissions of each trust
policy that requires that audience and names the program, such as
`contents: write`. Whoever holds a program's token can therefore push to the
repositories of every namespace whose trust policies name that program. The
audiences keep namespaces apart from each other, but not from someone who
can read a program's token. Limit who can use `pods/exec` or create Pods in
the programs' namespaces, and if you manage the API server, set
`--service-account-max-token-expiration`.

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
