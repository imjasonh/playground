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
Secret. A check makes a `Fix` commit with `in.CommitTree`, which also needs
`SigningKey: signing.Key` to [sign it](#sign-commits). `generate` grants a
program what its packages call, so a check that reads only the `GitBranch`,
such as `check-approval`, leaves both out, and its program can't read
Secrets.

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

## Sign commits

`check-base` and `check-gofmt` make commits: merges of a parent into a
branch, and formatting fixes. Landing makes none, because it fast-forwards
the parent to a commit that's already on the branch. To sign the checks'
commits, make an SSH key for signing only, put it in its own Secret in the
`GitRepository`'s namespace, and name the Secret in the `GitRepository`:

```sh
ssh-keygen -t ed25519 -N '' -C git-k8s -f git-k8s-signing
kubectl create secret generic app-signing --type=kubernetes.io/ssh-auth \
  --from-file=ssh-privatekey=git-k8s-signing
```

```yaml
spec:
  url: https://git.example.com/app.git
  secretRef:
    name: app-creds
  signingKeyRef:
    name: app-signing       # ssh-privatekey key, for signing commits
```

The checks sign with git's SSH signature format, `gpg.format=ssh`. Git runs
`ssh-keygen` to sign, so the checks' image needs it, and the
`cgr.dev/chainguard/git` image that [Install](#install) uses has it. The key
must be unencrypted, in the OpenSSH format that `ssh-keygen` writes. Ed25519
and RSA signatures come out the same every time, so a check still makes the
same fix commit from the same inputs; ECDSA signatures don't. Without
`signingKeyRef`, the checks' commits aren't signed. Keyless signing with
[gitsign](https://github.com/sigstore/gitsign) isn't supported; see
[future work](future-work.md#sign-commits-with-gitsign).

The key needs a Secret of its own, because the `secretRef` Secret holds the
credentials for the remote, and each test Pod's init container gets some of
its keys. A check reports an error instead of signing if `signingKeyRef`
names the `secretRef` Secret.

Only `check-base` and `check-gofmt` read the signing Secret, through the
`signing` package, which no other program links. They already read the
`secretRef` Secret, so `generate` grants them nothing new. For each commit,
a check writes the key to a file with mode 0600 in a new directory with mode
0700 under `/tmp`, passes git the file's path, and removes the directory
when the commit is done. `/tmp` is an `emptyDir` volume on the node's disk
that outlives the container, so a check that's killed while it signs leaves
the key there until the check restarts and removes it, or until the Pod is
deleted. The key never appears in a command's arguments or environment, in
a log, or in an error.

### Set up the forge

A forge shows a commit as verified when the key that signed it belongs to
the commit's committer. On GitHub:

1. As the account that git-k8s commits as, such as a bot account, go to
   **Settings** > **SSH and GPG keys** > **New SSH key**, set **Key type**
   to **Signing Key**, and add `git-k8s-signing.pub`. Or run
   `gh ssh-key add git-k8s-signing.pub --type signing` as that account.
2. Set the `-identity-email` flag of `check-base` and `check-gofmt` to an
   email address that the account has verified, such as its
   `ID+USERNAME@users.noreply.github.com` address. GitHub marks a commit
   **Verified** only when its committer email belongs to the account that
   has the key. To pass a flag, add it after `--` in the `generate`
   command, as in [Install](#install).

A GitHub App can't have a signing key. GitHub signs the commits that an App
makes through its API, but the checks make commits with git, so they sign
them with an account's key even when they push with an App's token. GitHub
verifies a signature no matter which credential pushed the commit.

### Protected branches

Checks push their commits to the branch that they check, and the merge
controller pushes the parent when a branch lands. GitHub's branch
protection rules and rulesets apply to those pushes:

- Rules that limit who can push to the parent, such as **Require a pull
  request before merging** and **Restrict updates**, reject a landing
  unless the account or GitHub App that git-k8s pushes as can bypass them.
  In a ruleset, add the account or App to the bypass list, set to **Always
  allow**. If the bypass list doesn't offer individual accounts, add a team
  whose only member is git-k8s's account. A bypass applies to every rule in
  its ruleset, so put the rules that git-k8s has to follow, such as
  **Require signed commits**, in another ruleset, without git-k8s in its
  bypass list. In a classic branch protection rule, add the account or App
  to **Allow specified actors to bypass required pull requests**, and to
  **Restrict who can push to matching branches** if that's on.
- **Require status checks to pass** rejects a landing unless the branch's
  head already passed those checks, for example in CI that runs on the
  branch. git-k8s doesn't report its own results to GitHub yet.
- **Require signed commits** refuses a landing unless GitHub verifies the
  signature of every commit that it adds to the parent, so people have to
  sign with a key on their GitHub account and use a committer email that
  the account has verified.
- **Require linear history** rejects the merge commits that `check-base`
  makes. Leave it off for a parent whose merge policy lets `base` push.
- **Block force pushes** doesn't affect git-k8s, which pushes only
  fast-forwards and deletions.
- **Restrict deletions** on a branch stops `deleteMergedBranches` from
  deleting it after it lands.

When GitHub refuses a push, the reason that it gives shows up on the
`GitBranch`. For a check's commit, the check's result in `status.checks` has
state `Error` and the reason in its message. For a landing, the `Synced`
condition is `False` and has the reason in its message. git-k8s retries
refused pushes, waiting longer each time, up to about 5 minutes.

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
gateway, and pushes branches to it. The git server accepts only commits
signed with their committer's key, as a forge that requires signed commits
does, so the test fails if git-k8s pushes an unsigned commit. It needs
Docker, `kubectl`, `git`, and `ssh-keygen`, and installs kind if it's
missing:

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
