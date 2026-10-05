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

`url` must be an `https://`, `http://`, `git://`, or `ssh://` URL, or an
scp-like address with a user name, such as `git@example.com:app.git`. Without
a user name, write an `ssh://` URL, such as `ssh://example.com/~/app.git`. The
API server rejects other URLs, and git-k8s runs git with `GIT_ALLOW_PROTOCOL`
set to those transports. Its git commands put `--end-of-options` before every
URL, branch, and commit, so git can't read one as an option. git-k8s doesn't
track branches whose names start with `-` or aren't valid ref names.

Put credentials in `secretRef`, not in `url`. `kubectl get gitrepositories`
shows each URL, and `check-gotest` copies it into its Pod specs.

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
in each program. Only commit SHAs go into Kubernetes objects. Apart from
[events](#events), which the API server deletes after an hour by default, no
object records a single push or check run, so the API server holds a bounded
amount of state.

After a branch lands, `kubectl get gitbranches` shows what's still open:

```
NAME                    BRANCH   HEAD                                       PARENT   STATE              AGE
app-c-auth-f684729ccf   c/auth   d28547a6c959905ea8dc037ac37541167a50638c   main     WaitingForChecks   9s
app-main-9157892a7c     main     610a7734a0b4d1bc1991a669d9feb35fd159219b                               48s
```

The `Merged` condition's message explains a `WaitingForChecks` state, for
example `checks: approval Failed, base Passed, gofmt Passed, risk Passed (high)`.

## Events

The controllers record an event about a `GitBranch` each time they change
the remote:

| Reason | From | When |
| --- | --- | --- |
| `PushedFix` | `check-NAME` | A check pushed a fix commit to the branch. |
| `Landed` | `merge` | The merge controller fast-forwarded the parent to the branch. |
| `DeletedBranch` | `merge` | The merge controller deleted the branch after it landed. |

`kubectl describe gitbranch GITBRANCH` lists a branch's events. After the
merge controller deletes a branch, the repositories controller deletes its
`GitBranch`, so list the namespace's events instead:

```sh
kubectl get events --sort-by=.metadata.creationTimestamp
```

After `c/fmt` in the end-to-end test lands, the output looks like this:

```
LAST SEEN   TYPE     REASON          OBJECT                           MESSAGE
14s         Normal   PushedFix       gitbranch/app-c-fmt-793d86522b   pushed 5d0c2e9a71b4 to c/fmt: 1 of 2 Go files need gofmt: util/add.go
9s          Normal   Landed          gitbranch/app-c-fmt-793d86522b   fast-forwarded main from 0e4f8a2c9d13 to c/fmt at 5d0c2e9a71b4
9s          Normal   DeletedBranch   gitbranch/app-c-fmt-793d86522b   deleted c/fmt at 5d0c2e9a71b4 after it landed on main
```

kube drops events when it falls behind on writing them, and the API server
deletes events after an hour by default. To audit what landed, use the
remote's history. `generate` grants `create` and `patch` on events to the
`git-k8s` program and to every check program. A check that never pushes a
fix, such as `check-approval`, gets the grant too, because the `checks`
package that every check uses records `PushedFix`.

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
shows something else. It doesn't know which branch's result changed last
before the restart, so a check run that several branches share shows the
result of the branch that it reconciles last, until one of their results
changes. Until the controller learns its app, it writes the result even to
a check run that shows it, because the check run that it finds can be
another app's. Branch protection reads only the check runs on a pull
request's head commit, so a check run on a commit that no branch is at
doesn't block a merge.

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
owner, for every app, until the time that GitHub gives, or for a minute. A
reconcile also stops at the first request that GitHub doesn't answer, so a
GitHub that doesn't answer holds up a repository's reconciles for one
30-second timeout each, not one for each check. GitHub can carry out a
request without its answer arriving, for example when the connection drops
or a proxy answers with a `502` status. So when a request to create a check
run gets no answer or a `5xx` status, the controller looks for the check run
on GitHub before it writes again. When a request to update a check run gets
no answer or a `5xx` status, the controller writes the check run again, even
when the result doesn't change.

The controller logs other errors from GitHub and tries again later, up to 5
minutes apart. It keeps trying even when GitHub's answer can't change. For
example, GitHub refuses with a `422` status to create a check run on a
commit that it doesn't have, and the controller tries again until no
branch's result is for that commit. When GitHub refuses with a `4xx` status
to update the check run on a commit that a branch left, the controller logs
the error and doesn't try again, so that the error doesn't delay the check
run on the branch's new commit. Each reconcile of a repository's branches
updates the check runs that deleted branches left, so while GitHub fails
otherwise to update one, every branch's reconcile fails and tries again
with its own backoff. Rate limits and errors don't hold back checks or
landings.

To show whether the check-runs identity works, the repositories controller
sets the `CheckRunsTokenIssued` condition on the `GitRepository`, which is
`False` with Octo STS's answer when Octo STS doesn't issue a token. The
`GitRepository` stays `Ready` either way.

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
| `check-approval` | `approval` | Passes when the `git-k8s.imjasonh.com/approve` annotation on the `GitBranch` names the branch's head, and sets `outputs.approver` to the `git-k8s.imjasonh.com/approved-by` annotation. A push after the approval needs a new one. See [Approve a branch](#approve-a-branch). |
| `check-gotest` | `gotest` | Runs `go test ./...` in a Pod that it declares with `kube.Own`, and fails with the end of the test output. See [Sandboxed checks](#sandboxed-checks). |

A check with `mayPush: true` pushes its fix commit to the branch, which moves
the head and runs the checks again. Fix commits have a `Git-K8s-Fixer:
CHECK` trailer, and `maxAutomatedCommits` (default 5) limits how many a
branch can have, so two checks that undo each other's fixes stop. The same
inputs always produce the same fix commit, so two retries of one fix push the
same commit.

### Approve a branch

An approval is two annotations on the `GitBranch`: `approve`, which names
the commit, and `approved-by`, which names you. Set both in one request:

```sh
kubectl annotate --overwrite gitbranch GITBRANCH git-k8s.imjasonh.com/approve=SHA \
  git-k8s.imjasonh.com/approved-by="$(kubectl auth whoami -o jsonpath='{.status.userInfo.username}')"
```

The `git-k8s-approvals` policy in `config/policy.yaml` enforces these rules:

- Setting, changing, or removing the `approve` or `approved-by` annotation
  requires the `approve` verb on the `GitBranch`. `generate` grants that
  verb to no program, so grant it to the people who approve:

  ```sh
  kubectl create role approver --verb=get,list,watch,patch,approve --resource=gitbranches.git-k8s.imjasonh.com
  kubectl create rolebinding approver --role=approver --group=GROUP
  ```

- A request that sets or changes `approve` must set `approved-by` to the
  username that sends it.
- A request that removes `approve` must remove `approved-by` too.
- A request that changes only `approved-by` takes over the approval, so
  `approve` must name a commit, and the request must set `approved-by` to
  the username that sends it.

On Kubernetes 1.36 or later, `kubectl apply -f config/approved-by.yaml`
installs a MutatingAdmissionPolicy that sets `approved-by` to your username
when you set or change `approve`, and removes it when you remove `approve`,
so one annotation approves:

```sh
kubectl annotate --overwrite gitbranch GITBRANCH git-k8s.imjasonh.com/approve=SHA
```

The mutating policy leaves `approved-by` alone when the request changes it
as well, and `git-k8s-approvals` checks every approval either way.

To take over an existing approval of the same commit, set both annotations
as in the first command. Setting only `approve` leaves that approval and its
`approved-by` as they are. Admission policies see only the object that a
request produces, so the mutating policy can't tell that the request set
`approve` again. `check-approval` reports the new approver after a takeover.

`check-approval` reports `approved-by` as `outputs.approver`, so a merge gate
can require particular approvers:

```yaml
when: >-
  checks.approval.passed &&
  checks.approval.outputs.approver in ["alice@example.com", "bob@example.com"]
```

An approval without `approved-by`, such as one from before the policy was
installed, still passes with an empty `outputs.approver`, so the branch waits
at a gate like this one until someone approves it again.

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

All of a test Pod's containers meet the `restricted`
[Pod Security Standard](https://kubernetes.io/docs/concepts/security/pod-security-standards/).
An admission policy keeps `check-gotest` to its own Pods, in namespaces that
opt in to test Pods and enforce the `restricted` standard. See
[Install](#install).

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
and `go-cache` sends TokenReviews and gets Pods itself, so the file adds a
ClusterRole that allows creating TokenReviews and getting Pods, and
nothing else. `go-cache` can get any Pod by name, but can't list or watch
Pods.

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
- Only `check-gotest`'s Pods write, and only before their tests start. The
  kubelet binds each projected token to its Pod, and a TokenReview names
  the Pod that a token is bound to. `go-cache` gets that Pod for each
  write, and accepts the token only if the Pod has the UID that the token
  names, has the label `kube.imjasonh.github.io/controller=check-gotest`,
  isn't being deleted, and is Pending. kube puts that label on each Pod
  that `check-gotest` creates. A Pod is Pending while its init containers
  run, and `upload` is one of them. A token that isn't bound to a Pod
  can't write. If `check-gotest` runs under another name, set
  `go-cache`'s `-controller` flag to that name.
- The namespace is the trust boundary. Anyone who can create Pods in a
  namespace can create one with `check-gotest`'s label and a token for any
  audience, so they can write the build caches of the namespace's
  repositories. They can already mount the namespace's Secrets, including
  the repositories' credentials, so the build cache doesn't let them do
  more. Anyone who can create tokens for the namespace's `default` service
  account, which `check-gotest`'s Pods run as, can bind one to such a Pod
  while it's Pending, and write too. `generate` lets a check that runs Pods
  create them in every namespace, but the `git-k8s-check-pods` policy in
  `config/policy.yaml` keeps each check to Pods with its own label, so
  another check's Pods can't write. They can read the build caches of a
  namespace that opts in to test Pods, where they can already mount the
  namespace's Secrets. Reads don't change what any Pod compiles.
  Namespaces don't share build caches.

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
  read build outputs, and use a token that writes until the token expires
  or its Pod leaves Pending.
- `go-cache` remembers a token's review for a minute, so a token that
  reads works for up to a minute after its Pod is deleted. A token that
  writes stops working when its Pod leaves Pending, because `go-cache`
  gets the Pod for each write. `go-cache` denies a token that isn't a JWT
  for the request's audience without a TokenReview, remembers denials
  apart from the tokens that it accepts, and sends at most 8 TokenReviews
  at once. A flood of bad tokens can hold up reviews of new tokens, but
  not requests with tokens that it accepted in the last minute. It gets at
  most 8 Pods at once, in slots of their own. Tokens bound to Pods that
  fail the check can hold up writes, but `go-cache` remembers up to 1024
  such Pods for 10 seconds each, so each costs at most one get every 10
  seconds.
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

`config/policy.yaml` holds four ValidatingAdmissionPolicies. The first lets
the service account of `check-NAME` change only `status.checks.NAME`, and
stops every other service account, including the core program's, from
changing `status.checks`. A check must run as the service account
`check-NAME` in the namespace `check-NAME`, as `generate` installs it, to
write results. Server-side apply already keeps the controllers' writes
apart; the policy stops a buggy or compromised check from writing another
check's result. The second stops every git-k8s service account from setting
the `approve` and `approved-by` annotations, which are for people, and stops
checks from changing `GitBranch` objects at all. RBAC also keeps every check
except `check-gotest`, which owns the Pods that run tests, from patching
`GitBranch` objects. `generate` grants that permission to a check that owns
objects, because it can't tell whether an owned object needs a finalizer on
its owner. The second policy denies the annotation that kube adds with that
finalizer, so a check can own only namespaced objects in the branch's
namespace.

The third keeps each check to its own Pods. `generate` lets a check that
declares Pods with `kube.Own`, such as `check-gotest`, create, patch, and
delete Pods in every namespace, because RBAC can't limit those verbs to the
Pods that a program created. kube labels each Pod that `check-NAME` declares
with `kube.imjasonh.github.io/controller=check-NAME`. The policy lets the
check change or delete only Pods with that label, and its new Pods must have
it. A new Pod's name must be `NAME-ID`, where `ID` has no hyphens, so that a
check can't take the name of another check's next Pod and block it. The check
can't write Pods in the `git-k8s` or `check-*` namespaces. Elsewhere, it
creates and changes Pods only in namespaces that have the label
`git-k8s.imjasonh.com/check-pods=true` and enforce the `restricted` Pod
Security Standard at version `latest`. It can delete its Pods in a namespace
without those labels, so it can clean up after a namespace drops them. Its
Pods must run as their namespace's `default` service account, and a new Pod
can't set `spec.nodeName`.

The policy itself enforces the `baseline` Pod Security Standard, more strictly
for capabilities and sysctls. It denies these fields in containers, init
containers, and ephemeral containers:

- The node's network, PID, and IPC namespaces
- `hostPath` volumes and host ports
- Privileged containers and added capabilities
- An unmasked `/proc`, the `Unconfined` seccomp profile, and Windows host
  processes
- The `Unconfined` AppArmor profile, SELinux users and roles, SELinux types
  other than the container types that `baseline` allows, and sysctls
- Probes and lifecycle handlers that set `host`, which make the kubelet
  connect from the node to another address

Pod Security admission enforces the rest of `restricted`, such as running as
a non-root user. An exemption in the cluster's Pod Security admission
configuration that covers a check's Pods, by user, RuntimeClass, or
namespace, weakens only that rest. The policy doesn't limit node selectors,
affinity, tolerations, or `runtimeClassName`, so a compromised check can
schedule Pods onto any node, including tainted ones, and start them without
the RuntimeClass that `-runtime-class` sets. To require that RuntimeClass,
add a ValidatingAdmissionPolicy that denies a Pod with the label
`kube.imjasonh.github.io/controller=check-gotest` unless its
`spec.runtimeClassName` is the RuntimeClass.

The policy matches every service account whose namespace or name starts with
`check-`. Of those, only `check-NAME` in the namespace `check-NAME`, as
`generate` installs the `NAME` check, can write Pods. Any other, such as an
unrelated service account named `check-deployer`, can't write Pods at all. A
check that runs as another service account needs a policy of its own. If that
policy reads parameters, its binding must set
`parameterNotFoundAction: Allow`. The API server looks up a binding's
parameters before it evaluates the policy's match conditions, so with `Deny`,
every Pod write in the cluster fails while the parameters are missing.

In a namespace that opts in, a compromised check's Pods can still mount the
namespace's Secrets, ConfigMaps, and PersistentVolumeClaims, run as its
`default` service account, and mount tokens for that account with any
audience. A service that accepts those tokens must check which Pod a token is
bound to, and that the Pod has the label of the check that the service
trusts.

The fourth checks who approves, as [Approve a branch](#approve-a-branch)
describes.

Without the policies, most of that doesn't hold, so the repositories
controller sets a `PoliciesInstalled` condition on each `GitRepository`. It's
`False` until all four policies are installed with bindings that deny.

Each namespace that holds a `GitRepository` whose merge policy lists `gotest`
must opt in to test Pods and enforce the `restricted` Pod Security Standard,
or the third policy denies the test Pods:

```sh
kubectl label namespace NAMESPACE git-k8s.imjasonh.com/check-pods=true pod-security.kubernetes.io/enforce=restricted
```

Replace `NAMESPACE` with the namespace of the `GitRepository`. The namespace
can't be `git-k8s` or start with `check-`. If it has the label
`pod-security.kubernetes.io/enforce-version`, the label's value must be
`latest`. Until the namespace has both labels, the branch's `gotest` result
stays `Running`, and its message says why kube couldn't create the Pod. kube
tries again with backoff that grows to 5 minutes, plus up to 10% jitter, so it
creates the Pod within about 5.5 minutes after you label the namespace,
without a new push.

If `check-gotest` already runs, label the namespaces of its repositories
before you apply `config/policy.yaml`. Otherwise the policy denies their test
Pods until you do.

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
