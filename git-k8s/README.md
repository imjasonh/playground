# git-k8s

git-k8s runs a branch workflow on Kubernetes. It tracks a remote git
repository's branches as `GitBranch` objects and runs checks on branches
that propose changes to another branch. Checks can push commits that fix
what they find. When the parent's merge policy passes, git-k8s lands the
branch on the parent by fast-forward, squash, or rebase.

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
shows each URL, and `check-gotest`, `check-review`, and `check-conflicts` copy
it into their Pod specs.

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
  over the fresh results. When it passes, the controller lands the branch,
  as [Landing methods](#landing-methods) describes, with
  `git push --force-with-lease`, so a parent that moved in the meantime is
  never overwritten. It then deletes the branch if the policy says to. When
  the policy lets the `base` check push, branches whose gates pass wait in
  the parent's [merge queue](#merge-queue), and only the branch at the front
  lands.

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
NAME                    BRANCH   HEAD                                       PARENT   STATE              QUEUE   AGE
app-c-auth-f684729ccf   c/auth   d28547a6c959905ea8dc037ac37541167a50638c   main     WaitingForChecks           9s
app-c-one-a7d8621874    c/one    04988fc4984947ac2af2b55d15bc96b8e49b5a2f   main     Queued             1       2s
app-c-two-de141ef616    c/two    62ebc5163be79d7963293a7e4c6152a967ed9838   main     Queued             2       2s
app-main-9157892a7c     main     610a7734a0b4d1bc1991a669d9feb35fd159219b                                       48s
```

The `Merged` condition's message explains a `WaitingForChecks` state, for
example `checks: approval Failed, base Passed, gofmt Passed, risk Passed (high)`.
`QUEUE` is a branch's place in its parent's [merge queue](#merge-queue).

## Events

The controllers record an event about a `GitBranch` each time they change
the remote:

| Reason | From | When |
| --- | --- | --- |
| `PushedFix` | `check-NAME` | A check pushed a fix commit to the branch, or `check-conflicts` pushed `resolve/BRANCH` for a diverged branch without a parent. |
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
`check-risk`, `check-conflicts`, and `check-review`, which pushes its agent's
fixes. The test Pods of `check-gotest` and the agent Pods of `check-review`
and `check-conflicts` fetch without credentials, so with Octo STS, `gotest`
and `review` work only for a public repository, and for a private one,
`conflicts` resolves only what git can. The `git-k8s` program publishes
[check runs](#check-runs) with tokens for `checkRunsIdentity`, and publishes
none without it. The URL must have the form `https://github.com/OWNER/REPO`,
with or without `.git`.

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
   subject_pattern: system:serviceaccount:(git-k8s:git-k8s|check-base:check-base|check-gofmt:check-gofmt|check-risk:check-risk|check-conflicts:check-conflicts|check-review:check-review)
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
reports an `Error` result, except `check-review`, which reports `Running` and
tries again to push its agent's fix, and `check-conflicts` on a branch with a
parent, which reports `Running` and tries again. The messages include Octo
STS's answer, such as `unable to find trust policy for "git-k8s"`. Octo STS
caches each trust policy, and the lack of one, for 5 minutes, so a change to a
trust policy can take that long to apply.

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
| `check-base` | `base` | Passes when the branch contains its parent's head, or the parent already contains the branch. Otherwise it merges the parent in with `git merge-tree`, and fails with the conflicting paths if the merge conflicts. With `mayPush`, it merges the parent in only at the front of the parent's [merge queue](#merge-queue), and until then passes a branch that merges cleanly, with `outputs.behind` set to `"true"`. |
| `check-gofmt` | `gofmt` | Formats every `.go` file outside `vendor` and `testdata` directories with `go/format`, and passes when nothing changes. |
| `check-risk` | `risk` | Always passes, and sets `outputs.level` to `high` for a large change, a change to a sensitive path, a new or unreleased dependency, or code from an AI agent, and to `low` otherwise. See [Risk ratings](#risk-ratings). |
| `check-approval` | `approval` | Passes when the `git-k8s.imjasonh.com/approve` annotation on the `GitBranch` names the branch's head, and sets `outputs.approver` to the `git-k8s.imjasonh.com/approved-by` annotation. A push after the approval needs a new one. See [Approve a branch](#approve-a-branch). |
| `check-gotest` | `gotest` | Runs `go test ./...` in a Pod that it declares with `kube.Own`, and fails with the end of the test output. See [Sandboxed checks](#sandboxed-checks). |
| `check-review` | `review` | Has an AI agent review the branch's change against its parent in a sandboxed Pod. It passes or fails with the agent's reasoning as its message, and sets `outputs.summary` and the run's token counts. With `mayPush: true`, the agent can also fix what it finds. See [Agentic checks](#agentic-checks). |
| `check-deps` | `deps` | On a dependency branch, passes when the `gotest` check passes. When the tests fail, it has an AI agent change the code to fit the new versions, and pushes the agent's fix. It passes on other branches. See [Dependency updates](#dependency-updates). |
| `check-conflicts` | `conflicts` | Passes when merging the parent into the branch has no conflicts. When the merge conflicts, or the branch diverged from the external repository, it pushes a merge that git or an AI agent resolved, or fails when neither can. When a side of a diverged branch rewound, it replays the other side's commits onto that side's head instead of merging. See [Resolve conflicts](#resolve-conflicts). |

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

### Risk ratings

`check-risk` compares the branch's head with its merge base on the parent,
and rates the change `high` when any of these is true:

- It changes more lines than `-max-lines`, 200 by default. Lines in `go.sum`
  and `go.work.sum` files don't count, because they're checksums that the
  `go` command checks, and the versions that they cover show in `go.mod`.
- It touches a path that matches a `-sensitive` glob.
- A `go.mod` file that it changes requires a module that no `go.mod` file
  at the merge base requires, moves a module to an earlier version than the
  file required, to a new major version, or to a version that isn't a
  release, such as a pseudo-version, replaces a module with another module
  or with a directory outside the repository, stops replacing one, or
  changes the `go` or `toolchain` line. A directory is outside the
  repository when its path is absolute, leads out of the repository from
  the `go.mod` file's directory, or goes through a symbolic link or a
  submodule, because the `go` command follows the link, which can point
  anywhere, and a submodule's files come from another repository. A
  `go.mod` file that the check can't parse also counts. Requiring a module
  that the file replaces with a directory in the repository is fine,
  because that code is in the repository. Requiring a module that only a
  `go.mod` file in the repository declares isn't, because without a
  replacement, the `go` command downloads the module from the module proxy.
- It adds or changes a symbolic link or a submodule that the directory of a
  replacement in any `go.mod` file goes through, even when no `go.mod` file
  changes.
- It changes a `go.work` file, whose directives apply to every module in
  the workspace.
- It has commits from AI agents, which carry a `Git-K8s-Agent: CHECK`
  trailer, because no person wrote that code.

Otherwise the change is `low` risk. So a patch or minor release of a module
that any part of the repository already requires is low risk, and lands
without approval under a gate such as
`checks.risk.outputs.level == "low" || checks.approval.passed`. The check
skips `go.mod` files in `testdata` and `vendor` directories. Its message
lists every reason, for example `risk is high: adds module example.com/c;
has changes from AI agents`.

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

A check runs again when the branch's head changes, and with `UsesParent`,
when the parent's head changes. `Always` runs it on every reconcile, for a
check that reads only the `GitBranch`. `Stale` runs it again when something
that it reads with `kube.Get` makes a finished result out of date, the way
`check-base` runs again when its branch reaches the front of the merge
queue.

Set `FilesOnly` in a check's `checks.Check` when its result for the branch's
head also holds for any commit with the same files that builds on the same
parent head, because the result doesn't depend on the branch's commits, such
as their messages or authors. Squash and rebase landings count only such
results for the commits that they make, as
[Which results count](#which-results-count) describes.

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
  namespaces. A branch that can't start its Pod yet reports `Running` and
  records when it started waiting in `outputs.waiting`. When a Pod
  finishes, the branch that has waited longest starts next. A new head, a
  retry after a failed fetch, or a replacement for a deleted Pod waits
  behind the branches that are already waiting. The times are in the
  `GitBranch` status, so a restarted check keeps the order.
- The check counts a Pod from the moment that it declares it, before its
  cache shows the Pod, so a burst of pushes can't start more than
  `-max-pods`. A Pod that never appears stops counting after a minute. If
  the API server refuses a Pod, for example because the check Pod policy
  denies it, other branches can then use its place while kube tries again.
  Until the Pod exists, its branch keeps the time that it started waiting in
  `outputs.queued`, so the branch still starts before the branches that
  started waiting after it. With `-shards`, a replica doesn't count the Pods
  that other replicas declared until its cache shows them, so replicas that
  start Pods at the same moment can go over the limit.

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
  another check's Pods can't write. The policy skips service accounts whose
  namespace and name don't start with `check-`. If a check runs as such an
  account and can create Pods, give it a policy of its own, as
  [Check service accounts](#check-service-accounts) says. Without one, its
  Pods can have `check-gotest`'s label and write. Other checks' Pods can
  read the build caches of a namespace that opts in to test Pods, where
  they can already mount the namespace's Secrets. Reads don't change what
  any Pod compiles. Namespaces don't share build caches.

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

### Agentic checks

`check-review` runs an AI agent with the
[Cursor SDK](https://www.npmjs.com/package/@cursor/sdk). Like
`check-gotest`, it declares a Pod for each head with `kube.Own`, and
reports `Running` until the Pod finishes. The `agent` package declares the
Pods, so other checks can run agents the same way. Each Pod has three
containers:

- The `prepare` init container fetches the head with the repository's
  credentials. It writes the head's files to a directory that isn't a git
  repository, without the `.cursorignore` files that Cursor reads to hide
  files from the agent. Next to it, it writes the change from the merge
  base, the paths that the change touches, and the commit log. It also
  copies the Cursor API key from a Secret to a memory volume. It's the only
  container that gets the credentials or reads a Secret.
- The `agent` init container runs the runner in `agent/runner`, a small
  Node program. The runner reads the key and deletes its file, then runs the
  agent in the directory of the head's files. The agent is offered only
  tools that read and search the files, plus tools that edit and delete them
  when the check can push, and Cursor's backend enforces that list. Apart
  from the key in the runner's memory, the container holds no credentials
  once the key file is gone. The runner writes the agent's verdict, summary,
  reasoning, and token usage to a result file, and the file's SHA-256 digest
  as the container's termination message. A run that fails after the agent
  starts writes the error and the token usage instead.
- The `result` container serves the result file over HTTP to requests whose
  bearer token is the Pod's UID.

The check reads the digest and the UID from the API server, fetches the
result from the Pod's IP over plain HTTP, and rejects it unless it matches
the digest. So the agent's containers get no Kubernetes or git credentials,
a check that restarts fetches the result again, and a result can hold the
files that the agent changed, which don't fit in a termination message.
Anyone who can read the Pod or watch the cluster's network can read a
result, but can't change it. The check also rejects a result with an
unknown verdict, an invalid path, a file mode other than a regular file or a
symbolic link, more than 1,000 files, or more than 8 MiB of file content.

Each agent Pod's volumes have size limits. The repository, the head's
files, and the agent's input can each use up to `-source-size`, 2Gi by
default, and the agent's home directory up to 1Gi. The init containers'
ephemeral-storage limit covers all the volumes and the logs. It's three
times `-source-size` plus 1344Mi, which is 7488Mi by default. When a Pod
uses more than a limit, the kubelet evicts it.

The scheduler reserves only a Pod's requests on its node, and the init
containers request `-storage-request` of ephemeral storage, 1Gi by
default. So a node can run low on disk space or memory while each Pod
stays within its limits, and then the kubelet evicts Pods, first those
that use more than they request. Either way, the check fails with the
kubelet's reason. If agent Pods often fail because their nodes run low on
disk space, raise `-storage-request`.

A ResourceQuota on `limits.ephemeral-storage` counts each agent Pod's
limit, and one on `requests.ephemeral-storage` counts `-storage-request`.
A LimitRange with a smaller maximum for ephemeral storage rejects every
agent Pod. When kube can't create a Pod, the check says so, and its
message or the program's log says why.

The agent's prompt holds the first 200,000 bytes of the diff and lists
every path that the change touches, so the agent can read the files that
the diff leaves out. The check fails a change that touches more than 1,000
paths.

When the policy lets the check push, the agent can also edit the files.
The check commits what changed on the head, and pushes it like any other
fix, with `Git-K8s-Fixer: review` and `Git-K8s-Agent: review` trailers and
within `maxAutomatedCommits`. The second trailer makes `check-risk` rate the
branch high. A fix leaves `.cursorignore` files as they are. If a path in
the head isn't valid UTF-8, the run fails before the agent starts. Without
`mayPush`, the agent's files are read-only.

The check's outputs hold the agent's `summary`, the `model`, the run's
`inputTokens`, `outputTokens`, `cacheReadTokens`, and `cacheWriteTokens`,
and two costs in cents when the SDK reports them. `costCents` is the model
token cost before discounts, the SDK's `rawCostCents`. `chargedCents` is
what Cursor charged, with discounts and fees, the SDK's `chargedCents`; it's
0 for usage that a Cursor plan includes. `runs` counts the agent runs on
the branch, and `pod` names the run's Pod. `state` holds what the check
needs to follow the run.

An agent can answer differently each time, so a result stays until the
branch's head changes, and the check doesn't run again when only the parent
moves. When the agent fails, for example because the API key is missing or
wrong or the run takes longer than `-timeout`, the check fails with the
agent's error. It also fails when an image's name isn't valid, when kube
still can't schedule the Pod 5 minutes after creating it, when a Secret is
still missing or an image still can't be pulled 5 minutes after the
container can start, and when three Pods in a row fail to fetch the head
or find that the branch no longer points to it. The next head runs the
agent again. To run it again on the same change, such as after a transient
error, push an empty commit with `git commit --allow-empty`.

Agent runs cost money. Three limits cap them, and they count runs, not
tokens:

- `maxAgentRuns` in the merge policy, 10 by default, is the most runs that
  each agentic check can start on one branch. Every new head needs a run,
  including the check's own fixes, `check-base`'s merges of the parent, and
  the commits that [squash and rebase landings](#which-results-count) push
  to the branch. A branch that has used them all reports `Running` until you
  raise the limit.
- `-max-runs-per-day`, 100 by default, is the most runs that each replica
  starts in any 24 hours. The program counts them in memory, so the count
  starts over when it restarts, and a replica that takes over a shard
  doesn't count the runs that the shard's last replica started.
- `-max-pods`, 10 by default, is the most agent Pods that run at once
  across all namespaces.

If the branch moves before the agent's Pod fetches it, the agent doesn't
run, so the run doesn't count toward `maxAgentRuns` or `-max-runs-per-day`,
and the new head starts a run of its own. The check waits a minute, or
twice the repository's `pollInterval` if that's longer, for a poll to find
the new head. If the branch's head is the same after the wait, such as when
the branch moved back, the check fetches it again in a new Pod, which
counts as a run.

If an agent Pod is deleted before its run finishes, kube creates it again,
and the agent runs again. The check counts that as another run. When
`maxAgentRuns` or `-max-runs-per-day` allows no more, the check fails
instead, and kube doesn't create the Pod again. A run that fails after the
agent starts still reports the `model`, the token counts, and the costs in
the check's outputs.

A deploy can also run agents again. A Pod's spec can't change, so after a
deploy that changes the agent Pods' spec, such as one with another
`-agent-image` or `-model` or with a version of `check-review` that builds
Pods differently, the check starts each run in progress again in a new
Pod, and kube deletes the old one. The agent starts over and costs as much
as in a new run. A restarted run takes a place in `-max-runs-per-day`, or
waits for one, but it doesn't count toward `maxAgentRuns`. A rollback
before the old Pod is gone returns the run to that Pod without taking a
place. If kube was deleting that Pod, it creates the Pod again once it's
gone, and the check counts another run, as for any deleted Pod. A run that
waits because the branch moved has no agent to start over, so a deploy ends
its wait, and the check fetches the head again at once in a new Pod, which
counts as a run.

The check counts a branch's runs in its outputs on the branch's
`GitBranch`, so a branch that's deleted and then pushed again can start
over at 0, and so can a branch with a new name. To cap what agents cost in
money, also set a spend limit for the Cursor team or account that owns the
API key.

The agent reads the branch's code, which can tell it what to do. Its
verdict goes through the same result path as any check's result, and its
fixes through the same push rules, but neither is a person's review. We
recommend a gate that also needs a person's approval for a risky change,
such as `checks.review.passed && (checks.risk.outputs.level == "low" ||
checks.approval.passed)`.

To install `check-review`, build the runner's image from
`agent/runner/Dockerfile`, push it, and pass its digest to the check with
`-agent-image`. Then create a Secret named `cursor-api-key` that holds a
Cursor API key under the key `api-key`, in each namespace with branches to
review. Agent Pods meet the `restricted` Pod Security Standard and run in
their branch's namespace, which must also opt in to check Pods, as
[Install](#install) describes:

```sh
docker build -t REGISTRY/agent-runner agent/runner
docker push REGISTRY/agent-runner
image="$(docker inspect -f '{{index .RepoDigests 0}}' REGISTRY/agent-runner)"
go run ./cmd/check-review generate -registry=REGISTRY -base=cgr.dev/chainguard/git:latest -- -agent-image="${image}" | kubectl apply -f -
kubectl -n NAMESPACE create secret generic cursor-api-key --from-literal=api-key=KEY
kubectl label namespace NAMESPACE git-k8s.imjasonh.com/check-pods=true pod-security.kubernetes.io/enforce=restricted
```

In a namespace without the Secret, each run fails before the agent starts.

To change a flag or upgrade `check-review`, run `generate` again. A deploy
that changes the agent Pods' spec starts every run in progress again, and
each agent starts over, so deploy when few agent Pods are running. To list
them, run the following command:

```sh
kubectl get pods --all-namespaces -l git-k8s.imjasonh.com/agent=review
```

`check-review` takes these flags, which `agent.Runner.AddFlags` registers:

| Flag | Default | Description |
| --- | --- | --- |
| `-agent-image` | Required | Image that runs the agent, built from `agent/runner/Dockerfile` |
| `-git-image` | `cgr.dev/chainguard/git:latest` | Image that fetches the source; it needs `git` and `sh` |
| `-backend` | `cursor` | Where the agent runs: `cursor`, with the Cursor SDK in the Pod, or `fake`, for tests |
| `-model` | `composer-2.5` | Model that the agent uses |
| `-api-key-secret` | `cursor-api-key` | Secret, in each branch's namespace, whose `api-key` key holds the API key |
| `-timeout` | `15m` | Longest that an agent can run |
| `-max-pods` | 10 | Most agent Pods to run at once, in all namespaces; 0 means no limit |
| `-max-runs-per-day` | 100 | Most agent runs to start in any 24 hours; 0 means no limit |
| `-runtime-class` | None | RuntimeClass for agent Pods, such as `gvisor` |
| `-source-size` | `2Gi` | Most disk space that each of an agent Pod's repository, files, and input can use |
| `-storage-request` | `1Gi` | Ephemeral storage that each agent Pod requests, which the scheduler reserves on the Pod's node |

Agent Pods need to reach the repository and Cursor's API over HTTPS, and
the check needs to reach the agent Pods on TCP port 8080. A NetworkPolicy
matches IP addresses, not host names, so by itself it can't limit agent
Pods to Cursor's API. This policy allows the agent Pods DNS, HTTPS to any
address, and requests from `check-review`:

```yaml
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: git-k8s-agents
  namespace: NAMESPACE
spec:
  podSelector:
    matchLabels:
      app.kubernetes.io/name: git-k8s-agent
  policyTypes: [Ingress, Egress]
  ingress:
    - from:
        - namespaceSelector:
            matchLabels:
              kubernetes.io/metadata.name: check-review
      ports:
        - port: 8080
  egress:
    - ports:
        - port: 53
          protocol: UDP
        - port: 53
          protocol: TCP
    - ports:
        - port: 443
```

If the repository's URL has another port, allow that port too. To allow
only Cursor's API and the repository, use a CNI plugin with DNS-based
rules, such as Cilium's `toFQDNs`.

To write an agentic check, give an `agent.Runner` the check's name, register
its flags, and call its `Run` method with a task. With a view type like the
one in [Write a check](#write-a-check), but with the key `docs`, this is a
complete check:

```go
var runner = &agent.Runner{Name: "docs"}

func run(ctx context.Context, in *checks.Input) (checks.Verdict, error) {
	v, _ := runner.Run(ctx, in, agent.Task{
		Instructions: "Check that the change documents each flag that it adds.",
		Edit:         in.Policy.MayPush,
	})
	return v, nil
}

func main() {
	runner.AddFlags(flag.CommandLine)
	checks.Main[Branch](checks.Check{Name: "docs", Remote: credentials.Remote, Run: run})
}
```

`Run` never returns an error, because a check that returns one loses its
outputs, which count the branch's runs. It also returns the agent's
`Result`, with the files that the agent changed, so a check can build
another kind of commit from them with `agent.ApplyFiles`.

### Resolve conflicts

`check-conflicts` runs the `conflicts` check, which resolves two kinds of
conflict that keep a branch from landing:

- Merging the branch's parent into it conflicts, so `check-base` can't keep
  the branch up to date. The check pushes a merge of the parent that
  resolves the conflicts.
- The branch diverged. It changed both in git-k8s and in the external repository
  since they last synced, and the core program set `status.diverged` to the
  external repository's head, the ref that holds it, and the head where the
  sides last synced. The check fetches the external repository's head from
  `status.diverged.ref`, and pushes a merge of it, or the replays that a rewind
  needs, with a lease on the branch's head. If the external repository deleted
  the branch, the check fails and leaves the branch for a person, who can push
  the branch to the external repository again to keep its changes, or delete it
  in git-k8s to drop them.

When a branch diverged and also conflicts with its parent, the check
resolves the divergence first, because merging the parent doesn't end it.

The check compares each side's head with the head where the sides last
synced, `status.diverged.base`. A side added the commits that its head has
and `base` doesn't, and removed the commits that `base` has and its head
doesn't. A side that removed commits rewound, for example with a force push.
If neither side rewound, only a head that contains both heads keeps both
sides' changes, so the check merges the external repository's head. If one
side rewound, a commit that contains both heads brings back the commits that
the rewound side removed, so the check never makes a merge commit. It
replays the commits that the other side added since `base` onto the rewound
side's head instead, and pushes the result with a lease on the branch's
head:

- If the external repository rewound, the check replays the branch's commits
  onto the external repository's head one at a time, with their authors and
  messages. It skips a commit whose replay changes nothing, such as one whose
  change the external repository's head already has. The check pushes to the
  side that didn't rewind, so the result can change commits to resolve
  conflicts. If a commit can't be replayed by itself, such as a merge, or a
  commit whose replay conflicts, or if the replays don't have every change
  that both sides made, the check replays the branch's whole change since
  `base` as one commit on top of the external repository's head instead.
  Git and the agent resolve that commit's conflicts as they resolve a
  merge's, with `base` as the merge base, and the agent's prompt says not to
  bring back what the rewind removed. If a replay makes the same change as a
  commit that the external repository removed, the check fails and leaves
  the divergence for a person, because one commit would only hide the
  replay.
- If the branch rewound in git-k8s, the check replays the external
  repository's commits onto the branch's head one at a time. It pushes the
  result to the side that rewound, so the result needs a replay of each
  commit that the external repository added, and every change that the
  external repository made. A replay is a commit that removes and adds the
  same lines in the same files as the original, ignoring the unchanged lines
  around them, and a commit replays at most one commit. The comparison
  ignores `.gitattributes` files, so that an attribute such as `-diff` can't
  hide a replay. A merge commit, and a commit that changes no file, have no
  replay. So the check resolves no conflicts here, and fails and leaves the
  divergence for a person when a commit has no replay or doesn't replay
  unchanged, or when the result doesn't have every change that the external
  repository made.
- If both sides rewound, the check replays the branch's commits onto the
  external repository's head if that head has none of the commits that the
  branch removed. Otherwise, it replays the external repository's commits onto
  the branch's head if that head has none of the commits that the external
  repository removed. In this case, it never replays the branch's whole
  change as one commit, and fails when neither replay works.

A head keeps a side's changes when it has none of the commits the side
removed and no replay of one, a replay of each commit it added, and every
change it made since `base`: merging the side into the head with `base` as
the merge base is clean and changes nothing. A replay of a removed commit
counts only if the side made the same change again, as a rebase does. A
head built on a side that rewound to a new commit keeps that side's changes
even where it resolved conflicts. In that case, merging either the side or
the commit where the side and `base` meet into the head, with `base` as the
merge base, must be clean and change nothing, so that the head brings back
no change that the side removed. The merges can't see a replay of a removed
commit whose change other removed commits undid, such as a secret and its
revert that a force push dropped, so the rule also looks for replays of the
removed commits. The search ignores `.gitattributes` files, so that an
attribute such as `-diff` can't hide a replay. It can't find one inside a
larger commit, such as a squash. No merge checks these replays, so a commit
that makes a removed commit's change on another line also counts as one.
The check passes when one side's head already keeps every change that the
other side made.

Branches diverge only with the in-cluster mirror that
[Future work](future-work.md#run-an-in-cluster-git-mirror) proposes, so the
end-to-end test can't make one diverge, and unit tests cover divergence
instead. Until git-k8s has the mirror, the check pushes to the repository's
URL. With the mirror, the check pushes through the mirror, and the mirror
resolves a divergence between its copy and the external repository by the
same rule. It moves one side to the other side's head only if that head
keeps every change that the moving side made, so once one side's head keeps
both sides' changes, such as after the check's push, the mirror moves the
other side to it.

Git resolves what it can by itself. Files that match `-union`, which is `go.sum`
by default, merge with git's union driver, which keeps the lines of both sides.
A union merge can make a file that doesn't work, such as a `go.sum` that lacks a
line that the merged `go.mod` needs, so we recommend a gate that also needs a
check that builds the result, such as `gotest`. The merge uses only the
attributes that `-union` makes, not the `.gitattributes` files of either side,
so a branch can't make git resolve its own conflicts, such as by marking a file
`merge=union`. The check doesn't use `git rerere`, which replays resolutions
that a person recorded in a working tree, or the `ours` and `theirs` options of
git's merge strategy, which pick a side.

When conflicts remain and the check has an agent image, an agent resolves them
in a sandboxed Pod that `Runner.RunJob` starts, as described in [Run agents from
a controller](#run-agents-from-a-controller). The Pod makes the same merge as
the check, with the same `-union` attributes, so its files hold the conflicts
that git left, in the diff3 style, which shows the merge base's lines between
the two sides. The agent's prompt lists both sides' commits since the merge base
and holds both sides' changes. The agent can edit files but not delete them, and
it can't build or run the code. It answers fail when it can't tell how to keep
both sides' changes.

The check commits the agent's files as a merge whose parents are both heads,
or, for a replay, as one commit on top of the external repository's head. It
fails instead when the merge that the agent's Pod made doesn't have the same
tree as the check's merge, when the agent changed a file that doesn't conflict,
deleted a file, or gave a file a mode that the file has on neither side, or when
a file still holds a conflict marker. A file holds one when a line starts with
one of the merge's marker labels, or when more of its lines start like a marker
than in its two sides together.

The check runs an agent only when the policy lets it push, and only within
`maxAutomatedCommits` and `maxAgentRuns`, which `RunJob` enforces as the job's
`MaxRuns` over all of the branch's runs. It runs none for a merge with more than
one merge base, for a conflict in a file that one side deleted or that isn't a
regular file on both sides, or for a conflict that git can't mark, such as one
in a binary file. It also runs none for a conflict in a `.cursorignore` file,
because the agent's work tree leaves those files out, or for conflicts in more
than 1,000 files or in files that hold more than 8 MiB, the most that a result
can change.

Each commit that the check pushes makes a new head, so every check runs
again on it. A merge, and a replay of the branch's whole change as one
commit, have a `Git-K8s-Fixer: conflicts` trailer and count toward
`maxAutomatedCommits`. A replay of one commit keeps that commit's message,
so it counts only if the original did, but the check pushes replays only
while the branch is under the limit, like any fix. When neither git nor the
agent resolves the conflicts, the check fails with the reason and leaves the
branch for a person, because a wrong resolution is worse than none.

In a [merge queue](#merge-queue), the check's merges keep the branch's
place, like other fixes, because each has the trailer and has the branch's
head as its first parent. A replay takes the branch out of the queue when it
adds a commit without the trailer, or when the new head doesn't contain the
old one. At the front, a merge of the parent that conflicts fails the `base`
check, so the branch leaves the queue. It joins again at the back when its
gate passes on the check's merge.

A merge of the parent that has no conflicts passes, because merging it is
`check-base`'s job. The check pushes a merge of the external repository's
head even without conflicts, because nothing else merges it. While an agent
runs, the check keeps following the run when the parent moves, so a parent
that moves often doesn't restart it. The Pod merges the parent's head that
the run started with, even if the parent moved past it before the Pod
fetched the parent. If the run fails after the parent moved, the check runs
again on the parent's new head. If the parent no longer contains the head
that the run started with when the Pod fetches it, the agent doesn't run,
and the check starts a new run on the parent's new head.

The check doesn't rebase a branch onto its parent or onto the external
repository's head. A rebase rewrites commits that checks and people already
saw, such as the head that an approval names, and `check-base` already
brings branches up to date with merges. The check replays commits only when
a side rewound, because then a merge brings back what the rewind removed.

A branch without a parent, such as `main`, has no merge gate, so a merge
pushed to it would skip every check. When such a branch diverges, the check
pushes the external repository's head to the branch `resolve/BRANCH`
instead, with an empty commit on top that says why. The empty commit has the
`Git-K8s-Fixer: conflicts` trailer, so the push follows the same rules as a
check's fix to `resolve/BRANCH`, including the `maxAutomatedCommits` of the
rule that matches it. `resolve/BRANCH` then lands on `BRANCH` through `BRANCH`'s
merge gate, like any other branch. `check-base` merges `BRANCH` into it, or
the conflicts check resolves that merge when it conflicts. The check waits
while `resolve/BRANCH` holds work that hasn't landed, and passes once
`BRANCH` contains the external repository's head, or when the external
repository's head contains `BRANCH`'s head, because the mirror then moves
`BRANCH` to it. To let the check resolve a diverged `main`, add the check to
`main`'s policy, and give `resolve/main` the parent `main` with a rule:

```yaml
  branches:
    - match: main
      merge:
        checks:
          - name: base
            mayPush: true
          - name: conflicts
            mayPush: true
          - name: gotest
    - match: resolve/main
      parent: main
    - match: c/**
      parent: main
```

`resolve/BRANCH` lands only once it contains `BRANCH`'s head, so it can't
resolve a rewind, and the check pushes nothing when a side of a diverged
parent rewound. The merge controller only moves a parent to a commit that
contains the parent's head, so a parent that rewound in the external
repository resolves only there, with a replay of each commit that landed on
the parent since `base`, and every change that those commits made. If a
commit can't be replayed unchanged, for example because it changes lines
that the rewind removed, the parent stays diverged until the external
repository's head contains the parent's head again. If the parent rewound
in git-k8s instead, replay the external repository's commits onto the
parent's head, and push the result to the external repository with a lease
on its head. The check fails, and says which of these to do, until either
side's head keeps every change that the other side made. Then it passes,
because the mirror moves the other side to that head.

Checks push with the repository's credentials, which can push to any
branch. The mirror lets a check update only a branch that has a parent, so
with the mirror, the core program must also give the service account
`check-conflicts` in the namespace `check-conflicts` the branch-name prefix
`resolve/`, which lets it create `resolve/BRANCH`.

To install `check-conflicts`, build the agent runner's image as for
`check-review`, and pass its digest with `-agent-image`. Without
`-agent-image`, the check resolves only what git can, and runs no agent:

```sh
go run ./cmd/check-conflicts generate -registry=REGISTRY -base=cgr.dev/chainguard/git:latest -- -agent-image="${image}" | kubectl apply -f -
```

`check-conflicts` takes the same flags as `check-review`, and `-union`, a
comma-separated list of path patterns in the gitattributes format whose
conflicts git resolves by keeping the lines of both sides. Its agent Pods run
in their branch's namespace, as `check-review`'s do, so that namespace needs
the Secret that holds the Cursor API key, and must opt in to check Pods, as
[Install](#install) describes. The agent Pods also need the NetworkPolicy
that `check-review`'s need, with ingress from the namespace `check-conflicts`.

### Run agents from a controller

A controller, or a check that needs a `Job` that `Run` doesn't build, runs
an agent with `Runner.RunJob`. Its `Job` names the repository, the
Secret with the repository's credentials, the commits to check out, the
task, the agent's tools, and the runner's image if it isn't
`-agent-image`. `Run` builds a `Job` from a check's branch, so both start
the same Pods, within the same `-max-pods` and `-max-runs-per-day` limits.
For a check, the `Runner`'s name must be the check's name, and the `Job`'s
namespace must opt in to check Pods, as [Install](#install) describes.

Call `RunJob` on each reconcile with the `JobState` that the last call
left. The state names the run's Pod and counts the runs that `RunJob`
started and didn't give back. `RunJob` changes it on each call, so store
all of it after each call with the object that the job is for, such as in
the object's status, so a controller that restarts follows the same run.
`MarshalText` encodes the state as one string, such as for one of a check's
outputs, and `UnmarshalText` decodes it. `RunJob` declares the Pod
with `kube.Own` and returns a `JobStatus`. Until the run is `Done`, the
status's `Message` says how the run is going. Once it's `Done`, `Result`
holds the agent's result, or is nil if the run failed, and `Message` says
why. If the run failed after the agent started, `Failed` holds the runner's
report, with its `Error` and what the agent used. `RunJob` reports that
once and sets the state's `Done`. Later calls for the same `Job` report
the run as `Done` without a `Result` or `Failed` and don't declare the
Pod, so kube deletes it in the next reconcile. `RunJob` doesn't ask for
that reconcile, so call `kube.RequeueAfter` to delete the Pod soon. Until
you store the state with `Done`, each call reports the result again and
keeps the Pod. So if acting on the result fails, store the state with
`Done` set to false, and the next call reports the result again.

A `Job` with other commits, another task, other tools, or another image
starts a new run, up to the job's `MaxRuns`. A deploy that changes the
agent Pods' spec starts an unfinished run again in a new Pod, which takes
a place in `-max-runs-per-day` but doesn't count toward `MaxRuns`. If the
Pod finds that the branch moved, the agent doesn't run, and `RunJob` gives
the run back and waits a minute for a `Job` with the new head. `Run` waits
twice the repository's `pollInterval` instead if that's longer. If a call
after the wait has the same `Job`, or a deploy changes the agent Pods' spec
during the wait, `RunJob` fetches the commits again in a new Pod, which
counts as a run. The status's `Moved` is true while the run waits for the new
head, and then while a limit holds back the new Pod. If `MaxRuns` holds it
back, `RunJob` doesn't ask for a reconcile, so the run waits for a `Job` that
allows more runs. A run ends after three Pods fail to fetch the commits or
find that the branch moved. If the run's Pod is deleted before the run is
`Done`, kube creates it again and the agent runs again, so `RunJob` counts
another run. When `MaxRuns` or `-max-runs-per-day` allows no more,
`RunJob` ends the run instead, and kube doesn't create the Pod again.

`agent.UsageOutputs` turns what a run used into outputs like `Run`'s, and
`agent.MaxFiles` and `agent.MaxFileBytes` are the most files and bytes that
a result can change, so a controller can skip a run whose result can't fit.

For an agent that resolves a merge, set `Checkout.Merge` to the commit to merge
into the head, and `Checkout.Base` to their merge base. In `Checkout.Merge`,
`Name` is the full name of a ref that contains the commit, such as
`refs/heads/main` or `refs/git-k8s/downstream/heads/main`, and `DisplayName` is
how the prompt names it, such as `main`. `Checkout.Union` lists path patterns in
the gitattributes format whose conflicts the merge resolves with git's union
driver. The `prepare` container then writes the files of the merge that `git
merge-tree --write-tree` makes with `merge.conflictStyle=diff3`, instead of the
head's, which is the same merge as `git.Repo.Merge` with those patterns in
`MergeOptions.Union`. Like `git.Repo.Merge`, the merge doesn't read the commits'
`.gitattributes` files, so only `Checkout.Union` changes how files merge. Each
conflict in a file holds the head's lines, the merge base's lines, and the
merged commit's lines between conflict markers. A file that one side deleted and
the other changed holds the changed version. The work tree leaves out
`.cursorignore` files, as in any task, so when one of them conflicts, the runner
fails the run before the agent starts. The prompt lists the paths that conflict,
and holds the change from the merge base to the merged commit, its paths, and
its commits, as well as the head's. The two diffs share the prompt's 200,000
bytes for a diff, and each gets at least half of them. A review needs every path
that its change touches, but a merge's agent needs only the conflicts, which the
prompt lists in full. So a merge's prompt lists only the first 1,000 paths of
each side's change, within 128 KiB, and says when it leaves some out. The run
fails when more than 1,000 paths conflict, the most files that a result can
change. With `Task.Edit`, the result's `Files` change the merge's files, and the
controller builds the merge commit from them. The result's `MergeTree` names the
tree of the Pod's merge. To build the commit, make the same merge, such as with
`git.Repo.Merge`, and check that its tree is `MergeTree`, so that the commit
holds the files that the agent saw.

The branch must still point to the head when the Pod fetches it, because the
controller pushes what the agent changes onto the head with a lease, which fails
once the branch moves. The merged ref only has to contain the commit, because
the merge is of the commit, so the run goes on when the ref moves past it. If
the ref no longer contains the commit, the run waits as when the branch moves.
While it waits, `JobStatus.Moved` is true, so a controller that keeps a run on
the commits that it started with, as `check-conflicts` does, can tell when to
start a new one.

Agents get no shell. The tools that an agent can have are `read`, `grep`,
`glob`, and `ls`, plus `edit` and `delete` when the task edits files, and
none of them runs a command. A shell would run the branch's code, such as
its build scripts and tests, in the agent's container, which holds the
Cursor API key and can reach Cursor's API. An agent that builds or tests
code needs another sandbox, without the key. So an agent edits files, and
the checks verify what the controller pushes, like any other head.

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

## Merge queue

Every landing moves the parent, so the other open branches fall behind it.
If each of them merged the parent in, every landing would run every check
again on every open branch. When a merge policy lets the `base` check push,
branches land through a queue for each parent instead:

1. A branch joins its parent's queue when its gate passes. The `base` check
   passes a branch that's behind its parent but merges cleanly, with
   `outputs.behind` set to `"true"`, so the branch needs no new commit to
   join.
2. When the branch reaches the front of the queue, the `base` check runs
   again, merges the parent in, and pushes the merge. Every check then runs
   on the new head. A branch that already contains the parent skips this
   step.
3. When the gate passes for the new head, the merge controller lands the
   branch, as [Landing methods](#landing-methods) describes, and the next
   branch moves to the front. When a squash or rebase landing first pushes
   its commit to the branch for the checks, as
   [Which results count](#which-results-count) describes, the branch stays
   at the front while they run on it.

The branches behind the front keep their heads, so each landing runs every
check again on one branch, and only the checks that set `UsesParent`, such
as `base` and `risk`, on the others. The parent's `status.queue` lists its
queue, front first. Each queued branch's `status.queued` records when it
joined, the head that the merge controller last kept in the queue, and its
place, from 1 at the front, which the `QUEUE` column shows. A queued
branch's state is `Queued`, and the `Merged` condition's message says what
it waits for, such as `2 of 3 in main's queue`.

A branch leaves the queue when one of these happens:

- It lands.
- Someone pushes a commit without a `Git-K8s-Fixer` trailer to it, or
  pushes a head that doesn't contain the one before. Fix commits keep the
  branch's place, including the `base` check's merge of the parent. The
  merge controller trusts the trailer, so a person who adds it to a commit
  keeps the branch's place, but the checks still run on the new head.
- Its checks finish without its gate passing, such as a test that fails
  after the merge of the parent. At the front, it leaves sooner, as soon
  as the `base` check fails or the gate fails with its unfinished checks
  counted as passing.
- A squash or rebase landing sets its state to `NeedsRebase`, as
  [Landing methods](#landing-methods) describes. The branch doesn't join
  again until its head or its parent's head changes.
- Someone deletes the branch, which deletes its `GitBranch`.
- Its parent goes away, or the parent's merge policy goes away or can't be
  evaluated.

A branch that leaves joins at the back when its gate passes again.

Three choices shape the queue:

- **Where the queue lives.** The queue is in `GitBranch` status, so it
  needs no new object type, and a controller that restarts continues from
  the queue that it wrote. Only the merge controller's reconcile of the
  parent writes `status.queue`, and kube runs one reconcile of an object at
  a time. Each reconcile reads the last queue from the API server, because
  the cache can lag a write, keeps the branches that are still queued in
  their places, and adds new ones at the back. The front stays the front
  until it leaves, even when several branches become ready at once.
- **How it orders branches.** Branches keep the order in which they joined.
  Branches that join between two reconciles of the parent go by
  `status.queued.since`, which is to the second, then by name.
- **Whether to merge or rebase.** The front catches up with the parent by
  merging it in, as `check-base` did before the queue. A rebase rewrites
  commits that people pushed, so their next push would conflict, and the
  merge controller couldn't tell a check's rebase from a force push. A
  squash or rebase landing still leaves the merge out of the parent.

At the front, the `base` check merges the parent at the head that the
repository controller listed. If the parent moved after that, the check
waits for the next listing, because a merge of the older head would be
behind as soon as it was pushed.

Without `mayPush` on `base`, branches don't queue. Each one lands when its
gate passes, and the `base` check fails a branch that's behind its parent.
The queue lands one branch at a time; it doesn't test several branches
together.

## Landing methods

A merge policy's `landing` field sets how branches land on the branches that
its rule matches. For example, this rule squashes each branch that lands on
`main`:

```yaml
    - match: main
      merge:
        landing: Squash
```

- `FastForward`, the default, moves the parent to the branch's head, so the
  parent ends up at the commit that the checks saw.
- `Squash` makes one commit with the files at the branch's head, on top of
  the parent's head.
- `Rebase` copies each of the branch's commits onto the parent's head, in
  order, and leaves out merge commits.

Like a fast-forward, a squash or rebase lands only a branch that contains the
parent's head, such as one that `check-base` merged the parent into.

A squash keeps the author and message of the branch's only commit that isn't
a merge or a check's fix. When the branch has several such commits, the
message starts with the first one's subject and lists the subject of every
commit that isn't a merge. It ends with the trailers of the commits that
aren't fixes, such as `Signed-off-by`, and a `Co-authored-by` trailer for
each of their authors besides the first. The squashed message never has a
`Git-K8s-Fixer` trailer, so the commit doesn't count as a fix. It always has
every `Git-K8s-Agent` line of the branch's commits, fixes and merges
included, so the commit still counts as a change from an AI agent, as
[Which results count](#which-results-count) explains. A rebase keeps each
commit's author and message, and leaves out a commit that changes nothing,
such as a change that the parent already has.

The merge controller commits as
`git-k8s <git-k8s@users.noreply.github.com>`, which its `-identity-name` and
`-identity-email` flags change. It takes commit times from the commits that
it copies, so making the same landing again makes the same commits.

When the branch is one commit on top of the parent's head, a squash
fast-forwards the parent to it. A rebase does the same for a branch with no
merge commits after the parent's head, because copying its commits changes
nothing. When the parent already has the files at the branch's head, a squash
sets the branch's state to `Merged` and pushes nothing. A rebase does that
only when the parent already has every commit's change, because it leaves out
each commit that changes nothing.

A rebase can't copy every branch. It sets the branch's state to
`NeedsRebase`, with a message that says why, when one of these happens:

- Copying a commit conflicts. A branch whose merge commit resolved a
  conflict with the parent does this, because the rebase leaves the merge
  out.
- A merge commit in the branch makes changes of its own, so the copies don't
  end up with the files at the branch's head.
- A commit has no parent, such as the first commit of an unrelated history.
- A commit to copy has an author that git refuses, or whose date git would
  change: it has no name that git accepts, no date that git can read, or a
  time zone that git can't keep, such as `+9999`. Only tools that write
  commit objects themselves make such commits.

To land such a branch, rebase it yourself, or set `landing: Squash`. A squash
also sets `NeedsRebase` when the commit whose author it keeps has such an
author. To land that branch, rebase it yourself and give that commit a new
author.

Both landings also set `NeedsRebase` for a branch with more than 1,000
commits that the parent doesn't have, or with more than 8 MiB of names,
messages, and other text in those commits. The limits bound the work and
memory that one branch takes, because a rebase runs two git commands for each
commit that it copies, and the controller keeps every commit's message in
memory. To land such a branch, squash it yourself into one commit on top of
the parent's head. With `landing: Rebase`, rebasing it yourself so that it
has no merge commits also works. The controller fast-forwards such a branch
without reading its commits, so the limits don't apply.

### Which results count

Squash and rebase landings make commits that no check saw. A squashed commit
has the files at the branch's head, on top of the parent's head, and so does
the last commit of a rebase. Those are the files and the parent head that the
checks saw, so a check that reads only files gives the new commit the same
result. As with a fast-forward, no check sees a rebase's earlier commits.

Other results depend on more than the files, such as those of a check that
reads the commits' messages, authors, signatures, or trailers like
`Signed-off-by`, or that counts the branch's commits. An agent that reviews
commit messages as well as the change is another. So a result for the
branch's head counts for the new commit only when its check sets `FilesOnly`
in its `checks.Check`, which gives its results `filesOnly: true`. A check
without `FilesOnly` costs one more round of checks, as the end of this section
describes.

The built-in checks set `FilesOnly`, except `check-review`, `check-deps`, and
`check-conflicts`. The agent of an [agentic check](#agentic-checks) reads the
subjects of the branch's commits, and `check-conflicts` replays commits with
their authors and messages. `check-base` passes for any commit that builds on
the parent's head, `check-gofmt` and `check-gotest` read only the files, and
`check-risk` compares them with the parent's head. `check-approval` reads only
the `GitBranch`, and an approval is for the change, which the new commit makes
too. `maxAutomatedCommits` counts fix commits by their trailer, but it limits
what checks push, and the gate doesn't read it.

`check-risk` also rates a change `high` when one of its commits has a
`Git-K8s-Agent` trailer, so its result depends on commit messages too. It
still sets `FilesOnly`, because both landings keep those trailers. A squash
keeps every `Git-K8s-Agent` line of the branch's commits, so the squashed
commit gets the head's rating. A rebase keeps each commit's message but
leaves out merge commits and commits that change nothing, so the head's
rating is never lower than the new commit's. The check's message doesn't
count those commits, because a squash makes one commit of them. If a squash
dropped the trailers, `check-risk` would rate a rewritten branch's squashed
commit `low` when it runs again, so the commit could land without a new
approval, and the parent's history wouldn't show which changes came from
agents. Dropping `FilesOnly` wouldn't fix that, because the check would read
the same squashed message.

When the counted results pass the gate, the controller lands the new commit
without another round of checks. It pushes the commit to the parent, with a
lease on the parent's head. The same atomic push deletes the branch, with a
lease on its head, or moves the branch to the new commit when
`deleteMergedBranches` is off. A branch that stays is then at its parent's
head, so it shows `Merged` instead of commits that the parent doesn't have.
If the parent or the branch moved since the repositories controller listed
them, the push changes neither, and the controller tries again.

When the gate doesn't pass on the counted results alone, the controller
pushes the new commit to the branch instead, with a lease on the branch's
head, and sets the branch's state to `Rewritten`. The checks run on the new
commit, and when the gate passes, the parent fast-forwards to it. In a
[merge queue](#merge-queue), the branch keeps its place at the front until
then. `check-approval` passes only for the head that the annotation names,
so a rewritten branch needs a new approval.

A check with `mayPush: true` can push a fix on top of the new commit. While
the parent doesn't move, a squash landing doesn't squash its own commit and
the fixes after it again, so they land by fast-forward, with each fix as its
own commit. Another squash would keep the fixes' files but drop their
commits, so a check that reads commits could push the same fix forever.
`maxAutomatedCommits` counts only the fixes after the squashed commit,
because it doesn't have the trailers of the fixes before it.

Moving a branch that stays, and pushing a rewritten branch, replace the
branch's commits on the remote. Before you push to a branch that the
controller moved, reset your copy to the remote's.

A remote can refuse to replace a branch's commits or to delete the branch.
Git's `receive.denyNonFastForwards` and `receive.denyDeletes` settings do
that, and so do GitHub rules that block force pushes or deletions. When the
remote refuses the branch's part of a landing push, the controller pushes
the parent alone, with the same lease, as a fast-forward landing does. If
the remote refused to delete the branch, the controller tries to move the
branch to the parent's new head instead, so that it shows `Merged`. A branch
that the controller can't change keeps its commits, and the `Merged`
condition's message says why. It shows `Merged` once a check such as
`check-base` merges the parent into it.

If the remote refuses to replace the branch's commits with the new commit
for the checks, the controller sets the branch's state to `NeedsRebase`
instead of `Rewritten`. To land such a branch, squash or rebase it yourself
onto the parent's head and push the result to a new branch, or let the
remote accept force pushes to proposal branches.

## Dependency updates

`git-k8s-deps` is a controller that keeps the Go modules that repositories
require up to date. It pushes each update to its own branch under a prefix,
`deps/` by default, and each branch lands through its parent's merge policy
like any other branch. When an update breaks the tests, `check-deps` has an
AI agent fix the code.

To keep a parent's modules up to date, add a rule that matches branches
under the prefix and names that parent. The parent's policy in this example
also lists the checks that dependency branches need:

```yaml
spec:
  branches:
    - match: main
      merge:
        checks:
          - name: base
            mayPush: true
          - name: gotest
          - name: deps
            mayPush: true
          - name: risk
          - name: approval
        when: >-
          checks.base.passed && checks.gotest.passed && checks.deps.passed &&
          (checks.risk.outputs.level == "low" || checks.approval.passed)
    - match: deps/**
      parent: main
```

Every `-interval`, one hour by default, the controller reads the `go.mod`
files on the parent's head. For each module that they require directly, it
reads the module's versions from the module proxies in `-goproxy`, and picks
the newest release with the same major version. It runs `go get` in a Pod to
make the update, commits the `go.mod` and `go.sum` files that `go` changed on
the parent's head, and pushes the commit to the module's branch, such as
`deps/go/example.com/greet@v1`. The commit has a
`Git-K8s-Deps: go MODULE VERSION` trailer. The same update of the same parent
head always makes the same commit.

`check-risk` rates a patch or minor release of a module that the repository
already requires `low`, unless the update brings in a module that the
repository didn't require before or changes a `go` or `toolchain` line.
[Risk ratings](#risk-ratings) lists the rules. Under the gate in the example,
a low-risk update lands as soon as its checks pass, and a person approves the
rest.

### Versions

The controller updates each module that a `go.mod` file requires without an
`// indirect` comment, unless the file replaces the module. `go get` updates
indirect requirements as the direct ones need. Each module and major version
gets its own branch, so an update that breaks the tests doesn't hold back
the others, and each change stays small enough to rate low risk. The
controller never moves a module to another major version, because major
versions make incompatible changes, and from `v2` on each one has its own
module path.

Compromised releases are often pulled within days, so the controller takes a
version only once it's `-min-age` old, 72 hours by default, both by the time
that the module proxy reports for it and since the controller first saw it in
the module's list of versions. A proxy such as `proxy.golang.org` reports the
time of the version's commit, not when the release came out, and whoever
makes a commit can set its time. When a newer version is younger than that,
the controller looks again once the version is old enough.

`go get` can also raise other requirements to newer versions, and add modules
that a `go.mod` file didn't require. The minimum age covers those versions
too. Before the controller pushes an update, each version that the update
raises a requirement to must be `-min-age` old by both measures. A raised
version waits from when the controller first saw it, either in its module's
list as a version that the controller could update to, or in an update that
raised a requirement to it. The controller doesn't look for versions of
indirect requirements or new modules ahead of time, so their versions usually
wait from when an update first raises a requirement to them, and the update
takes a second update Pod. Proxies don't list pseudo-versions, and a proxy
can serve a version before it lists it, so those versions wait from then
too, and keep that time until the proxy lists them.

`go get` also raises a requirement to a version that its module retracts,
with only a warning. The controller doesn't push such an update. It logs
that the update failed, and makes the update again after `-interval`. When
the update would replace a branch whose `go.mod` files raise a requirement
to a retracted version too, including the version of the branch's own
module, for example because the controller pushed the branch before the
module retracted the version, the controller deletes the branch. It deletes
a branch that stays behind its parent in a merge queue the same way, without
making the update again, as [Branches](#branches) describes.

When no module proxy has a module or version that an update raises a
requirement to, the controller can't check the version, so it doesn't push
the update either. It logs that the update failed, and starts no update Pod
for the update until `-interval` later, even when the parent moves.

While an update waits, the controller doesn't push it. It logs the version
that the update waits for and until when, and starts no update Pod for the
update until then, even when the parent moves. Then it makes the update again
in a new Pod, and pushes it if every version that it raises is old enough.
The wait holds back only that version of the module. Once a newer version is
old enough, the controller makes that update in its own Pod, and it can wait
too. The controller forgets the wait of an update that it no longer needs,
such as the older version's.

The version of a branch that the controller owns, which the trailer of the
branch's update names, was old enough when the controller pushed it, so it
doesn't wait again, even after a restart. A branch whose version the module
retracts or a `go.mod` file excludes is still deleted.

For other versions, the controller keeps when it first saw each one in the
ConfigMap in its own namespace that `-seen-configmap` names,
`git-k8s-deps-first-seen` by default, so that a restart, or another replica
taking over, doesn't restart their wait. Each line of the ConfigMap's
`first-seen` key holds a proxy URL, a module path, a version, and when the
controller first saw the version, in that proxy's list of the module's
versions or in an update that raised a requirement to it. A line ends with
`unlisted` when an update raised a requirement to the version while the proxy's
list left the version out. The controller reads the ConfigMap before it looks
for newer versions, and writes it when the times change. It records only
versions that it could update to and versions that an update raises a
requirement to. It drops a version when the proxy that listed it stops listing
it, and if the version comes back, it waits again. It keeps the times of
pseudo-versions, which proxies don't list, and of `unlisted` versions until the
proxy lists them. When the controller can't read the ConfigMap, it logs a
warning, uses the times in its memory, and doesn't write the ConfigMap.
`generate` lets the controller read and write ConfigMaps only in its own
namespace. With `-seen-configmap=`, the controller keeps the times only in
memory, so after a restart, each of these versions waits `-min-age` again.

The controller also skips prereleases, versions that a `go.mod` file
excludes, and versions that the module retracts. To keep the controller from
taking a version, exclude it in `go.mod`. To keep the controller away from a
module, add a rule for the module's branch, without a parent, before the
prefix's rule, such as `match: deps/go/example.com/big@v1`.

The controller ignores `go.work` files. It also skips `go.mod` files in
`testdata` and `vendor` directories, in modules that vendor their
dependencies, and in directories whose names hold characters other than
letters, digits, dots, hyphens, and underscores. It skips a `go.mod` file
whose `go` line is older than 1.17, and logs a warning. Such a file lists
only the requirements that other requirements don't imply, so `go get` can
raise a module that the build uses without the file showing it, and neither
the minimum age nor `check-risk` would see the new version. To have the
controller update the module, raise its `go` line to 1.17 or later and run
`go mod tidy`. The controller updates a `go.mod` file that has no `go` line:
`go get` adds one, the file then lists every module that the build uses, and
`check-risk` rates the change high.

### Branches

When a newer version comes out before a branch lands, the controller replaces
the branch's commit with an update to the newer version, so each module keeps
one branch. When the parent has no [merge queue](#merge-queue), the
controller also remakes a branch that falls behind its parent, so that the
branch can fast-forward the parent. Every push has a lease on the head that
the controller read, so the controller never overwrites a push that it
didn't see.

When the parent has a merge queue, as in the example, a branch that falls
behind stays instead. Remaking it would push a head that doesn't contain the
one before, which sends the branch to the back of the queue, and would drop
fix commits from checks, such as `check-deps`. `check-base` merges the parent
in when the branch reaches the front. The branch stays only while it merges
cleanly with the parent and has automated commits left under
`maxAutomatedCommits` for that merge. Without a queue, `check-base` doesn't
merge the parent in, so the controller remakes a branch that falls behind
even when the branch has fixes, and the fixes are lost. While a branch stays
behind its parent, the controller deletes it if it raises a requirement to a
version that its module retracts. A newer version still replaces the branch
and its fixes.

The controller changes and deletes only branches whose commits beyond the
parent are all its updates and checks' fixes. An update is a commit that the
controller committed, as its `-identity-email`, whose last trailer is its
`Git-K8s-Deps` trailer. A fix is a commit that a check committed, as
`-check-identity-email`, with a `Git-K8s-Fixer` trailer. To take over a
branch, push a commit of your own to it. Amending or squashing the branch's
commits also makes you their committer, so the branch becomes yours. When
no update is left for a module, for example because its branch landed or
someone updated the module on another branch, the controller deletes the
module's branch.

The merge controller also commits as `git-k8s@users.noreply.github.com` by
default. When a squash landing pushes a squashed commit to a dependency
branch for the checks, as [Which results count](#which-results-count)
describes, the commit keeps the update's author and `Git-K8s-Deps` trailer.
If the branch had a commit of yours or an agent's fix, the squashed commit
ends with a `Co-authored-by` or `Git-K8s-Agent` trailer, so the controller
leaves the branch alone and the change isn't lost. If you amended the update
and kept its message instead, the squashed commit looks like an update, so
the controller can replace it and drop your change. To keep a change, push
it as a commit of its own.

The controller doesn't authenticate committers. Anyone who can push to the
repository can make commits that look like updates and fixes, and the
controller then treats the branch as its own: it replaces or deletes the
branch, and takes the version that the update's trailer names as old enough.
That gives nothing beyond push access, because the parent's merge policy
decides what lands, and it treats the branch as it would the same change
pushed under the person's own name.

### Agent fixes

`check-deps` passes on branches outside its `-prefix`, so the parent's policy
can list it for every branch. It also passes when the policy doesn't list
`gotest`. On a dependency branch, it waits for the `gotest` check's result
for the branch's current commits, and passes when the tests pass. When the
tests fail, for example because a module changed its API, and the policy
lets the check push, the check runs an agent with the `agent` package, as
`check-review` does. The agent gets the test output and the update's change,
and can edit files. The check pushes what the agent changed as a fix with
`Git-K8s-Fixer: deps` and `Git-K8s-Agent: deps` trailers, and `check-gotest`
tests the new head.

The agent runs in this check instead of in `git-k8s-deps`, so its fix takes
the same path as other checks' fixes: the policy must let the check push, the
fix counts toward `maxAutomatedCommits`, and the push has a lease on the
commit whose tests failed.

The check fails, and the branch waits for a person, when the policy doesn't
let it push, when the branch has no automated commits left, and when the
agent can't fix the tests, changes a `go.mod`, `go.sum`, `go.work`, or
`go.work.sum` file, or changes no files. The limits in
[Agentic checks](#agentic-checks), such as `maxAgentRuns`, cap its agent
runs. Its fix commit makes `check-risk` rate the branch `high`, so a person
approves the fix before it lands.

### Update Pods

`go get` downloads modules that anyone can publish, so the controller runs it
in a Pod, as `check-gotest` runs tests. Each Pod makes up to 10 updates on
one parent's head, and has three containers:

- The `prepare` init container fetches the parent's head with the
  repository's credentials. It's the only container that gets them.
- The `update` init container runs `go get`, and then `go mod tidy` in
  modules that were tidy, as user 65532 with no service account token, no
  privileges, and a read-only root file system. `GOPROXY` holds only the
  proxies in `-goproxy`, so `go` downloads modules only from them and runs no
  version control tools. `GOTOOLCHAIN=local` stops it from downloading
  another Go toolchain.
- The `result` container, from the agent runner's image, serves the `go.mod`
  and `go.sum` files that `go` changed. The controller fetches them and
  checks them against their digest, as
  [Agentic checks](#agentic-checks) describes.

Update Pods run in the parent's namespace and meet the `restricted` Pod
Security Standard. The `git-k8s-check-pods` policy applies only to checks'
service accounts, so update Pods don't need the namespace to opt in to check
Pods.

The controller accepts only the `go.mod` and `go.sum` files next to the
`go.mod` files that it asked to update. It rejects a `go.mod` file that
changes anything other than its requirements and its `go` and `toolchain`
lines, but not one whose other directives `go get` sorted. The `go` command
checks the `go.sum` checksums when it builds the branch. At most `-max-pods`
update Pods run at once across all namespaces, and kube deletes each one once
the controller has its result. When an update fails, the controller logs why
and tries again after `-interval`. An update also fails when an image's name
isn't valid, when kube still can't schedule the update Pod 5 minutes after
creating it, and when a Secret is still missing or an image still can't be
pulled 5 minutes after the container can start.

Each update Pod's volumes have size limits. The repository can use up to
`-source-size`, 2Gi by default, and the home directory, which holds Go's
module and build caches, up to `-go-cache-size`, 4Gi by default. The init
containers request 1Gi of ephemeral storage, and their limits cover all the
volumes. When a Pod uses more than a limit, the kubelet evicts it, and its
updates fail with the kubelet's reason.

Update Pods need to reach the repository, the module proxies, and the
checksum database in `-gosumdb`, and the controller needs to reach them on
TCP port 8080. A NetworkPolicy like the one in
[Agentic checks](#agentic-checks), with the Pod label
`app.kubernetes.io/name: git-k8s-deps` and the namespace `git-k8s-deps`,
allows that. For `check-deps`'s agent Pods, allow requests from the
namespace `check-deps` too.

Until git-k8s has a mirror, the controller pushes with the repository's
credentials, which can push to any branch, so it refuses to push branches
outside its prefix. It reads the repository's Secret, so `generate` lets it
read every Secret, and `config/policy.yaml` stops it from approving or
changing `GitBranch` objects. [Push dependency branches to the
mirror](future-work.md#push-dependency-branches-to-the-mirror) proposes the
fix.

### Install the dependency controller

To install `git-k8s-deps` and `check-deps`, build and push the agent runner's
image. In each namespace with dependency branches, create the
`cursor-api-key` Secret and opt the namespace in to check Pods, as
[Agentic checks](#agentic-checks) describes. `git-k8s-deps` runs its result
containers from that image, and `check-deps` runs agents in it:

```sh
go run ./cmd/git-k8s-deps generate -registry=REGISTRY -base=cgr.dev/chainguard/git:latest -- -result-image="${image}" | kubectl apply -f -
go run ./cmd/check-deps generate -registry=REGISTRY -base=cgr.dev/chainguard/git:latest -- -agent-image="${image}" | kubectl apply -f -
```

Upgrade the core program first, because it installs `config/policy.yaml`
when it starts, and the second policy there stops `git-k8s-deps` from
changing `GitBranch` objects. With `-install-policies=false`, apply
`config/policy.yaml` instead. The policy recognizes `git-k8s-deps` only as
the service account `git-k8s-deps` in the namespace `git-k8s-deps`, so
install it there, as `generate` does unless you set `-namespace`.

`check-deps` takes `-prefix`, which must match the controller's, and the
flags in the `check-review` table. It exits at startup when `-prefix` isn't a
branch-name prefix that ends with `/`. `git-k8s-deps` takes these flags:

| Flag | Default | Description |
| --- | --- | --- |
| `-result-image` | Required | Image that serves update results, built from `agent/runner/Dockerfile` |
| `-prefix` | `deps/` | Branch-name prefix of the controller's branches, ending with `/` |
| `-identity-email` | `git-k8s@users.noreply.github.com` | Author and committer email of the controller's updates |
| `-check-identity-email` | `git-k8s@users.noreply.github.com` | Committer email of the fixes that checks push: the checks' `-identity-email` |
| `-interval` | `1h` | How often to look for newer versions |
| `-min-age` | `72h` | How old a version must be, both by the time that the module proxy reports for it and since the controller first saw it, before the controller takes it or pushes an update that raises a requirement to it |
| `-seen-configmap` | `git-k8s-deps-first-seen` | Name of the ConfigMap in the controller's namespace that keeps when the controller first saw versions, or empty to keep the times only in memory |
| `-goproxy` | `https://proxy.golang.org` | Comma-separated URLs of the module proxies to read modules from; `direct` and `off` aren't allowed |
| `-gosumdb` | `sum.golang.org` | `GOSUMDB` for `go get`, or `off` |
| `-go-image` | `cgr.dev/chainguard/go:latest` | Image that runs `go get`; it needs `go`, `git`, `sh`, `base64`, `sha256sum`, `tail`, and `cut` |
| `-git-image` | `cgr.dev/chainguard/git:latest` | Image that fetches the source; it needs `git` and `sh` |
| `-timeout` | `15m` | Longest that an update Pod can run |
| `-source-size` | `2Gi` | Most disk space that an update Pod's copy of the repository can use |
| `-go-cache-size` | `4Gi` | Most disk space that an update Pod's Go module and build caches can use |
| `-max-pods` | 10 | Most update Pods to run at once, in all namespaces; 0 means no limit |
| `-runtime-class` | None | RuntimeClass for update Pods, such as `gvisor` |

Update Pods get no credentials for modules, so the controller can't update a
private module unless a proxy in `-goproxy` serves it. An update that needs
a newer Go than the one in `-go-image` fails. The controller remembers only
in memory which updates failed and which wait for the versions that they
raise. After a restart, it makes each of them again in a new Pod once the
version that it updates to is old enough. That's right away when the
ConfigMap that `-seen-configmap` names kept when the controller first saw
the version, and `-min-age` after the restart with `-seen-configmap=`. The
controller still doesn't push an update whose raised versions aren't old
enough.

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
changing `status.checks`. A check that doesn't run as `check-NAME` in the
namespace `check-NAME` needs an entry in the `git-k8s-checks` ConfigMap to
write results. Server-side apply already keeps the controllers' writes
apart; the policy stops a buggy or compromised check from writing another
check's result. It also stops every service account except the core program's
from changing `status.diverged`, which names the commit that `check-conflicts`
merges or replays. The second stops every git-k8s service account from setting
the `approve` and `approved-by` annotations, which are for people, and stops
checks and `git-k8s-deps` from changing `GitBranch` objects at all. RBAC
also keeps every check except `check-gotest`, `check-review`, `check-deps`,
and `check-conflicts`, which own Pods, from patching `GitBranch` objects.
`generate` grants that permission to a program that owns objects, such as
these checks and `git-k8s-deps`, because it can't tell whether an owned
object needs a finalizer on its owner. The second policy denies the
annotation that kube adds with that finalizer, so these programs can own
only namespaced objects in the branch's namespace.

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
add a ValidatingAdmissionPolicy that denies a Pod with the check's label,
such as `kube.imjasonh.github.io/controller=check-gotest`, unless its
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

Each namespace that holds a `GitRepository` whose merge policy lists
`gotest`, `review`, or `deps`, or lists `conflicts` with `mayPush: true`
while `check-conflicts` runs with `-agent-image`, must opt in to check Pods
and enforce the
`restricted` Pod Security Standard, or the third policy denies the check's
Pods:

```sh
kubectl label namespace NAMESPACE git-k8s.imjasonh.com/check-pods=true pod-security.kubernetes.io/enforce=restricted
```

Replace `NAMESPACE` with the namespace of the `GitRepository`. The namespace
can't be `git-k8s` or start with `check-`. If it has the label
`pod-security.kubernetes.io/enforce-version`, the label's value must be
`latest`. Until it has both labels, the branch's `gotest`, `review`, or
`conflicts` result, or a `deps` result that runs an agent, stays `Running`,
and its message says why kube couldn't create the Pod. kube tries again with
backoff that grows to 5 minutes, plus up to 10% jitter, so it creates the Pod
within about 5.5 minutes after you label the namespace, without a new push.

If `check-gotest`, `check-review`, or `check-conflicts` already runs, label
the namespaces of their repositories before you upgrade the core program,
which installs `config/policy.yaml` when it starts, or before you apply
`config/policy.yaml` yourself. Otherwise the policy denies their Pods until
you do.

### Admission policies

The core program installs `config/policy.yaml` when it starts, before it
reconciles. It labels the policies, their bindings, and the `git-k8s-checks`
ConfigMap with `kube.imjasonh.github.io/managed-by=git-k8s`, and applies
them again each time it starts, but doesn't watch them. The first two
policies name the core program's service account and read the
`git-k8s-checks` ConfigMap in the `git-k8s` namespace, and the third keeps
checks' Pods out of that namespace. Install the core program there, as
`generate` does unless you set `-namespace`.

If a policy or its binding goes missing, `PoliciesInstalled` turns `False`,
and its message says to restart the core program. Only the replica that
holds the leader election lease installs `config/policy.yaml`, so deleting a
standby replica's Pod doesn't install it again. Restart the Deployment:

```sh
kubectl -n git-k8s rollout restart deployment/git-k8s
```

`PoliciesInstalled` also turns `False` when no binding for a policy denies
every request that the policy rejects. A binding can let some of them
through when its `validationActions` doesn't hold `Deny`, when its policy
reads parameters and its `paramRef.parameterNotFoundAction` isn't `Deny`,
when its `matchResources` sets resource rules, or when a selector in its
`matchResources` sets `matchLabels` or `matchExpressions`. The API server
ignores the `paramRef` of a binding whose policy doesn't read parameters,
such as the third and fourth policies, so the condition does too. The
message gives a `kubectl patch` command that makes the binding from
`config/policy.yaml` deny all of them again, without a restart. For a
binding that someone set to `Warn`, the command is:

```sh
kubectl patch validatingadmissionpolicybinding git-k8s-branches --type=merge \
  -p '{"spec":{"validationActions":["Deny"]}}'
```

A binding set to `Warn` stops the core program the next time that it
starts, whether you restart it or a node drain or an upgrade does. The core
program's apply keeps the entries that others add to a binding's
`validationActions`, so it adds `Deny` next to `Warn`, and the API server
rejects a binding that has both. The core program exits, each replica that
takes the lease after it exits too, and nothing lands until you patch or
delete the binding. `PoliciesInstalled` reports a binding from
`config/policy.yaml` set to `Warn` even while another binding for the same
policy denies. To install the binding from `config/policy.yaml` again
instead of patching it, delete the binding, and then restart the core
program.

For a binding that someone limited with `matchResources`, the command
removes `matchResources`. Restarting the core program doesn't remove it,
because `config/policy.yaml` sets no `matchResources`, and the core
program's apply changes only the fields that the manifest sets.

The condition doesn't compare the policies, or the bindings' other fields,
with `config/policy.yaml`, so it doesn't report a policy with
`failurePolicy: Ignore` or with a `matchConditions` entry that never
matches. When the core program starts, its apply restores the fields that
the manifest sets, such as `failurePolicy` and the validations. Applying
`config/policy.yaml` yourself does too. Neither removes a `matchConditions`
entry that someone adds under another name, because the API server merges
that list by name. Remove such an entry with `kubectl edit`.

`generate` grants the core program `create` and `patch` on each policy,
binding, and ConfigMap in `config/policy.yaml`, by name, and `get` on the
`git-k8s-checks` ConfigMap, which the bindings of the first two policies
name as their parameter. The API server lets only someone who can read
every ConfigMap create a policy whose parameter is a ConfigMap, and it
checks that as `get` on a ConfigMap named `*`. No ConfigMap can have that
name, so `generate` also grants `get` on the name `*`, and the core program
still can't read any other ConfigMap.

The core program can't create other admission policies, but a compromised
core program could rewrite these policies, their bindings, and the
`git-k8s-checks` ConfigMap, to weaken them or to deny other requests in the
cluster. It already decides what lands, so it could land a branch without
its checks anyway. To keep the policies out of its reach, for example in a
cluster that manages admission policies separately, install it with
`-install-policies=false`, which also leaves out the permissions, and apply
`config/policy.yaml` yourself:

```sh
go run ./cmd/git-k8s generate -registry=REGISTRY -base=cgr.dev/chainguard/git:latest -- -install-policies=false |
  kubectl apply -f -
kubectl apply -f config/policy.yaml
```

With `-install-policies=false`, the message of a `False` `PoliciesInstalled`
says to apply `config/policy.yaml` instead of restarting the core program.
The core program doesn't apply the manifest when it starts, so a binding set
to `Warn` doesn't stop it, and the condition doesn't report one while another
binding for the same policy denies.

### Check service accounts

The first two policies recognize a check by the service account that makes
each write. `generate` installs `check-NAME` with the service account
`check-NAME` in the namespace `check-NAME`, and the policies treat that
service account as the check `NAME`. For a check that runs as another
service account, such as a check installed with `generate -namespace=checks`,
add an entry to the `git-k8s-checks` ConfigMap in the `git-k8s` namespace.
Each key is `NAMESPACE.SERVICE_ACCOUNT`, and its value is the check's name:

```sh
kubectl -n git-k8s patch configmap git-k8s-checks --type=merge \
  -p '{"data":{"checks.check-approval":"approval"}}'
```

An entry overrides the `check-NAME` convention, so an entry with an empty
value stops that service account from writing results. The policies ignore
an entry for the core program's service account, `git-k8s.git-k8s`, so an
entry can't let the core program write a result or stop it from changing
`GitBranch` objects. The core program applies the ConfigMap without data, so
restarting it keeps your entries.
Anyone who can change ConfigMaps in the `git-k8s` namespace can decide which
service accounts write which results, so give that permission only to people
who can install checks.

The third policy doesn't read the ConfigMap, so an entry doesn't change
which Pods a check can write. A check that owns Pods and runs as another
service account needs a policy of its own.

While the ConfigMap is missing, the API server denies every create and update
of a `GitBranch` or its status, including people's, with a message that says
`no params found for policy binding`. To create the ConfigMap again, run
`kubectl -n git-k8s create configmap git-k8s-checks`, or restart the core
program with `kubectl -n git-k8s rollout restart deployment/git-k8s`. With
`-install-policies=false`, apply `config/policy.yaml` instead.

## Test

The unit tests call each reconciler with `kube.Fake` and a real git server
that runs in the test process:

```sh
go test -race ./...
```

The agent runner in `agent/runner` has its own tests, which its image build
also runs:

```sh
cd agent/runner && npm ci && npm test
```

The repository's daily dependency update upgrades the runner's npm
dependencies too, and runs these tests.

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

The end-to-end test builds the agent runner's image with Docker, and runs
`check-review` and `check-deps` with the `fake` backend, which needs no API
key. The fake agent fails a change that adds a line with `DO NOT MERGE` in
it, and deletes those lines when the check can push. When it can edit files,
it also replaces each line that holds `FAKE AGENT FIX:` with the text after
it. It runs `check-conflicts` with the `fake` backend too. There, the fake
agent resolves each conflict by keeping the branch's lines and then the other
side's, and fails a conflict with `DO NOT MERGE` in it. The git server also
serves a Go module proxy. The test publishes module versions to it, makes it
`go-cache`'s upstream, and checks that `git-k8s-deps` lands a patch release
without approval, that the fake agent fixes a release that breaks the tests,
and that `git-k8s-deps` keeps when it first saw a version through a restart.

## Limitations

- The controllers poll remotes; they don't receive webhooks. A check's status
  write runs the repositories controller again, so a check's fix is listed
  soon after the check pushes it. The controller lists a repository at most
  once every 5 seconds, or every `pollInterval` if that's shorter.
- Remotes authenticate with HTTP basic auth only.
- `check-gotest` runs Pods in the `GitBranch`'s namespace and doesn't add a
  NetworkPolicy, so a test can reach anything that the namespace's Pods can
  until you [add one](#restrict-test-pods-network).
- An approval names one head, so a branch that needs one needs another after
  the `base` check merges its parent in at the front of the queue. The
  branch leaves the queue until someone approves the merge, then joins at
  the back. While other branches keep landing, it might never land.
- A check that doesn't finish at the front of a queue holds up the branches
  behind it while the front can still land.
- `check-review` and `check-conflicts` read repository credentials, so
  `generate` lets them read every Secret, including the Cursor API key,
  which only their agent Pods use. Like `check-gotest`, they can also create
  Pods in every namespace, and `check-conflicts` can even without
  `-agent-image`. Installing them with `generate -watch-namespace` limits
  their Secrets and Pods to one namespace.
- Like `check-review`, `git-k8s-deps` reads repository credentials and
  creates Pods, so `generate` lets it read every Secret and create Pods in
  every namespace. Only its own code keeps its pushes under its prefix.
- `git-k8s-deps` keeps at most 256 KiB of first-seen times in its ConfigMap,
  and drops the oldest first, so after a restart, a version whose time it
  dropped waits `-min-age` again. When a write leaves out times, it logs a
  warning that says how many. With more than one shard, or for a moment while a
  Deployment with one replica rolls out, two controllers can write the
  ConfigMap at once, and the last write wins. Each one writes its times again
  the next time that it reads the module's versions, so a time is lost only
  when the controller that saw the version stops first.
- Squash and rebase landings make unsigned commits, even from signed ones.
  With a check that requires signed commits, use `FastForward`.

[`future-work.md`](future-work.md) proposes fixes for these, and lists the
other known gaps.
