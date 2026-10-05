# git-k8s

git-k8s runs a branch workflow on Kubernetes. It tracks a git repository's
branches as `GitBranch` objects, and keeps a copy of the repository on a git
server in the cluster, the mirror. It runs checks on branches that propose
changes to another branch, and checks can push commits that fix what they
find. When the parent's merge policy passes, git-k8s lands the branch on the
parent by fast-forward, squash, or rebase. The mirror pushes every change to
the external repository, such as one on GitHub, and takes the changes that
people push there.

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

For each branch, the first rule whose `match` glob matches applies, and
branches that match no rule aren't tracked. A branch whose rule names a
`parent` is a proposal to that parent. The parent's rule says what a proposal
needs before it lands.

`url` must be an `https://`, `http://`, `git://`, or `ssh://` URL, or an
scp-like address with a user name, such as `git@example.com:app.git`. Without
a user name, write an `ssh://` URL, such as `ssh://example.com/~/app.git`. The
API server rejects other URLs, and git-k8s runs git with `GIT_ALLOW_PROTOCOL`
set to those transports. Its git commands put `--end-of-options` before every
URL, branch, and commit, so git can't read one as an option. git-k8s doesn't
track branches whose names start with `-` or aren't valid ref names.

Put credentials in `secretRef`, not in `url`, because
`kubectl get gitrepositories` shows each URL.

The `git-k8s` program, which this README calls the core program, serves the
mirror and runs three controllers. Each check runs as its own program. The
mirror is a `kube.Serve` handler, and each controller is a `kube.For`
reconciler:

- The **mirror** keeps a copy of each repository on a persistent volume and
  serves it over git's smart HTTP protocol. The copy is the repository's
  source of truth, and checks fetch from it and push to it. The external
  repository is a downstream copy. See [The mirror](#the-mirror).
- The **repositories** controller syncs each copy with its external
  repository, and declares a `GitBranch` for each tracked branch in the copy
  with `kube.Own`. The spec holds the branch's head, its parent's head, and
  the parent's merge policy. When a branch disappears, kube deletes its
  `GitBranch`, because the reconcile stops declaring it.
- Each **check** controller is its own program. It reconciles `GitBranch`
  objects through a view type that declares only the check's own entry in
  `status.checks`. kube writes the view's status with server-side apply, so
  each check manages one map key and never sees or rewrites another check's
  result. Results record the commits they're for, and the merge controller
  ignores results for older commits.
- The **merge** controller evaluates the merge policy's `when` expression
  over the fresh results. When it passes, the controller lands the branch in
  the mirror's copy, as [Landing methods](#landing-methods) describes, but
  only if the parent still points to the commit that the checks saw, so it
  never overwrites a parent that moved in the meantime. It then deletes the
  branch if the policy says to, and the repositories controller pushes both
  changes to the external repository.

The core program's third controller, **check-runs**, copies check results to
GitHub as check runs. See [Check runs](#check-runs).

The checks and the merge controller read each branch's repository as a
`gitk8s.Repository`, a `GitRepository` without its status, so the
repositories controller's status writes don't run them again.

Git objects live in the mirror's copies, and each check that reads files
keeps a local copy of the repositories that it reads. Only commit SHAs go
into Kubernetes objects. Apart from [events](#events), which the API server
deletes after an hour by default, no object records a single push or check
run, so the API server holds a bounded amount of state.

After a branch lands, `kubectl get gitbranches` shows what's still open:

```
NAME                    BRANCH   HEAD                                       PARENT   STATE              AGE
app-c-auth-f684729ccf   c/auth   d28547a6c959905ea8dc037ac37541167a50638c   main     WaitingForChecks   9s
app-main-9157892a7c     main     610a7734a0b4d1bc1991a669d9feb35fd159219b                               48s
```

The `Merged` condition's message explains a `WaitingForChecks` state, for
example `checks: approval Failed, base Passed, gofmt Passed, risk Passed (high)`.

## The mirror

The mirror serves the copy of each `GitRepository` at `/NAMESPACE/NAME.git`.
`generate` installs the core program behind the Service `git-k8s` in the
namespace `git-k8s`, so the copy of the `GitRepository` `app` in the
namespace `team` is at `http://git-k8s.git-k8s.svc/team/app.git`. The
Service's port 80 forwards to port 8081 of the core program's Pod, where
`kube.Serve` listens. If you install the core program under another name or
in another namespace, set `-mirror` to the mirror's base URL on `check-base`,
`check-gofmt`, `check-risk`, and `check-gotest`. Also set the core program's
`-mirror-namespace` and `-mirror-labels` to its own namespace and labels,
which it uses in the [test Pods' NetworkPolicy](#sandboxed-checks).

### Sync with the external repository

The mirror acknowledges a push as soon as its copy has it, and syncs it to
the external repository afterward, so git-k8s keeps working while the
external repository is down. After each push, the mirror triggers a
reconcile of the `GitRepository` with `kube.Trigger`, and the merge
controller does the same after each landing. The reconcile pushes each
branch that changed only in the copy to the external repository with
`git push --force-with-lease`, so it never overwrites a change that it
hasn't fetched. If `kube.Trigger` can't queue the reconcile, such as while
the core program shuts down, the next poll syncs the push. git doesn't retry
a push, so the mirror keeps it either way.

The external repository can't be watched, so the repositories controller
fetches its branches once each `pollInterval`, 30 seconds by default. Only
the mirror contacts external repositories, and every other reconcile reads
the copy, which is cheap. A branch that changed only in the external
repository moves to the same commit in the copy. Deleting a branch on one
side deletes it on the other, unless the other side added commits to the
branch since they last synced. Then the branch diverges, and neither side
changes. See [Divergence](#divergence).

The `ExternalSynced` condition on each `GitRepository` says whether the
external repository has every change in the copy:

| Status | Reason | Meaning |
| --- | --- | --- |
| `True` | `InSync` | The external repository has every change in the copy. |
| `False` | `Pending` | The external repository doesn't have the changes to the branches that the message lists yet. |
| `False` | `Diverged` | The branches that the message lists changed on both sides. See [Divergence](#divergence). |
| `False` | `CompareFailed` | The mirror couldn't compare the heads of the branches that the message lists, for the reasons in the message, such as a comparison that took too long. It leaves those branches as they are on each side, and they don't land. See [Divergence](#divergence). |
| `False` | `SyncFailed` | Fetching from or pushing to the external repository failed, for the reason in the message. |

After a fetch or a push fails, the controller tries again within 30
seconds, or within `pollInterval` if that's shorter, and doesn't push until
then. Until a copy has fetched from its external repository once, the
mirror answers requests for it with `503 Service Unavailable`, and the
`GitRepository`'s `Ready` condition says why, with the reason `FetchFailed`
or `CredentialsUnavailable`.

When you delete a `GitRepository`, the controller pushes the copy's last
changes to the external repository and then deletes the copy. While the
external repository lacks a change, because the sync fails or a branch
diverged, the `GitRepository` stays, and its `Synced` condition says why. It
also stays while the mirror can't compare a branch's heads. To delete it
anyway, with the changes that the external repository lacks, remove the
finalizer `kube.imjasonh.github.io/repositories`.

The mirror syncs branches only. It doesn't fetch or push tags, and it takes
pushes only to branches.

### Who can fetch and push

Each request to the mirror carries a projected service account token with
the audience `git-k8s-mirror` as a bearer token, which git sends with
`http.extraHeader`. The mirror checks the token with `kube.ReviewToken`,
which sends a TokenReview to the API server. A request without a valid token
gets `401 Unauthorized`. A request for a repository that the caller can't
fetch gets `404 Not Found`, so that the caller doesn't learn which
repositories exist.

The service account that the token belongs to decides what the caller can
do:

| Caller | Can fetch | Can push |
| --- | --- | --- |
| The check `NAME`, which runs as the service account `check-NAME` in the namespace `check-NAME` | Each repository whose merge policies list the check | Each branch that has a parent whose merge policy gives the check `mayPush: true` |
| A controller that starts branches, which the core program's `-branch-prefix` flag names | Every repository | The branches under its prefix, except parents |
| A test Pod of `check-gotest`, with a token that's bound to the Pod | The repository of the branch that the Pod tests, while the `gotest` check's result names the Pod and the Pod is `Pending` | Nothing |

The merge controller is part of the core program and updates the copy
directly, so it's the only thing that moves a parent.

The mirror reads the ref updates at the start of each push before git
applies them, and refuses the whole push if it refuses any update in it.
git shows the reason to the person or program that pushed:

```
 ! [remote rejected] HEAD -> main (main is a parent branch, which only the merge controller updates)
```

A check can't create or delete branches. git updates a branch only if it
still points to the commit that the push expects, so a push never
overwrites a change that the pusher hasn't seen. Pushes can't see or change
the mirror's own refs under `refs/git-k8s/`, and git checks every object in
a push with `receive.fsckObjects`. To resolve a divergence, fetches can see
the external repository's heads under `refs/git-k8s/downstream/heads/`, and
the heads where the copy and the external repository last synced under
`refs/git-k8s/synced/heads/`.

The mirror reads at most 1,000 ref updates and shallow commits, in at most
1 MiB, at the start of a push, and a copy takes a pack of at most 256 MiB.
The mirror stops reading a request that takes longer than git's 5-minute
timeout plus 10 seconds, and stops writing a response 10 minutes 20 seconds
after the request starts. A client that sends a pack slowly keeps the copy
open until the first deadline, and a client that stops reading the response
keeps it open until the second. While a copy is open, the mirror can't
delete it, replace it, or switch it to a new URL, and the requests that
come after such a change wait for it too.

To let a controller start branches, pass the core program
`-branch-prefix=NAMESPACE/SERVICEACCOUNT=PREFIX` for the controller's
service account, and repeat the flag for more controllers. For example, for
a dependency update controller that `generate` installs in the namespace
`git-k8s-deps`:

```sh
go run ./cmd/git-k8s generate -registry=REGISTRY -base=cgr.dev/chainguard/git:latest -- -branch-prefix=git-k8s-deps/git-k8s-deps=deps/
```

The controller reaches the mirror with `mirror.Remote`, as a check does, and
a branches rule such as `match: deps/**` with `parent: main` tracks its
branches.

The mirror knows a controller only by the namespace and name of its service
account. Anyone who can create Pods or tokens in that namespace can act as
the controller, which can fetch every repository, so only cluster
administrators should control the namespace.

A test Pod's token is bound to the Pod, so it stops working when the Pod is
deleted, and it expires after 10 minutes. The mirror lets the Pod fetch only
while a `Running` result of the `gotest` check on one of the repository's
branches names the Pod in its `pod` output, so `check-gotest` records the
Pod's name before it starts the Pod. Because the name is known before the
Pod exists, another program that creates Pods in the namespace could create
a Pod with that name first. So the mirror also checks the Pod itself: it
reads the name and UID of the token's Pod from the TokenReview, gets that
Pod, and refuses the request unless the Pod has that UID, has kube's label
`kube.imjasonh.github.io/controller=check-gotest`, which kube puts on the
Pods that `check-gotest` declares, isn't being deleted, and is `Pending`. A
Pod is `Pending` while its init containers run, and only the init container
that fetches the branch has the token, so the token stops working when the
tests start. That's why `generate` lets the core program get Pods. The
third admission policy in `config/policy.yaml` keeps other checks from
setting the label, as [Install](#install) describes. Any other program that
can create Pods in the namespace can set it, so the label means
`check-gotest` only as long as those programs don't set it.

### Divergence

A branch diverges when the copy and the external repository both changed it
since they last synced, and neither side's head keeps the other side's
changes. For example, a check pushes a fix to the mirror while a person
pushes to GitHub, or a person force-pushes to GitHub to remove a commit
while a check pushes a fix on top of that commit to the mirror. The mirror
overwrites neither side. It keeps the external repository's head at
`refs/git-k8s/downstream/heads/BRANCH` in the copy, and the head where the
two sides last synced at `refs/git-k8s/synced/heads/BRANCH`. The merge
controller records both in the `GitBranch`'s status:

```yaml
status:
  state: Diverged
  diverged:
    commit: 3f1d0c2b9a8e7d6c5b4a39281706f5e4d3c2b1a0
    ref: refs/git-k8s/downstream/heads/c/auth
    base: 8c2e4a6f0b1d3c5e7a9f2b4d6c8e0a1f3b5d7c9e
```

If the external repository deleted the branch, `commit` and `ref` are empty.
If the copy deleted it, the branch has no `GitBranch`, and only the
`ExternalSynced` condition lists it.

The mirror compares each side's head with the head where they last synced,
`base`. A side added the commits that its head has and `base` doesn't, and
removed the commits that `base` has and its head doesn't. A side that
removed commits rewound, for example with a force push, and deleting a
branch removes every commit. The mirror moves one side to the other side's
head only if that head keeps every change that the moving side made. A head
keeps a side's changes when it has none of the commits the side removed and
no replay of one, a replay of each commit it added, and every change it made
since `base`:

- The head has none of the commits that the moving side removed, and no
  replay of one unless the moving side made the same change again, as a
  rebase does.
- The head has each commit that the moving side added. If the head doesn't
  contain `base`, a replay of the commit also counts. A replay is a commit
  other than a merge that removes and adds the same lines in the same files
  as the original, as `git patch-id --stable` compares them, which ignores
  whitespace and where in each file the lines are. The comparison ignores
  `.gitattributes` files, so that an attribute such as `-diff` can't hide a
  replay. Each commit in the head replays at most one commit, and a commit
  that changes no file has no replay.
- If the moving side removed commits, or the head doesn't contain the
  moving side's head, merging the moving side's head into the head, with
  `base` as the merge base, is clean and changes nothing. The merge ignores
  `.gitattributes` files, so that an attribute such as `merge=union` can't
  make it clean.

So a branch diverges if one side rewound and the other side added commits,
even if the other side's head contains the rewound side's head, because
moving the rewound side to it brings back the commits that it removed. If
neither side rewound, only a head that contains both heads keeps both
sides' changes.

A head built on a side that rewound to a new commit keeps that side's
changes even where it resolved conflicts. The side's head is then a commit
that `base` doesn't have, and each commit that the head has and the side's
head doesn't has the side's head or another such commit as a parent. In
that case, merging either the side's head or the commit where the side's
head and `base` meet, their only merge base, into the head, with `base` as
the merge base, must be clean and change nothing, so that the head brings
back no change that the side removed. A merge of the side's head with
another commit is built on the side's head only if that commit is too. So a
merge with a commit that overrides the side's change, such as one that
`git merge -X theirs` makes, doesn't keep the side's changes, and the
branch diverges.

Because a replay can match the same change on another line, the merge is
what stops a commit from counting as the replay of a different change, and
stops a rebased or reworded copy of a removed commit from bringing the
removed change back. git merges conservatively, so changes to the same line
or to adjacent lines conflict, and a head that keeps every change can still
diverge.

The merges can't see a replay of a removed commit whose change other
removed commits undid, such as a secret and its revert that a force push
dropped, so the rule also looks for replays of the removed commits. It
can't find one inside a larger commit, such as a squash. No merge checks
these replays, so a commit that makes a removed commit's change on another
line also counts as one, and the branch diverges.

Comparing the heads can take a long time when both sides rewrote the same
long stretch of history between two syncs. The mirror stops comparing a
branch's heads after 10 minutes 20 seconds, twice the longest that one git
command can take, or when one git command runs past git's 5-minute
timeout, and leaves the branch as it is on each side, with the reason
`CompareFailed`. It remembers what it decided about each branch, including
a comparison that took too long, and doesn't compare that branch's heads
again until either side's head moves or the core program restarts. To
resolve a branch whose comparison took too long, push the same commit to
the branch in the mirror and in the external repository. When comparing
the heads fails for another reason, such as a full disk, the next sync
compares them again.

A diverged branch doesn't land, because landing the copy's head leaves out
the external repository's changes. To resolve a divergence, push a head
that keeps both sides' changes to the branch on either side, with a lease on
that side's head. The mirror then moves the other side to it, and the merge
controller clears `status.diverged`:

- If neither side rewound, push a commit that contains both heads, such as
  a merge of the downstream ref.
- If one side rewound, a commit that contains both heads can't express the
  removal. Replay the commits that the other side added since `base` onto
  the rewound side's head, and push the result with a lease. If you push it
  to the side that didn't rewind, it resolves the divergence even if you
  changed commits to resolve conflicts, as long as none of its commits
  replays a commit that the rewound side removed, you didn't change lines
  that the removed commits changed, and either you didn't change lines
  that the rewound side changed, or the rewound side didn't change lines
  that the removed commits changed. A line next to a changed line counts
  as changed. If you push it to the side that rewound, each commit that
  the other side added needs a replay in it. If the branch still diverges,
  push the result to both sides.

To keep one side's head instead, and drop the other side's changes, push
that head to the other side.

For example, if a person force-pushed `c/auth` in the external repository
while a check pushed to it in the mirror, replay the check's commits onto
the external repository's head, and push the result to the mirror:

```sh
git fetch MIRROR refs/heads/c/auth refs/git-k8s/downstream/heads/c/auth refs/git-k8s/synced/heads/c/auth
git switch --detach COPY_HEAD
git rebase --onto COMMIT BASE
git push --force-with-lease=refs/heads/c/auth:COPY_HEAD MIRROR HEAD:refs/heads/c/auth
```

Replace the following:

- `MIRROR`: the copy's URL, such as `http://git-k8s.git-k8s.svc/team/app.git`
- `COPY_HEAD`: the copy's head, which is the `GitBranch`'s `spec.head`
- `COMMIT`: `status.diverged.commit`
- `BASE`: `status.diverged.base`

If the copy rewound instead, replay the external repository's commits onto
the copy's head with `git rebase --onto COPY_HEAD BASE COMMIT`, and push the
result to the external repository with a lease on `COMMIT`. To resolve a
branch that the copy deleted, delete it in the external repository too,
after you push the commits that you want to keep to a new branch there.

People have no identity of their own on the mirror. To fetch or push by
hand, use a token for a service account that can, such as the service
account of the check that pushed the change, and pass it to git with
`-c http.extraHeader="Authorization: Bearer TOKEN"`. This command makes one
for anyone whom Kubernetes RBAC lets create tokens for that service account:

```sh
kubectl -n NAMESPACE create token SERVICEACCOUNT --audience=git-k8s-mirror
```

A parent takes no pushes, so branches still land on a diverged parent, and
a commit that contains both heads resolves it when it lands from a child
branch like any other change. A new child branch that resolves a diverged
parent can also go to the external repository, and the mirror takes it at
its next poll. The merge controller only moves a parent to a commit that
contains the parent's head, so a parent that rewound in the external
repository resolves only there, with a replay of each commit that landed in
the copy since `base`. If a commit can't be replayed unchanged, for example
because it changes lines that the rewind removed or lines next to them, the
parent stays diverged until the external repository's head contains the
copy's head again.
[Resolve conflicts in a controller](future-work.md#resolve-conflicts-in-a-controller)
proposes a controller that resolves divergence by itself.

### Credentials

Only the core program reads Secrets or gets tokens from Octo STS. Each time
the repositories controller fetches from or pushes to an external
repository, it reads the Secret that `secretRef` names, and sends its
`username` and `password` keys with HTTP basic auth, or `git` as the
username if the Secret has none. For a repository on GitHub, it can use a
token from Octo STS instead, as [GitHub repositories](#github-repositories)
describes. Checks and test Pods reach only the mirror, with their own
tokens, so `generate` doesn't let them read Secrets or request tokens. The
[`credentials`](credentials/credentials.go) package holds the only code that
reads Secrets or gets tokens for external repositories, and is where other
ways to authenticate belong.

The mirror reaches external repositories only over the network. A `url`
that's a local path or a `file` URL fails, so a `GitRepository` can't read
another namespace's copy from the core program's volume.

## Events

The controllers record an event about a `GitBranch` each time they push a
fix to the branch, fast-forward its parent to it, or delete it, in the
mirror's copy. The repositories controller then pushes the change to the
external repository, as
[Sync with the external repository](#sync-with-the-external-repository)
describes. Squash and rebase landings record no event, and only the
`Merged` condition reports them:

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
deletes events after an hour by default. To audit what landed, use the git
history of the copy or of the external repository. `generate` grants
`create` and `patch` on events to the `git-k8s` program and to every check
program. A check that never pushes a fix, such as `check-approval`, gets the
grant too, because the `checks` package that every check uses records
`PushedFix`.

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

`gitIdentity` replaces `secretRef`, so set only one of the two. Only the
mirror uses tokens for it, to fetch from and push to the repository. The
checks and `check-gotest`'s test Pods fetch from the mirror, so `gotest`
works for a private repository too. The core program publishes
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
   subject: system:serviceaccount:git-k8s:git-k8s
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
When you install the core program with `generate`, as [Install](#install)
describes, it runs as the service account `git-k8s` in the namespace
`git-k8s`. It's the only program that asks Octo STS for tokens, so both
trust policies name only its service account. If you install it under
another name or in another namespace, change `subject` to match.

Each token's audience is `octo-sts.dev/` followed by the `GitRepository`'s
namespace. The core program uses the same service account for every
`GitRepository`, so the audience is the part of a token that names the
namespace it's for. A trust policy that requires your namespace's audience
refuses the tokens that git-k8s requests for a `GitRepository` in another
namespace, even one that names your repository and identities. Without an
`audience`, a trust policy accepts only `octo-sts.dev`, which git-k8s never
requests.

`contents: write` lets the mirror fetch and push. To land changes to files
in `.github/workflows`, also grant `workflows: write`, because GitHub refuses
a push that changes those files without it. `checks: write` lets the core
program create and update check runs.

The core program keeps each GitHub token in memory and gets a new one 10
minutes before it expires. If an exchange fails, it uses the old token until
a minute before it expires, and asks Octo STS again after 30 seconds. When
the mirror can't get a token before its first fetch of a repository, the
`GitRepository`'s `Ready` condition is `False` with the reason
`CredentialsUnavailable`. After that, its `ExternalSynced` condition is
`False` with the reason `SyncFailed`, and checks keep working on the copy.
Both messages include Octo STS's answer, such as
`unable to find trust policy for "git-k8s"`. Octo STS caches each trust
policy, and the lack of one, for 5 minutes, so a change to a trust policy can
take that long to apply.

### Check runs

When a `GitRepository` names a `checkRunsIdentity`, the core program's
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

The controller keeps what it wrote only in memory. If the core program
restarts after a branch leaves a commit and before the controller reconciles
the change, the check run on that commit stays in
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

The controller relies on the core program's one replica, which reconciles
all of a repository's branches and keeps the only record of the check runs
that they share. `generate` installs the core program with one replica
because of the mirror's volume, as [Install](#install) describes.

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

The core program keeps GitHub tokens in memory and passes them to git in its
environment, so the tokens don't appear in process arguments, Kubernetes
objects, or logs. The service account tokens that it sends to Octo STS are
bound to its Pod and last an hour. `generate` lets the core program request
tokens for its own service account, and for no other. The checks' only
tokens are for the mirror, and `generate` mounts those, so the checks can't
request tokens at all.

The core program sends service account tokens only to Octo STS, and GitHub
tokens only to GitHub. For tests, its `-fake-github` flag points it at a fake
GitHub and Octo STS instead. It's a flag and not a `GitRepository` field, so
only whoever installs the core program can choose where its tokens go. The
end-to-end test's git server runs such a fake, which checks each service
account token with a TokenReview, because Octo STS can't reach a kind
cluster's issuer.

A trust policy's audience ties it to one namespace, so anyone who can create
a `GitRepository` in that namespace can use the trust policy's permissions.
Grant that only to people who may push to the repository. The audience holds
only the namespace's name, so a namespace that's deleted and created again
with the same name gets the trust policies that named the old one.

The rule that lets the core program request tokens, `create` on
`serviceaccounts/token` for its own service account, also lets anyone who
holds one of its service account tokens create more. Someone who can run
`kubectl exec` in the core program's Pod, create Pods in its namespace, or
read files on its node can get such a token. The tokens that they create
can have any audience, needn't be bound to the Pod, and can last as long as
the API server allows. A token with the audience
`octo-sts.dev/` followed by a namespace gets the permissions of each trust
policy that requires that audience and names the core program, such as
`contents: write`. Whoever holds the core program's token can therefore push
to the repositories of every namespace whose trust policies name it. The
audiences keep namespaces apart from each other, but not from someone who
can read the core program's token. Limit who can use `pods/exec` or create
Pods in the namespace `git-k8s`, and if you manage the API server, set
`--service-account-max-token-expiration`.

GitHub grants `contents: write` for a whole repository, not for branches, so
the mirror's tokens can push to any branch. Checks never hold them. A check
pushes to the mirror, which applies the rules in
[Who can fetch and push](#who-can-fetch-and-push).

## Checks

| Program | Check | What it does |
| --- | --- | --- |
| `check-base` | `base` | Passes when the branch contains its parent's head, or the parent already contains the branch. Otherwise it merges the parent in with `git merge-tree`, and fails with the conflicting paths if the merge conflicts. |
| `check-gofmt` | `gofmt` | Formats every `.go` file outside `vendor` and `testdata` directories with `go/format`, and passes when nothing changes. |
| `check-risk` | `risk` | Always passes, and sets `outputs.level` to `high` when the change is larger than `-max-lines` or touches a path that matches a `-sensitive` glob, and to `low` otherwise. |
| `check-approval` | `approval` | Passes when the `git-k8s.imjasonh.com/approve` annotation on the `GitBranch` names the branch's head, and sets `outputs.approver` to the `git-k8s.imjasonh.com/approved-by` annotation. A push after the approval needs a new one. See [Approve a branch](#approve-a-branch). |
| `check-gotest` | `gotest` | Runs `go test ./...` in a Pod that it declares with `kube.Own`, and fails with the end of the test output. See [Sandboxed checks](#sandboxed-checks). |

A check with `mayPush: true` pushes its fix commit to the branch in the
mirror, which moves the head and runs the checks again. Fix commits have a
`Git-K8s-Fixer: CHECK` trailer, and `maxAutomatedCommits` (default 5) limits
how many a branch can have, so two checks that undo each other's fixes stop.
The same inputs always produce the same fix commit, so two retries of one
fix push the same commit.

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
	checks.Main[Branch](checks.Check{Name: "readme", Remote: mirror.Remote, Run: run})
}
```

`in.Repo` fetches the branch and its parent from the mirror into the
program's local repository. A verdict with a `Fix` commit asks the framework
to push it. Both need `Remote: mirror.Remote`, from the `git-k8s/mirror`
package, which reaches the repository's copy on the mirror with a token for
the mirror. `generate` mounts that token in the Pods of each program that
imports the package, so a check that reads only the `GitBranch`, such as
`check-approval`, leaves `Remote` out, and its program gets no token. No
check reads Secrets.

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

- An init container fetches the head from the mirror. It's the only
  container with a token for the mirror, and the token is bound to the Pod.
  The token reaches git through the init container's environment, not the
  repository's configuration, which the test container can read.
- The test container runs `go test ./...` as user 65532 with no service
  account token, no privileges, a read-only root file system, and
  `GOPROXY=off`, so tests can't download modules.
- A NetworkPolicy that the core program owns lets the Pod reach only the
  mirror and the cluster's DNS servers, and lets nothing reach it. When the
  core program's `-goproxy` isn't `off`, the policy also lets the Pod reach
  ports 80 and 443 on IPv4 addresses outside the private ranges
  (`10.0.0.0/8`, `172.16.0.0/12`, and `192.168.0.0/16`), the shared address
  space (`100.64.0.0/10`), and the link-local range (`169.254.0.0/16`).
  Those ranges usually hold the cluster's Pods, Services, and nodes, and a
  cloud's metadata server. If your cluster gives Pods, Services, or nodes
  addresses outside those ranges, the policy lets test Pods reach those
  addresses on ports 80 and 443 too, so leave `-goproxy` `off` there.
- If fetching fails, the check starts a new Pod 30 seconds later, and 60
  seconds after a second failure, so its three Pods outlast a restart of the
  core program.
- At most `-max-pods` test Pods, 10 by default, run at once across all
  namespaces. A branch that would start another reports `Running` and waits
  until one finishes.

kube deletes a Pod when the check stops declaring it: after the check
records the Pod's result, or when the branch moves to a new head. Owner
references delete the Pods with their `GitBranch`. Set `-runtime-class` to
run the Pods under a sandboxing runtime such as gVisor, and `-go-image`,
`-git-image`, `-timeout`, and `-goproxy` to change the rest. If you set
`-goproxy`, set the same value on the core program.

The core program owns the NetworkPolicy so that `check-gotest`, which
creates Pods in every namespace that has a `GitBranch`, can't change
NetworkPolicies. Each `GitRepository` owns one policy, `NAME-test-pods`. It
selects the Pods in the repository's namespace that have kube's controller
label for `check-gotest`, `kube.imjasonh.github.io/controller=check-gotest`,
which are the Pods that the mirror lets fetch. The policies of the
`GitRepository` objects in a namespace are the same, so each one covers every
test Pod there. The repositories controller declares the policy before the
`GitBranch` objects, so it exists before `check-gotest` starts the first test
Pod for a new `GitRepository`. If someone deletes the policy, the next
reconcile of the `GitRepository` that succeeds creates it again. When you
delete the last `GitRepository` in a namespace, garbage collection deletes
the policy with the `GitBranch` objects, before the test Pods that they own,
so a test Pod that's still running loses the policy's limits until it stops.

The policy selects the cluster's DNS servers as the Pods labeled
`k8s-app=kube-dns` in the namespace `kube-system`, which is where kubeadm
and kind run CoreDNS. If your cluster's DNS Pods have other labels or run in
another namespace, set the core program's `-dns-labels` and
`-dns-namespace`. If Pods send DNS queries to an address that isn't a Pod's,
such as NodeLocal DNSCache's `169.254.20.10`, set its `-dns-cidrs`, for
example to `169.254.20.10/32`.

The NetworkPolicy needs a network plugin that enforces NetworkPolicies, such
as Calico or Cilium. Kubernetes allows a connection that any policy for the
Pod allows, so another policy that selects test Pods can let them reach
more, such as a module proxy inside the cluster. Some plugins, such as
kind's kindnet, don't filter a Pod's connections to its own node, which can
include the API server. Test Pods have no service account token, so the API
server gives them only what it gives anonymous requests.

Both of a test Pod's containers meet the `restricted`
[Pod Security Standard](https://kubernetes.io/docs/concepts/security/pod-security-standards/).
An admission policy keeps `check-gotest` to its own Pods, in namespaces that
opt in to test Pods and enforce the `restricted` standard. See
[Install](#install).

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
`Git-K8s-Fixer` trailer, so the commit doesn't count as a fix. A rebase keeps
each commit's author and message, and leaves out a commit that changes
nothing, such as a change that the parent already has.

The merge controller commits as
`git-k8s <git-k8s@users.noreply.github.com>`, which its `-identity-name` and
`-identity-email` flags change. It takes commit times from the commits that
it copies, so making the same landing again makes the same commits.

When the branch is one commit on top of the parent's head, a squash
fast-forwards the parent to it. A rebase does the same for a branch with no
merge commits after the parent's head, because copying its commits changes
nothing. When the parent already has the files at the branch's head, a squash
sets the branch's state to `Merged` and changes nothing. A rebase does that
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

The built-in checks set `FilesOnly`. `check-base` passes for any commit that
builds on the parent's head, `check-gofmt` and `check-gotest` read only the
files, and `check-risk` compares them with the parent's head.
`check-approval` reads only the `GitBranch`, and an approval is for the
change, which the new commit makes too. `maxAutomatedCommits` counts fix
commits by their trailer, but it limits what checks push, and the gate
doesn't read it.

When the counted results pass the gate, the controller lands the new commit
without another round of checks. It moves the parent to the commit in the
mirror's copy, if the parent is still at the head that the checks saw. The
same atomic update deletes the branch, if the branch is still at its head,
or moves the branch to the new commit when `deleteMergedBranches` is off. A
branch that stays is then at its parent's head, so it shows `Merged` instead
of commits that the parent doesn't have. If the parent or the branch moved
since the repositories controller listed them, the update changes neither,
and the controller tries again.

When the gate doesn't pass on the counted results alone, the controller
moves the branch to the new commit in the mirror's copy instead, if the
branch is still at its head, and sets the branch's state to `Rewritten`.
The checks run on the new commit, and when the gate passes, the parent
fast-forwards to it. `check-approval` passes only for the head that the
annotation names, so a rewritten branch needs a new approval.

A check with `mayPush: true` can push a fix on top of the new commit. While
the parent doesn't move, a squash landing doesn't squash its own commit and
the fixes after it again, so they land by fast-forward, with each fix as its
own commit. Another squash would keep the fixes' files but drop their
commits, so a check that reads commits could push the same fix forever.
`maxAutomatedCommits` counts only the fixes after the squashed commit,
because it doesn't have the trailers of the fixes before it.

Moving a branch that stays, and rewriting a branch, replace the branch's
commits in the mirror's copy, and then in the external repository. Before
you push to a branch that the controller moved, reset your copy to the
branch's new head.

An external repository can refuse to replace a branch's commits or to
delete the branch. Git's `receive.denyNonFastForwards` and
`receive.denyDeletes` settings do that, and so do GitHub rules that block
force pushes or deletions. The merge controller changes only the mirror's
copy, so a refusal doesn't stop a landing or a rewrite, and the checks run
on a rewritten branch's new commit in the copy. The mirror pushes each
branch on its own, so the parent still reaches the external repository, and
the external repository keeps the branch where it was. The
`GitRepository`'s `ExternalSynced` condition is then `False` with the reason
`SyncFailed` and a message such as
`the external repository refused updates to c/auth ([remote rejected] (deletion prohibited))`,
and the mirror tries again at each poll. A rewritten branch that the
external repository refused still lands. If the merge policy deletes merged
branches, the mirror then deletes the branch in the external repository,
unless the external repository refuses that too. To clear the condition,
let the external repository accept the update, such as by allowing force
pushes to and deletions of proposal branches.

## Install

Each program installs with kube's `generate` command, which builds an image,
pushes it, and writes the YAML for its namespace, service account, RBAC
rules, and Deployment. The programs run `git`, so build them on an image
that has git 2.43 or later:

```sh
for program in git-k8s check-base check-gofmt check-risk check-approval check-gotest; do
  go run "./cmd/${program}" generate -registry=REGISTRY -base=cgr.dev/chainguard/git:latest | kubectl apply -f -
done
kubectl apply -f config/policy.yaml
```

Replace `REGISTRY` with a registry and repository prefix that your cluster
can pull from, such as `ghcr.io/you`. To pass flags to a program, add them
after `--`, as in `go run ./cmd/check-risk generate -registry=REGISTRY -- -sensitive='auth/**'`.

The core program keeps the mirror's copies on a PersistentVolumeClaim that
`generate` adds for its `kube.Volume`, at
`/var/lib/git-k8s/NAMESPACE/NAME.git`. The claim asks for 1 GiB of the
cluster's default StorageClass unless you pass `-volume-size` or
`-storage-class` to `generate`. A volume has one writer, so the core program
runs one replica without leader election, and a rollout stops the old Pod
before it starts the new one. While the Pod restarts, the mirror and the
controllers are down, and checks retry. For more about volumes, see
[Keep state on disk](../kube/README.md#keep-state-on-disk) in kube's README.

Two Pods can still overlap on one node, for example after
`kubectl delete pod`, for up to the old Pod's 30-second termination grace
period. Every ref update in a copy takes git's lock on the ref and checks
the ref's old value, so an update that loses a race to the other Pod fails,
and a later reconcile tries again. Both Pods reconcile while they overlap,
so a late status write from the old Pod can replace a newer one, as kube's
lost-Lease limitation describes. If you lose the volume, you
lose only the changes that the external repositories don't have yet, and
the core program fetches each repository again. Deleting the installation,
for example with `kubectl delete -f`, deletes the claim.

A git that's killed while it holds a lock, for example when the Pod runs
out of memory, leaves the lock file, and git can't update what the file
locks until it's gone. A git command that runs past its 5-minute timeout,
or whose request ends, gets `SIGTERM` and removes its own locks. Before
each sync, the mirror removes the copy's lock files that are older than 6
minutes and 10 seconds: the longest that a git command can take, plus a
minute in case the volume's clock differs from the node's. A newer lock
might belong to the other Pod. Until the mirror removes a lock, a sync or a
landing that needs the locked ref fails and tries again later. When a sync
fails, the `GitRepository`'s `Ready` condition (reason `MirrorFailed`) or
`ExternalSynced` condition (reason `SyncFailed`) names the lock.

Git packs a copy's objects in its maintenance. A fetch or a push would
start maintenance in the background, where git's timeout doesn't apply, so
the mirror turns that off and runs maintenance itself at the end of each
sync, when git says the copy needs it, and logs any failure. The sync
waits for it. Maintenance that runs past the timeout gets `SIGTERM`, and so
does the repack that it started, and the next sync starts over, so a copy
whose repack takes longer than the timeout isn't repacked. Maintenance that
gets `SIGKILL` instead, as when the Pod's grace period runs out, leaves
`objects/maintenance.lock`, which makes later maintenance skip the copy
without an error, so the mirror removes that lock once it's stale, like the
others.

The checks keep local copies of repositories in `/tmp/git-k8s`, on the
`emptyDir` volume that `generate` mounts at `/tmp`.

To upgrade an installation from before the mirror, apply it with
`kubectl apply`, as the loop does, because server-side apply can't switch
the core program's Deployment to the `Recreate` strategy. Then delete the
Role, RoleBinding, and PodDisruptionBudget that the core program needed for
two replicas:

```sh
kubectl -n git-k8s delete --ignore-not-found role,rolebinding,poddisruptionbudget git-k8s
```

If you set `check-gotest`'s `-goproxy`, set the same value on the core
program. Otherwise, on a cluster that enforces NetworkPolicies, the test
Pods' NetworkPolicy keeps them from reaching the proxy. A proxy inside the
cluster also needs a NetworkPolicy of your own, as
[Sandboxed checks](#sandboxed-checks) describes.

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
trusts. The mirror checks both for test Pods, as
[Who can fetch and push](#who-can-fetch-and-push) describes.

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

## Security model

git-k8s divides what each program can do, so that no single check can land
a change:

- A check can push only to branches that have a parent whose merge policy
  gives the check `mayPush: true`. Each push is a new head that every check
  runs on again, so a compromised check can't move a parent or skip a merge
  gate. It can't read Secrets or reach external repositories, and the
  admission policies keep it to its own result.
- The test container, which runs the branch's code, has no token and no
  credentials, and the core program's NetworkPolicy lets it reach only the
  mirror and the cluster's DNS servers. `check-gotest` creates the Pod but
  can't change NetworkPolicies. The init container's token can fetch only
  the branch's repository, only before the test container starts, and stops
  working when the Pod is deleted.
- Tokens for the mirror have their own audience, `git-k8s-mirror`, so the
  API server doesn't accept them, and the mirror doesn't accept tokens for
  the API server. The kubelet renews each check's token, which lasts an
  hour.
- The mirror runs git with `--end-of-options` before every argument that
  comes from a `GitRepository` or a push, and doesn't sync or list branches
  whose names start with `-`, so neither can pass git an option.

The core program is the only program that reads Secrets or changes
NetworkPolicies, which it does in every namespace, and the only one that
gets tokens from Octo STS. It holds the external repositories' credentials
and decides what lands.

Kubernetes RBAC is the trust boundary. Anyone who can write a
`GitRepository` in a namespace chooses the external repository, and the
Secret or Octo STS identities that the core program uses there. Of the
service accounts, only `check-gotest`'s can write the `gotest` result, but
people who can write `GitBranch` status in a namespace can write it too.
Such a result can name a Pod in that namespace for the mirror to let fetch
the repository, but the mirror accepts only a `Pending` Pod with
`check-gotest`'s controller label. Making such a Pod takes the right to
create Pods in that namespace, which already lets a Pod mount the
repository's Secret. Anyone who can create tokens for a check's service
account can push as that check, and anyone who can create tokens for a
controller's service account can do what its `-branch-prefix` allows.

The mirror serves plain HTTP inside the cluster, so anything that can read
Pod traffic can read tokens and repositories, and a token that leaks works
until it expires.

## Test

The unit tests call each reconciler with `kube.Fake` and a real git server
that runs in the test process, and serve the mirror's handler with
`httptest` and `kube.FakeRequest`:

```sh
go test -race ./...
```

The end-to-end test installs every program with `generate` in a
[kind](https://kind.sigs.k8s.io/) cluster with a local registry. It runs a
git server on this machine as the external repository, which Pods reach
through the kind network's gateway. It pushes branches to that git server,
and to the mirror through `kubectl port-forward` with tokens from
`kubectl create token`. It checks what test Pods can reach only if the
cluster enforces NetworkPolicies, which kindnet does only on kernels with
`nfnetlink_queue`. It needs Docker, `kubectl`, and `git`, and installs kind
if it's missing:

```sh
GIT_K8S_KIND_E2E=1 go test -v -count=1 ./e2e/kind/
```

CI runs it when `git-k8s/` or `kube/` changes. To keep the cluster
afterward, set `GIT_K8S_KIND_KEEP=1`. If your network can't reach `cgr.dev`,
set `GIT_K8S_KIND_CHAINGUARD=docker.io/chainguard`.

## Limitations

- The mirror polls external repositories; it doesn't receive webhooks. A
  push to an external repository takes up to `pollInterval` to reach
  git-k8s. Pushes to the mirror and landings reach the external repository
  at once.
- External repositories authenticate with HTTP basic auth only.
- The core program runs one replica, so the mirror and the controllers are
  down while it restarts.
- The mirror syncs branches, not tags.
- Nothing resolves a divergence or a merge conflict by itself.
- The test Pods' NetworkPolicy works only with a network plugin that
  enforces it.
- Squash and rebase landings make unsigned commits, even from signed ones.
  With a check that requires signed commits, use `FastForward`.

[`future-work.md`](future-work.md) proposes fixes for these, and lists the
other known gaps.
