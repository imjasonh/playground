# git-k8s

git-k8s runs a branch workflow on Kubernetes. It tracks a git repository's
branches as `TrackedBranch` objects, and keeps a copy of the repository on a git
server in the cluster, the mirror. It runs checks on branches that propose
changes to another branch, and checks can push commits that fix what they
find. When the parent's merge policy passes, git-k8s lands the branch on the
parent by fast-forward, squash, or rebase. The mirror pushes every change to
the external repository, such as one on GitHub, and takes the changes that
people push there.

It's a rewrite of [imjasonh/git-k8s](https://github.com/imjasonh/git-k8s)
on [`kube`](../kube/), the controller framework in this repository. The
module imports `kube` at head with `replace github.com/imjasonh/playground/kube => ../kube`.

The kinds are `TrackedRepository` and `TrackedBranch`, with the short names
`gkrepo` and `gkbranch`, because Flux's source-controller already defines a
`GitRepository` kind with the plural `gitrepositories` and the short name
`gitrepo`. On a cluster that runs both, kubectl resolves each of those names
to only one of the two kinds.

## How it works

You write a `TrackedRepository`:

```yaml
apiVersion: git-k8s.imjasonh.com/v1alpha1
kind: TrackedRepository
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
        deleteLandedBranches: true
    - match: c/**
      parent: main
```

For each branch, the first rule whose `match` glob matches applies, and
branches that match no rule aren't tracked. A branch whose rule names a
`parent` is a proposal to that parent. The parent's rule says what a proposal
needs before it lands.

`url` must be an `https://` or `http://` URL without a query or a fragment,
such as `https://git.example.com/app.git`. git-k8s authenticates to external
repositories only over HTTP, so it doesn't take `ssh://` URLs or scp-like
addresses, such as `git@example.com:app.git`, which git reaches over ssh. The
API server rejects other URLs, and git-k8s runs git with `GIT_ALLOW_PROTOCOL`
set to `http:https`. Its git commands put `--end-of-options` before every
URL, branch, and commit, so git can't read one as an option. git-k8s doesn't
track branches whose names start with `-` or aren't valid ref names.

Put credentials in `secretRef`, not in `url`. `kubectl get trackedrepositories`
shows each URL, and `git-k8s-deps` copies it into the specs of its update
Pods.

The `git-k8s` program, which this README calls the core program, serves the
mirror and an endpoint that accepts check results, and runs four
controllers. Each check runs as its own program. The mirror and the results
endpoint share one `kube.Serve` handler, and each controller is a
`kube.For` reconciler:

- The **mirror** keeps a copy of each repository on a persistent volume and
  serves it over git's smart HTTP protocol. The copy is the repository's
  source of truth, and checks fetch from it and push to it. The external
  repository is a downstream copy. See [The mirror](#the-mirror).
- The **repositories** controller syncs each copy with its external
  repository, and declares a `TrackedBranch` for each tracked branch in the copy
  with `kube.Own`. The spec holds the branch's head, its parent's head, and
  the parent's merge policy. When a branch disappears, kube deletes its
  `TrackedBranch`, because the reconcile stops declaring it.
- Each **check** controller reconciles a view of `TrackedBranch` without a
  status, so it can't write status. It reads its last result through a view
  that declares only its own entry in `status.checks`, so it never sees
  another check's result. It sends each new result to the core program.
  Results record the commits they're for, and the merge controller ignores
  results for older commits.
- The **results** controller writes check results to `status.checks`. Each
  result goes to the entry of the check that sent it. See
  [Check results](#check-results).
- The **merge** controller evaluates the merge policy's `when` expression
  over the fresh results. When it passes, the controller lands the branch in
  the mirror's copy, as [Landing methods](#landing-methods) describes, but
  only if the parent still points to the commit that the checks saw, so it
  never overwrites a parent that moved in the meantime. If the policy says
  to, the same update deletes the branch, unless the branch moved since the
  repositories controller listed it. The repositories controller pushes
  both changes to the external repository. When the policy lets the `base`
  check push, branches whose gates pass wait in the parent's
  [merge queue](#merge-queue), and only the branch at the front lands.

The core program's fourth controller, **check-runs**, copies check results
to GitHub as check runs. See [Check runs](#check-runs).

The checks and the merge controller read each branch's repository as a
`gitk8s.Repository`, a `TrackedRepository` without its status, so the
repositories controller's status writes don't run them again.

Git objects live in the mirror's copies, and each check that reads files
keeps a local copy of the repositories that it reads. Only commit SHAs go
into Kubernetes objects. Apart from [events](#events), which the API server
deletes after an hour by default, no object records a single push or check
run, so the API server holds a bounded amount of state.

After a branch lands, `kubectl get trackedbranches` shows what's still open:

```
NAME                    BRANCH   HEAD                                       PARENT   STATE              QUEUE   AGE
app-c-auth-f684729ccf   c/auth   d28547a6c959905ea8dc037ac37541167a50638c   main     WaitingForChecks           9s
app-c-one-a7d8621874    c/one    04988fc4984947ac2af2b55d15bc96b8e49b5a2f   main     Queued             1       2s
app-c-two-de141ef616    c/two    62ebc5163be79d7963293a7e4c6152a967ed9838   main     Queued             2       2s
app-main-9157892a7c     main     610a7734a0b4d1bc1991a669d9feb35fd159219b                                       48s
```

The `Landed` condition on each `TrackedBranch` that has a parent says whether
the merge controller landed the branch, and `STATE` repeats the condition's
reason. The condition is `True` only when the controller lands the branch,
so `kubectl wait --for=condition=Landed` doesn't return for a branch that
someone just created from its parent:

| Status | Reason | Meaning |
| --- | --- | --- |
| `True` | `Landed` | The merge controller landed the branch. A branch that stays after it lands keeps this reason while its head is the parent's head. |
| `False` | `WaitingForChecks` | The merge policy's gate doesn't pass yet. The message lists the checks' states, for example `checks: approval Failed, base Passed, gofmt Passed, risk Passed (high)`. |
| `False` | `Queued` | The branch waits in its parent's [merge queue](#merge-queue). The message says what it waits for. |
| `False` | `NothingToLand` | The parent already has the branch's changes, such as when someone created the branch from the parent. The merge controller didn't land the branch, so it doesn't delete it. |
| `False` | `NotFastForward` | The branch doesn't contain the parent's head, so it can't land. |
| `False` | `Rewritten` | A squash or rebase landing moved the branch to new commits for the checks to run on. See [Which results count](#which-results-count). |
| `False` | `NeedsRebase` | A squash or rebase landing can't copy the branch's commits, for the reason in the message. See [Landing methods](#landing-methods). |
| `False` | `InvalidGate` | The gate fails to evaluate after every check finished, for the reason in the message. See [Merge gates](#merge-gates). |
| `False` | `Diverged` | The branch changed both in the mirror and in the external repository. See [Divergence](#divergence). |
| `False` | `NoMergePolicy` | No branches rule that matches the parent has a merge policy. |
| `False` | `ParentMissing` | The parent doesn't exist in the mirror. |

A branch without a parent has no state and no `Landed` condition. `QUEUE`
is a branch's place in its parent's [merge queue](#merge-queue).

## The mirror

The mirror serves the copy of each `TrackedRepository` at `/NAMESPACE/NAME.git`.
`generate` installs the core program behind the Service `git-k8s` in the
namespace `git-k8s`, so the copy of the `TrackedRepository` `app` in the
namespace `team` is at `http://git-k8s.git-k8s.svc/team/app.git`. The
Service's port 80 forwards to port 8081 of the core program's Pod, where
`kube.Serve` listens, and where the core program also serves the
[results endpoint](#check-results). If you install the core program under
another name or in another namespace, set `-mirror` to the mirror's base URL
on `check-base`, `check-gofmt`, `check-risk`, `check-approval`, `check-gotest`,
`check-review`, `check-conflicts`, `check-deps`, and `git-k8s-deps`, and set
`-results-url` to the results endpoint's URL on every check. Also set the
core program's `-mirror-namespace` and `-mirror-labels` to its own namespace
and labels, which it uses in the
[test Pods' NetworkPolicy](#sandboxed-checks), and change the
[agent Pods' NetworkPolicy](#agentic-checks) to match.

### Sync with the external repository

The mirror acknowledges a push as soon as its copy has it, and syncs it to
the external repository afterward, so git-k8s keeps working while the
external repository is down. After each push, the mirror triggers a
reconcile of the `TrackedRepository` with `kube.Trigger`, and the merge
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

The `ExternalSynced` condition on each `TrackedRepository` says whether the
external repository has every change in the copy:

| Status | Reason | Meaning |
| --- | --- | --- |
| `True` | `InSync` | The external repository has every change in the copy. |
| `False` | `Pending` | The external repository doesn't have the changes to the branches that the message lists yet. |
| `False` | `Diverged` | The branches that the message lists changed on both sides. See [Divergence](#divergence). |
| `False` | `CompareFailed` | The mirror couldn't compare the heads of the branches that the message lists, for the reasons in the message, such as a comparison that took too long. It leaves those branches as they are on each side, and they don't land. See [Divergence](#divergence). |
| `False` | `UpdateFailed` | The mirror couldn't update the branches that the message lists in its copy, for the reasons in the message. For example, the copy can't take the external repository's new branch `a/b` while it has a branch `a`, because git doesn't allow both in one repository. The mirror still syncs the other branches, and tries those again at each sync. |
| `False` | `SyncFailed` | Fetching from or pushing to the external repository failed, for the reason in the message. |
| `Unknown` | `FetchFailed`, `CredentialsUnavailable`, or `MirrorFailed` | The last sync failed before the mirror could compare the two sides. The `Ready` condition has the same reason and message. |

After a fetch or a push fails, the controller tries again within 30
seconds, or within `pollInterval` if that's shorter, and doesn't push until
then. Until a copy has fetched from its external repository once, the
mirror answers requests for it with `503 Service Unavailable`, and the
`TrackedRepository`'s `Ready` condition says why, with the reason `FetchFailed`
or `CredentialsUnavailable`. Each git command stops after the core
program's `-git-timeout`, 5 minutes by default, and git doesn't resume a
fetch that stopped, so for an external repository whose first fetch takes
longer, raise `-git-timeout`.

When you delete a `TrackedRepository`, the controller pushes the copy's last
changes to the external repository and then deletes the copy. While the
external repository lacks a change, because the sync fails or a branch
diverged, the `TrackedRepository` stays, and its `Synced` condition says why. It
also stays while the mirror can't compare a branch's heads. To delete it
anyway, with the changes that the external repository lacks, remove the
finalizer `kube.imjasonh.github.io/repositories`.

Each `TrackedRepository` and `TrackedBranch` has a `Synced` condition, which
kube sets after every reconcile of the object. After a reconcile succeeds,
`Synced` is `True` with the reason `Reconciled`. After one fails, it's
`False`, and its message says what failed. Its reason is then
`ReconcileError`, or `PermanentError` for an error that retrying won't fix,
such as an invalid `pollInterval`. After a `ReconcileError`, kube retries
the reconcile with backoff. After a `PermanentError`, it reconciles the
object again when the object changes. kube doesn't reconcile a
`TrackedRepository` that's being deleted, so its other conditions, such as
`ExternalSynced`, keep their values from before the deletion. If the
deletion can't finish, `Synced` is `False`, and its message says why. For
more about `Synced`, see
[Read the real state, declare the desired state](../kube/README.md#read-the-real-state-declare-the-desired-state)
in kube's README.

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
| The check `NAME`, which runs as a service account that the `git-k8s-checks` ConfigMap maps to `NAME`, as [Check service accounts](#check-service-accounts) describes | Each repository whose merge policies list the check | Each branch that has a parent whose merge policy gives the check `mayPush: true` |
| A controller that starts branches, or a check such as `check-conflicts`, whose service account the core program's `-branch-prefix` flag names | Every repository | The branches under its prefix, except parents |
| A Pod of a check, such as a test Pod of `check-gotest` or an agent Pod of `check-review` or `check-conflicts`, with a token that's bound to the Pod | The repository of the branch that the Pod works on, while the check's `Running` result on that branch names the Pod, the branch's merge policy lists the check, and the Pod is `Pending` | Nothing |

The merge controller is part of the core program and updates the copy
directly, so it's the only thing that moves a parent.

The mirror reads the ref updates at the start of each push before git
applies them, and refuses the whole push if it refuses any update in it.
git shows the reason to the person or program that pushed:

```
 ! [remote rejected] HEAD -> main (main is a parent branch, which only the merge controller updates)
```

A check can't create or delete branches unless `-branch-prefix` names its
service account, which gives the check a controller's rights as well as its
own. git updates a branch only if it still points to the commit that the
push expects, so a push never overwrites a change that the pusher hasn't
seen. Pushes can't see or change the mirror's own refs under
`refs/git-k8s/`, and git checks every object in a push with
`receive.fsckObjects`. To resolve a divergence, fetches can see the external
repository's heads under `refs/git-k8s/downstream/heads/`, and the heads
where the copy and the external repository last synced under
`refs/git-k8s/synced/heads/`.

The mirror reads at most 1,000 ref updates and shallow commits, in at most
1 MiB, at the start of a push, and a copy takes a pack of at most 256 MiB.
The mirror stops reading a request that takes longer than git's timeout
plus 10 seconds, 5 minutes 10 seconds with the default `-git-timeout`, and
stops writing a response twice that long
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
go run ./cmd/git-k8s generate -registry=REGISTRY -base=cgr.dev/chainguard/git:latest -- -branch-prefix=git-k8s-deps/git-k8s-deps=deps/ | kubectl apply -f -
```

The controller reaches the mirror with `mirror.Remote`, as a check does, and
a branches rule such as `match: deps/**` with `parent: main` tracks its
branches. `check-conflicts` needs the prefix `resolve/`, as
[Resolve conflicts](#resolve-conflicts) describes.

The mirror knows a controller only by the namespace and name of its service
account. Anyone who can create Pods or tokens in that namespace can act as
the controller, which can fetch every repository, so only cluster
administrators should control the namespace.

A check Pod's token is bound to the Pod, so it stops working when the Pod
is deleted, and it expires after 10 minutes. The mirror lets the Pod fetch
only while a `Running` result of the check on one of the repository's
branches names the Pod in its `pod` field, and the branch's merge policy
lists the check. `check-gotest` records the Pod's name before it starts the
Pod. `check-review` and `check-conflicts` name an agent Pod in the reconcile
that declares it, and kube writes that result right after it creates the
Pod. An agent Pod that fetches before the mirror sees the result fails to
fetch, and the check tries again in a new Pod, as after any failed fetch.

A Pod's name is known before the Pod exists, so another program that
creates Pods in the namespace could create a Pod with that name first. So
the mirror also checks the Pod itself, which is why `generate` lets the
core program get Pods. It reads the name and UID of the token's Pod from
the TokenReview, gets that Pod, and refuses the request unless the Pod has
that UID, has kube's label `kube.imjasonh.github.io/controller=check-NAME`
for a check `NAME` whose result names the Pod, isn't being deleted, and is
`Pending`. kube puts that label on the Pods that `check-NAME` declares. Only
the init container that fetches the branch has the token. A Pod is
`Pending` while its init containers run, so a test Pod's token stops
working when the tests start. An agent Pod's agent runs in a later init
container, without the token. The third admission policy in
`config/policy.yaml` keeps each check from setting another check's label,
as [Install](#install) describes. Any other program that can create Pods in
the namespace can set it, so the label means the check only as long as
those programs don't set it.

### Divergence

A branch diverges when the copy and the external repository both changed it
since they last synced, and neither side's head keeps the other side's
changes. For example, a check pushes a fix to the mirror while a person
pushes to GitHub, or a person force-pushes to GitHub to remove a commit
while a check pushes a fix on top of that commit to the mirror. The mirror
overwrites neither side. It keeps the external repository's head at
`refs/git-k8s/downstream/heads/BRANCH` in the copy, and the head where the
two sides last synced at `refs/git-k8s/synced/heads/BRANCH`. The merge
controller records both in the `TrackedBranch`'s status:

```yaml
status:
  state: Diverged
  diverged:
    commit: 3f1d0c2b9a8e7d6c5b4a39281706f5e4d3c2b1a0
    ref: refs/git-k8s/downstream/heads/c/auth
    base: 8c2e4a6f0b1d3c5e7a9f2b4d6c8e0a1f3b5d7c9e
```

If the external repository deleted the branch, `commit` and `ref` are empty.
If the copy deleted it, the branch has no `TrackedBranch`, and only the
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
branch's heads after twice the longest that one git command can take, 10
minutes 20 seconds with the default `-git-timeout`, or when one git command
runs past that timeout, and leaves the branch as it is on each side, with
the reason
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
- `COPY_HEAD`: the copy's head, which is the `TrackedBranch`'s `spec.head`
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
copy's head again. The [`conflicts` check](#resolve-conflicts) resolves
divergence by itself.

### Credentials

Only the core program pushes with the credentials of external repositories
or gets tokens from Octo STS. Each time the repositories controller fetches
from or pushes to an external repository, it reads the Secret that
`secretRef` names, and sends its `username` and `password` keys with HTTP
basic auth, or `git` as the username if the Secret has none. For a
repository on GitHub, it can use a token from Octo STS instead, as
[GitHub repositories](#github-repositories) describes. Checks and their test
Pods and agent Pods fetch only from the mirror, with their own tokens, so
`generate` doesn't let the checks request tokens. It lets only the checks
that [sign commits](#sign-commits) read Secrets, for the signing key. Agent
Pods that a controller starts with `RunJob`, and the update Pods of
`git-k8s-deps`, fetch from the external repository with the Secret's
credentials, as [Limitations](#limitations) describes. The
[`credentials`](credentials/credentials.go) package holds the only code that
reads credentials or gets tokens for external repositories, and is where
other ways to authenticate belong.

The mirror reaches external repositories only over the network. A `url`
that's a local path or a `file` URL fails, so a `TrackedRepository` can't read
another namespace's copy from the core program's volume.

Over the network, though, the core program reaches any address that its Pod
can, such as another namespace's Service, a node, or a cloud's metadata
service. Whoever can create a `TrackedRepository` can make the core program send
git's HTTP requests to those addresses, even when NetworkPolicies keep their
own Pods from reaching them. The address can be in the `url`, or in a
redirect from the server that the `url` names, because git follows a
redirect of its first request. The `TrackedRepository`'s conditions show git's
exit status and git's own messages, such as
`fatal: unable to access 'https://10.0.0.1/app.git/': The requested URL returned error: 403`.
They say whether the address answered, and with what HTTP status, but leave
out the body of an error response, which git prints after `remote:`. The
core program logs it instead.

`generate` doesn't limit where the core program connects. To limit it, add
an egress NetworkPolicy for the core program's Pod that allows only the API
server, DNS, your external repositories, and Octo STS and GitHub if you use
them. Without one, grant `create` on `trackedrepositories` only to people who
may send those requests.

## Events

The controllers record an event about a `TrackedBranch` each time they push a
fix to the branch, land it on its parent, or delete it, in the mirror's
copy. The repositories controller then pushes the change to the external
repository, as
[Sync with the external repository](#sync-with-the-external-repository)
describes. A branch without a parent takes no check
results, so `check-conflicts` also records an event when it finds that such
a branch diverged:

| Reason | From | When |
| --- | --- | --- |
| `PushedFix` | `check-NAME` | A check pushed a fix commit to the branch, or `check-conflicts` pushed `resolve/BRANCH` for a diverged branch without a parent. |
| `ResolvingDivergence` | `check-conflicts` | `check-conflicts` found a diverged branch without a parent, and pushed nothing. A `Warning` says what keeps the check from resolving the divergence. A `Normal` event says that the check waits for `resolve/BRANCH` to land, or that nothing is left to resolve. |
| `Landed` | `merge` | The merge controller fast-forwarded the parent to the branch, or squashed or rebased the branch onto the parent. |
| `DeletedBranch` | `merge` | The merge controller deleted the branch after it landed. |

`kubectl describe trackedbranch TRACKEDBRANCH` lists a branch's events. After
the merge controller deletes a branch, the repositories controller deletes its
`TrackedBranch`, so list the namespace's events instead:

```sh
kubectl get events --sort-by=.metadata.creationTimestamp
```

After `c/fmt` in the end-to-end test lands, the output looks like this:

```
LAST SEEN   TYPE     REASON          OBJECT                           MESSAGE
14s         Normal   PushedFix       trackedbranch/app-c-fmt-793d86522b   pushed 5d0c2e9a71b4 to c/fmt: 1 of 2 Go files need gofmt: util/add.go
9s          Normal   Landed          trackedbranch/app-c-fmt-793d86522b   fast-forwarded main from 0e4f8a2c9d13 to c/fmt at 5d0c2e9a71b4
9s          Normal   DeletedBranch   trackedbranch/app-c-fmt-793d86522b   deleted c/fmt at 5d0c2e9a71b4 after it landed on main
```

kube drops events when it falls behind on writing them, and the API server
deletes events after an hour by default. To audit what landed, use the git
history of the copy or of the external repository. `generate` grants
`create` and `patch` on events to the `git-k8s` program and to every check
program. A check that never pushes a fix, such as `check-approval`, gets the
grant too, because the `checks` package that every check uses records
`PushedFix`.

## GitHub repositories

For a repository on github.com, a `TrackedRepository` can name
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
checks, `git-k8s-deps`, `check-gotest`'s test Pods, and the agent Pods of
`check-review`, `check-conflicts`, and `check-deps` fetch from the mirror, so
`gotest`, `review`, `conflicts`, and `deps` work for a private repository
too. The update Pods of `git-k8s-deps` fetch from the external repository,
without credentials when the `TrackedRepository` has no `secretRef`, so with
Octo STS, `git-k8s-deps` updates only a public repository. The core program
publishes [check runs](#check-runs) with tokens for `checkRunsIdentity`, and
publishes none without it. The URL must have the form
`https://github.com/OWNER/REPO`, with or without `.git`.

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
   - `NAMESPACE`: the `TrackedRepository`'s namespace

4. Apply the `TrackedRepository`.

A service account token's subject is `system:serviceaccount:NAMESPACE:NAME`.
When you install the core program with `generate`, as [Install](#install)
describes, it runs as the service account `git-k8s` in the namespace
`git-k8s`. It's the only program that asks Octo STS for tokens, so both
trust policies name only its service account. If you install it under
another name or in another namespace, change `subject` to match.

Each token's audience is `octo-sts.dev/` followed by the `TrackedRepository`'s
namespace. The core program uses the same service account for every
`TrackedRepository`, so the audience is the part of a token that names the
namespace it's for. A trust policy that requires your namespace's audience
refuses the tokens that git-k8s requests for a `TrackedRepository` in another
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
`TrackedRepository`'s `Ready` condition is `False` with the reason
`CredentialsUnavailable`. After that, its `ExternalSynced` condition is
`False` with the reason `SyncFailed`, and checks keep working on the copy.
Both messages include Octo STS's answer, such as
`unable to find trust policy for "git-k8s"`. Octo STS caches each trust
policy, and the lack of one, for 5 minutes, so a change to a trust policy can
take that long to apply.

### Check runs

When a `TrackedRepository` names a `checkRunsIdentity`, the core program's
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
`TrackedRepository` are at the same commit, they share the check run for each
check, and it shows the result that changed last, for either branch.

The check run's title is the result's state. Its summary is the result's
message, or the state when the result has no message, and its text lists the
result's `fix` and outputs. The controller puts the message and the text in
code blocks, so GitHub shows what a check writes as it is, not as Markdown.

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
repository's `TrackedBranch` objects is deleted or the `TrackedRepository` loses
its `checkRunsIdentity`. After a restart, the controller finds each branch's
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
sets the `CheckRunsTokenIssued` condition on the `TrackedRepository`, which is
`False` with Octo STS's answer when Octo STS doesn't issue a token. The
`TrackedRepository` stays `Ready` either way.

### Security

The core program keeps GitHub tokens in memory and passes them to git in its
environment, so the tokens don't appear in process arguments, Kubernetes
objects, or logs. The service account tokens that it sends to Octo STS are
bound to its Pod and last an hour. `generate` lets the core program request
tokens for its own service account, and for no other. The checks' only
tokens are for the mirror and the results endpoint, and `generate` mounts
those, so the checks can't request tokens at all.

The core program sends the service account tokens for Octo STS only to Octo
STS, and GitHub tokens only to GitHub. For tests, its `-fake-github` flag
points it at a fake GitHub and Octo STS instead. It's a flag and not a
`TrackedRepository` field, so only whoever installs the core program can choose
where its tokens go. The end-to-end test's git server runs such a fake,
which checks each service account token with a TokenReview, because Octo
STS can't reach a kind cluster's issuer.

A trust policy's audience ties it to one namespace, so anyone who can create
a `TrackedRepository` in that namespace can use the trust policy's permissions.
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
| `check-base` | `base` | Passes when the branch contains its parent's head, or the parent already contains the branch. Otherwise it merges the parent in with `git merge-tree`, and fails with the conflicting paths if the merge conflicts. The merge ignores `.gitattributes` files, so that a branch can't choose how its own conflicts merge. With `mayPush`, it merges the parent in only at the front of the parent's [merge queue](#merge-queue), and until then passes a branch that merges cleanly, with `outputs.behind` set to `"true"`. |
| `check-gofmt` | `gofmt` | Formats every `.go` file outside `vendor` and `testdata` directories with `go/format`, and passes when nothing changes. It fails on a file that doesn't parse or is larger than 8 MiB, and on a head whose list of files from `git ls-tree` is larger than 16 MiB, about 150,000 files. |
| `check-risk` | `risk` | Always passes, and sets `outputs.level` to `high` for a large change, a change to a sensitive path, a new or unreleased dependency, or code from an AI agent, and to `low` otherwise. See [Risk ratings](#risk-ratings). |
| `check-approval` | `approval` | Passes when the `git-k8s.imjasonh.com/approve` annotation on the `TrackedBranch` names the branch's head, or a commit whose change the head makes too, and sets `outputs.approver` to the `git-k8s.imjasonh.com/approved-by` annotation. A push that changes the code needs a new approval. See [Approve a branch](#approve-a-branch). |
| `check-gotest` | `gotest` | Runs `go test ./...` in a Pod that it declares with `kube.Own`, and fails with the end of the test output. See [Sandboxed checks](#sandboxed-checks). |
| `check-review` | `review` | Has an AI agent review the branch's change against its parent in a sandboxed Pod. It passes or fails with the agent's reasoning as its message, and records the agent's summary and the run's token counts in its notes. With `mayPush: true`, the agent can also fix what it finds. See [Agentic checks](#agentic-checks). |
| `check-deps` | `deps` | On a dependency branch, passes when the `gotest` check passes. When the tests fail, it has an AI agent change the code to fit the new versions, and pushes the agent's fix. It passes on other branches. See [Dependency updates](#dependency-updates). |
| `check-conflicts` | `conflicts` | Passes when merging the parent into the branch has no conflicts. When the merge conflicts, or the branch diverged from the external repository, it pushes a merge that git or an AI agent resolved, or fails when neither can. When a side of a diverged branch rewound, it replays the other side's commits onto that side's head instead of merging. See [Resolve conflicts](#resolve-conflicts). |

A check with `mayPush: true` pushes its fix commit to the branch in the
mirror, which moves the head and runs the checks again. Fix commits have a
`Git-K8s-Fixer: CHECK` trailer, and `maxAutomatedCommits` (default 5) limits
how many a branch can have, so two checks that undo each other's fixes stop.
The same inputs always produce the same fix commit, so two retries of one
fix push the same commit.

### Approve a branch

An approval is two annotations on the `TrackedBranch`: `approve`, which names
the commit, and `approved-by`, which names you. Set both in one request:

```sh
kubectl annotate --overwrite trackedbranch TRACKEDBRANCH git-k8s.imjasonh.com/approve=SHA \
  git-k8s.imjasonh.com/approved-by="$(kubectl auth whoami -o jsonpath='{.status.userInfo.username}')"
```

An approval is for a change: what the approved commit changes on top of its
merge base with the parent's head. `check-approval` passes for any head that
makes the same change on top of its own merge base, as
[Which results count](#which-results-count) defines, so the files that land
are the parent's files with the approved change. An approval holds when
`check-base` merges the parent into the branch at the front of the
[merge queue](#merge-queue), after a rebase or a squash that doesn't resolve
a conflict, and for the commit that a squash or rebase landing makes. A push
that adds, removes, or changes code needs a new approval, and so does a
merge that resolves a conflict.

`approve` must name the commit's full SHA, as `git rev-parse` prints it.
Anyone who can push can make a commit whose SHA starts with a shorter
prefix, so `check-approval` fails a prefix, and the `git-k8s-approvals`
policy rejects one. You can approve a commit after the branch moves on from
it, such as when `check-base` merges the parent in while you review the
change. The check's message then names both commits, for example
`1bd279367630 is approved by alice, and 9132990e9ac2 makes the same change`.
To compare the changes, `check-approval` reads the repository from the
[mirror](#the-mirror). If the mirror no longer has the approved commit, the
check fails, and the branch needs a new approval.

The `git-k8s-approvals` policy in `config/policy.yaml` enforces these rules:

- Setting, changing, or removing the `approve` or `approved-by` annotation
  requires the `approve` verb on the `TrackedBranch`. `generate` grants that
  verb to no program, so grant it to the people who approve. The policy
  checks for the verb in the `TrackedBranch` object's namespace, so run these
  commands for each namespace that has a `TrackedRepository`:

  ```sh
  kubectl -n NAMESPACE create role approver --verb=get,list,watch,patch,approve --resource=trackedbranches.git-k8s.imjasonh.com
  kubectl -n NAMESPACE create rolebinding approver --role=approver --group=GROUP
  ```

  kubectl warns that `approve` isn't a standard resource verb. The warning
  is expected, and kubectl creates the Role.

- `approve` must be a commit's full SHA, in lowercase hexadecimal.
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
kubectl annotate --overwrite trackedbranch TRACKEDBRANCH git-k8s.imjasonh.com/approve=SHA
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
- It changes a file that git treats as binary, such as one with a NUL byte
  in its first 8,000 bytes, because git counts no lines in such a file.
- It touches a path that matches a `-sensitive` glob.
- A `go.mod` file that it changes requires a module that no `go.mod` file
  at the merge base requires, moves a module to an earlier version than the
  file required, to a new major version, or to a version that isn't a
  release, such as a pseudo-version, replaces a module with another module
  or with a directory outside the repository, stops replacing one, or
  changes the `go`, `toolchain`, or `godebug` lines. For a new `go.mod`
  file, the check compares those lines with the ones in the `go.mod` file
  of the module that its directory was in at the merge base, or with no
  lines if the directory was in no module. A directory is outside the
  repository when its path is absolute, leads out of the repository from
  the `go.mod` file's directory, or goes through a symbolic link or a
  submodule, because the `go` command follows the link, which can point
  anywhere, and a submodule's files come from another repository. A
  `go.mod` file that the check can't parse also counts. Requiring a module
  that the file replaces with a directory in the repository is fine,
  because that code is in the repository. Requiring a module that only a
  `go.mod` file in the repository declares isn't, because without a
  replacement, the `go` command downloads the module from the module proxy.
- It adds or changes a symbolic link that the directory of a replacement in
  any `go.mod` file goes through, even when no `go.mod` file changes.
- It adds or changes a submodule, whose files come from another repository,
  or changes the `.gitmodules` file, which names that repository.
- It changes a `go.work` file, whose directives apply to every module in
  the workspace.
- The check can't read all of it: the list of files that it changes is
  larger than 8 MiB, the list of files in the head or at the merge base is
  larger than 16 MiB, each about 150,000 files, or a `go.mod` file that the
  check reads is larger than 8 MiB.
- It has commits from AI agents, which carry a `Git-K8s-Agent: CHECK`
  trailer, because no person wrote that code.

Otherwise the change is `low` risk. So a patch or minor release of a module
that any part of the repository already requires is low risk, and lands
without approval under a gate such as
`checks.risk.outputs.level == "low" || checks.approval.passed`. The check
skips `go.mod` files in `testdata` and `vendor` directories. Its message
lists every reason, for example `risk is high: adds module example.com/c;
has changes from AI agents`.

The check rates each change once. The rating holds when the parent moves,
and for any head that makes the same change, such as `check-base`'s merge of
the parent, a rebase, or a squash, as
[Which results count](#which-results-count) describes. A rating that reads
`go.mod` files at the merge base, which the check does for a change to a
`go.mod` file or a symbolic link, holds only for the parent's head, so the
check rates such a change again when the parent moves.

### Write a check

A check is a `checks.Check` and a view type that names its key in
`status.checks`. The framework reads the check's last result through the
view, and sends each new result to the core program. This `main` package,
next to the others in `cmd/`, is a complete check that fails branches
without a `README.md`:

```go
type Branch struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=TrackedBranch,plural=trackedbranches,scope=Namespaced"`
	Spec        gitk8s.TrackedBranchSpec `json:"spec"`
	Status      struct {
		Checks struct {
			Result *gitk8s.CheckResult `json:"readme,omitempty"`
		} `json:"checks,omitzero"`
	} `json:"status,omitzero"`
}

func (b *Branch) Parts() (*kube.ObjectMeta, *gitk8s.TrackedBranchSpec, **gitk8s.CheckResult) {
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
the mirror. A check makes a `Fix` commit with `in.CommitTree`, or replays
commits with `in.Replay`, which also need `SigningKey: signing.Key` to
[sign the commits](#sign-commits). `generate` grants a program what its
packages call. It mounts the mirror's token in the Pods of each program
that uses `mirror.Remote`, and lets each program that uses `signing.Key`
read Secrets. A check that reads only the `TrackedBranch` leaves both out, so
its program gets no token for the mirror and can't read Secrets.

A verdict's `Outputs` are for merge gates, such as a risk level. Its `Notes`
are other values that the check records, such as what its next run needs or
what an agent's run used, and gates don't see them. A result's notes replace
the last result's, so a check that keeps a value copies it from
`in.Previous`. An `Error` result keeps the verdict's notes, or the last
result's when `Run` returns an error or the core program wouldn't accept the
verdict's notes, so an error doesn't reset a count such as an agent's runs.
A verdict's `Pod` names a Pod that does the check's work, which the mirror
lets fetch the repository while the result is `Running`, as
[Who can fetch and push](#who-can-fetch-and-push) describes. A `Fixed`
result names the commit that the framework pushed in `fix`.

The core program accepts at most 16 outputs and 32 notes, with names of up
to 63 bytes. For a verdict with more, the framework reports `Error` and
doesn't push its fix. The framework shortens messages, output values, and
note values to 1,024 bytes, the most that the core program accepts.

A check runs again when the branch's head changes, and with `UsesParent`,
when the parent's head changes. `Always` runs it on every reconcile, for a
check that reads more of the `TrackedBranch` than its heads, such as an
annotation. `Stale` runs it again when something that it reads with
`kube.Get` makes a finished result out of date, the way `check-base` runs
again when its branch reaches the front of the merge queue.

Set `SameChange` instead of `UsesParent` when the check's result is for the
branch's change: what its head changes on top of its merge base with the
parent's head. The framework keeps such a result, if it's `Passed` or
`Failed` without a fix, for any later head that makes the same change, as
[Which results count](#which-results-count) describes. So the check doesn't
run again when the parent moves, or after a merge of the parent, a rebase,
or a squash that makes the same change. A verdict that also depends on files
at the merge base that the change doesn't touch sets `UsesParent` in its
`checks.Verdict`, and holds only for the parent's head, as `check-risk`'s
rating of a change to a `go.mod` file does. A check that compares changes
in `Run` with `in.ChangeOf` and `in.SameChange`, as `check-approval` does,
sets `MergeBase` in its verdict to the merge base that the verdict is for.

Set `FilesOnly` in a check's `checks.Check` when its result for the branch's
head also holds for any commit with the same files that builds on the same
parent head, because the result doesn't depend on the branch's commits, such
as their messages or authors. Squash and rebase landings count only such
results for the commits that they make, as
[Which results count](#which-results-count) describes.

To install the check, save the package as `cmd/check-readme`, and install
it the way that [Install](#install) installs the other checks. `generate`
installs it with the service account `check-readme` in the namespace
`check-readme`. Then map that service account to the check in the
`git-k8s-checks` ConfigMap:

```sh
go run ./cmd/check-readme generate -registry=REGISTRY -base=cgr.dev/chainguard/git:latest | kubectl apply -f -
kubectl -n git-k8s patch configmap git-k8s-checks --type=merge \
  -p '{"data":{"check-readme.check-readme":"readme"}}'
```

Until the entry exists, the core program answers the check's results with
`403 Forbidden` and a message that says `isn't a check's service account`,
and the check sends nothing more for a branch until the branch changes or
the check restarts. The mirror doesn't let it fetch or push either, as
[Check service accounts](#check-service-accounts) describes. Last, add
`readme` to `merge.checks` in the rule of each parent whose branches need
it, as in [How it works](#how-it-works).

### Sandboxed checks

The checks that read files run in their controller's process. A check that
runs the branch's code, such as `go test`, runs it in a Pod instead.
`check-gotest` declares one Pod for each head with `kube.Own`, and reports
`Running` until the test container exits or an init container fails:

- An init container fetches the head from the mirror. It's the only
  container with a token for the mirror, and the token is bound to the Pod.
  The token reaches git through the init container's environment, not the
  repository's configuration, which the test container can read.
- The test container runs `go test ./...` as user 65532 with no service
  account token, no privileges, and a read-only root file system. It has
  `GOPROXY=off`, so tests can't download modules, unless you
  [share modules and build outputs](#share-modules-and-build-outputs).
- A NetworkPolicy that the core program owns lets the Pod reach only the
  port of the core program's Pod that serves the mirror and the
  [results endpoint](#check-results), which both need a token that the test
  container doesn't have, and the cluster's DNS servers, and lets nothing
  reach it. With the
  core program's `-go-cache-namespace`, the policy also lets the Pod reach
  `go-cache`, as
  [Share modules and build outputs](#share-modules-and-build-outputs)
  describes. When the core program's `-goproxy` isn't `off`, the policy also
  lets the Pod reach ports 80 and 443 on IPv4 addresses outside the private
  ranges (`10.0.0.0/8`, `172.16.0.0/12`, and `192.168.0.0/16`), the shared
  address space (`100.64.0.0/10`), and the link-local range
  (`169.254.0.0/16`). Those ranges usually hold the cluster's Pods,
  Services, and nodes, and a cloud's metadata server. If your cluster gives
  Pods, Services, or nodes addresses outside those ranges, the policy lets
  test Pods reach those addresses on ports 80 and 443 too, so leave
  `-goproxy` `off` there.
- If fetching fails, the check starts a new Pod 30 seconds later, and 60
  seconds after a second failure, so its three Pods outlast a restart of the
  core program.
- At most `-max-pods` test Pods, 10 by default, run at once across all
  namespaces. A branch that can't start its Pod yet reports `Running` and
  records when it started waiting in `notes.waiting`. When a Pod's phase
  becomes `Succeeded` or `Failed`, or the Pod no longer exists, the next
  branch starts. Branches at the front of a [merge queue](#merge-queue) go
  first, then the branch that has waited longest. A new head, a retry after
  a failed fetch, or a replacement for a deleted Pod waits behind the
  branches that are already waiting, unless its branch is at the front of a
  queue. The times and the places in the queues are in the `TrackedBranch`
  status, so a restarted check keeps the order.
- Only the front of a queue lands, so a front that waits for a Pod holds up
  every branch behind it. The rest of a queue waits in line with the
  branches that aren't queued, because the `base` check merges the parent
  into each of those branches when it reaches the front, which runs the
  tests again, and their places change at every landing. When the fronts of
  `-max-pods` or more queues wait at once, every test Pod can go to a
  front. Other branches then wait until the queues drain, which they do
  because a branch whose tests haven't passed can't join a queue. A branch
  counts as the front once the merge controller keeps it in the queue at
  its head, moments after the `base` check pushes its merge of the parent.
  The check reads the places in the queues through a view of `TrackedBranch`
  that declares only `status.queued.head` and `status.queued.position`, so
  it still sees no other check's result, and `generate` grants it no new
  permissions, because it already lists and watches `TrackedBranch` objects.
- The check counts a Pod from the moment that it declares it, before its
  cache shows the Pod, so a burst of pushes can't start more than
  `-max-pods`. A Pod that never appears stops counting after a minute. If
  the API server refuses a Pod, for example because the check Pod policy
  denies it, other branches can then use its place while kube tries again.
  Until the Pod exists, its branch keeps the time that it started waiting in
  `notes.queued`, so the branch keeps its place in line. With `-shards`, a
  replica doesn't count the Pods that other replicas declared until its
  cache shows them, so replicas that start Pods at the same moment can go
  over the limit.

The check records a Pod's result as soon as the Pod's status shows that the
test container exited or an init container failed. The kubelet sets the
Pod's phase about a second later, after it stops the Pod's sandbox, and the
Pod counts toward `-max-pods` until then. kube deletes a Pod when the check
stops declaring it: once the check has recorded the Pod's result and the
Pod's phase is `Succeeded` or `Failed`, or when the branch moves to a new
head. The API server deletes a Pod in either phase at once, but waits for
the kubelet to stop a running one. The kubelet sends the containers of a
running Pod `SIGTERM`, and kills them when the Pod's termination grace
period ends. A container's first process ignores `SIGTERM` unless it
handles the signal, and the shell that fetches the head without
`-go-cache` doesn't, so test Pods set the grace period to 2 seconds, the
kubelet's minimum, instead of the default 30. Owner references delete the
Pods with their `TrackedBranch`.
Set `-runtime-class` to run the Pods under a sandboxing runtime such as
gVisor, and `-go-image`, `-git-image`, `-timeout`, and `-goproxy` to change
the rest. If you set `-goproxy`, set the same value on the core program.

The test container runs the Go in `-go-image` with `GOTOOLCHAIN=local`, so
the tests of a module that needs a newer Go fail until you set `-go-image`
to an image that has it. The default names an image by digest, as
[Install](#install) describes, so it doesn't move to a newer Go until you
upgrade `check-gotest`.

Each test Pod's volumes have size limits. The repository can use up to
`-source-size`, 2Gi by default, and the home directory, which holds Go's
module and build caches and the tests' temporary files, up to
`-go-cache-size`, 4Gi by default. With `-go-cache`, the build outputs that
the Pod shares can use up to `-go-cache-size` too. Each container requests
1Gi of ephemeral storage, and its limit covers all the volumes and 256Mi of
logs. That's 6400Mi by default, and 10496Mi with `-go-cache`. When a Pod
uses more than a limit, the kubelet evicts it, and the check fails with the
kubelet's reason.

Each container can use up to `-cpu-limit` CPUs, 2 by default, and
`-cpu-limit=0` removes the limit. Go 1.25 and later set `GOMAXPROCS` from
that limit, and `go test` runs that many builds and test binaries at once,
so the limit also bounds how many of them share the test container's 2Gi
of memory.

The scheduler reserves only a Pod's requests on its node. So a node can
run low on disk space or memory while each Pod stays within its limits,
and then the kubelet evicts Pods, first those that use more than they
request. A ResourceQuota on `limits.cpu` or `limits.ephemeral-storage`
counts each test Pod's limits, and a LimitRange with a smaller maximum for
either resource rejects every test Pod.

The core program owns the NetworkPolicy so that `check-gotest`, which
creates Pods in every namespace that has a `TrackedBranch`, can't change
NetworkPolicies. Each `TrackedRepository` owns one policy, `NAME-test-pods`. It
selects the Pods in the repository's namespace that have kube's controller
label for `check-gotest`, `kube.imjasonh.github.io/controller=check-gotest`,
which are the Pods that run a branch's code. The policies of the
`TrackedRepository` objects in a namespace are the same, so each one covers
every test Pod there. The repositories controller declares the policy before the
`TrackedBranch` objects, so it exists before `check-gotest` starts the first
test Pod for a new `TrackedRepository`. If someone deletes the policy, the next
reconcile of the `TrackedRepository` that succeeds creates it again. When you
delete the last `TrackedRepository` in a namespace, garbage collection deletes
the policy with the `TrackedBranch` objects, before the test Pods that they own,
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

All of a test Pod's containers meet the `restricted`
[Pod Security Standard](https://kubernetes.io/docs/concepts/security/pod-security-standards/).
An admission policy keeps each check to its own Pods, in namespaces that
opt in to check Pods and enforce the `restricted` standard. See
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
  `TrackedRepository`, hold what the go command compiled, by action ID. The go
  command derives an action ID from everything that goes into a build step,
  such as the source files, the compiler and its flags, and the step's
  dependencies.

Install `go-cache` with `generate`, apply `config/go-cache.yaml`, set
`check-gotest`'s `-go-cache` flag to `go-cache`'s URL, and set the core
program's `-go-cache-namespace` flag to `go-cache`'s namespace:

```sh
go run ./cmd/go-cache generate -registry=REGISTRY \
  -base=cgr.dev/chainguard/static:latest -replicas=1 -tmp-size=10Gi \
  -- -max-size=8Gi | kubectl apply -f -
kubectl apply -f config/go-cache.yaml
go run ./cmd/check-gotest generate -registry=REGISTRY \
  -base=cgr.dev/chainguard/git:latest \
  -- -go-cache=http://go-cache.go-cache | kubectl apply -f -
go run ./cmd/git-k8s generate -registry=REGISTRY \
  -base=cgr.dev/chainguard/git:latest \
  -- -go-cache-namespace=go-cache | kubectl apply -f -
```

Pass `-go-cache-namespace` with the core program's other flags. It makes
the test Pods' [NetworkPolicy](#sandboxed-checks) let them reach port 8080
on the Pods labeled `app.kubernetes.io/name=go-cache` in that namespace.
NetworkPolicies match the port that a Service sends connections to, and
`go-cache` listens on port 8080 behind its Service's port 80. If its Pods
have other labels, also set the core program's `-go-cache-labels`.

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

With `-go-cache`, a test Pod has three init containers:

1. `fetch` runs `check-gotest`'s own image, which `generate` names in the
   `KUBE_IMAGE` environment variable, instead of `-git-image`. It copies
   the `check-gotest` binary to a volume, and then fetches the head with
   git. The binary is the Pod's `GOCACHEPROG`, the program that the go
   command asks for build outputs. Build `check-gotest` on an image that
   has git, as [Install](#install) does.
2. `build` runs the `check-gotest` binary from the volume in the Go image,
   with the test container's environment. It lists the packages that
   `go test` needs, and compiles the ones from GOROOT and the module cache
   with `go list -export`, which neither links nor runs anything. Its
   `GOCACHEPROG` reads outputs from the repository's build cache, with a
   service account token that can only read it.
3. `upload` sends what `build` compiled to the build cache, with a token
   that can write to it. It runs `check-gotest`'s image, and doesn't mount
   the branch's files.

Test Pods run in the `TrackedBranch`'s namespace as its `default` service
account and don't set `imagePullSecrets`, so each namespace that has a
`TrackedRepository` must be able to pull `check-gotest`'s image. If pulling
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
- Only `check-gotest`'s code and git run before `build`. `fetch` copies
  the `GOCACHEPROG` program from `check-gotest`'s image, and then runs git,
  which runs none of the branch's code. A git bug that ran code from the
  fetched objects could replace the program. That bug could change what
  `build` runs anyway. `fetch` can write the go command's environment
  file, which `build` reads from the `tmp` volume, and `GOFLAGS` in that
  file can add `-toolexec`. So copying the program in an init container of
  its own, which the kubelet would start about a second after `fetch`
  exits, wouldn't keep git from changing what `build` runs.
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
  read the build caches of a namespace that opts in to check Pods, where
  they can already mount the namespace's Secrets. Reads don't change what
  any Pod compiles. Namespaces don't share build caches.

The design leaves these risks:

- The defense relies on git and the go command not running code from the
  files that they read. A bug that let a branch run code in `fetch` or
  `build` would let it store any output under action IDs that the build
  cache doesn't have yet.
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

### Agentic checks

`check-review` runs an AI agent with the
[Cursor SDK](https://www.npmjs.com/package/@cursor/sdk). Like
`check-gotest`, it declares a Pod for each head with `kube.Own`, and
reports `Running` until the Pod finishes. The `agent` package declares the
Pods, so other checks can run agents the same way. Each Pod has three
containers:

- The `prepare` init container fetches the head from the mirror, with a
  token for the mirror that's bound to the Pod, as
  [Who can fetch and push](#who-can-fetch-and-push) describes. The token
  reaches git through the container's environment, not the repository's
  configuration. The container writes the head's files to a directory that
  isn't a git repository, without the `.cursorignore` files that Cursor
  reads to hide files from the agent. Next to it, it writes the change from
  the merge base, the paths that the change touches, and the commit log. It
  also copies the Cursor API key from a Secret to a memory volume. It's the
  only container that gets the token or reads a Secret.
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

The kubelet reports the `result` container as running a moment before its
server listens, so a check that fetches right away can find nothing
listening. When the Pod refuses the connection less than 10 seconds after
the container starts, the check tries again after a quarter second. After
other failed fetches, it waits 5 seconds.

kube deletes an agent Pod once the check has its result, or when the check
stops declaring the Pod for another reason, such as a new head. The kubelet
sends the Pod's containers `SIGTERM`, and kills them when the Pod's
termination grace period ends. A container's first process ignores
`SIGTERM` unless it handles the signal. The `prepare` container's shell
doesn't, and the runner does only once the `result` container's server
listens, so agent Pods set the grace period to 2 seconds, the kubelet's
minimum, instead of the default 30. A Pod counts toward `-max-pods` until
its containers stop.

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
The check commits what changed on the head, and [signs](#sign-commits) and
pushes the commit like any other fix, with `Git-K8s-Fixer: review` and
`Git-K8s-Agent: review` trailers and within `maxAutomatedCommits`. The
second trailer makes `check-risk` rate the branch high. A fix leaves
`.cursorignore` files as they are. If a path in the head isn't valid UTF-8,
the run fails before the agent starts. Without `mayPush`, the agent's files
are read-only.

The check's notes hold the agent's `summary`, the `model`, the run's
`inputTokens`, `outputTokens`, `cacheReadTokens`, and `cacheWriteTokens`,
and two costs in cents when the SDK reports them. `costCents` is the model
token cost before discounts, the SDK's `rawCostCents`. `chargedCents` is
what Cursor charged, with discounts and fees, the SDK's `chargedCents`; it's
0 for usage that a Cursor plan includes. `runs` counts the agent runs on
the branch, and the result's `pod` names the run's Pod. `state`, `base`, and
`url` hold what the check needs to follow the run, such as the URL that its
Pods fetch from, so the check keeps the run's Pod while it can't reach the
mirror.

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
the check's notes.

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

The check counts a branch's runs in its notes on the branch's
`TrackedBranch`, so a branch that's deleted and then pushed again can start
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
[Install](#install) describes. Last, map the check's service account to
`review` in the `git-k8s-checks` ConfigMap, as
[Check service accounts](#check-service-accounts) describes:

```sh
docker build -t REGISTRY/agent-runner agent/runner
docker push REGISTRY/agent-runner
image="$(docker inspect -f '{{index .RepoDigests 0}}' REGISTRY/agent-runner)"
go run ./cmd/check-review generate -registry=REGISTRY -base=cgr.dev/chainguard/git:latest -- -agent-image="${image}" | kubectl apply -f -
kubectl -n NAMESPACE create secret generic cursor-api-key --from-literal=api-key=KEY
kubectl label namespace NAMESPACE git-k8s.imjasonh.com/check-pods=true pod-security.kubernetes.io/enforce=restricted
kubectl -n git-k8s patch configmap git-k8s-checks --type=merge \
  -p '{"data":{"check-review.check-review":"review"}}'
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
| `-git-image` | `cgr.dev/chainguard/git` by digest | Image that fetches the source; it needs `git` and `sh` |
| `-backend` | `cursor` | Where the agent runs: `cursor`, with the Cursor SDK in the Pod, or `fake`, for tests |
| `-model` | `composer-2.5` | Model that the agent uses |
| `-api-key-secret` | `cursor-api-key` | Secret, in each branch's namespace, whose `api-key` key holds the API key |
| `-timeout` | `15m` | Longest that an agent can run |
| `-max-pods` | 10 | Most agent Pods to run at once, in all namespaces; 0 means no limit |
| `-max-runs-per-day` | 100 | Most agent runs to start in any 24 hours; 0 means no limit |
| `-runtime-class` | None | RuntimeClass for agent Pods, such as `gvisor` |
| `-source-size` | `2Gi` | Most disk space that each of an agent Pod's repository, files, and input can use |
| `-storage-request` | `1Gi` | Ephemeral storage that each agent Pod requests, which the scheduler reserves on the Pod's node |

Agent Pods need to reach the mirror on TCP port 8081 of the core program's
Pods and Cursor's API over HTTPS, and the check needs to reach the agent
Pods on TCP port 8080. A NetworkPolicy matches IP addresses, not host names,
so by itself it can't limit agent Pods to Cursor's API. This policy allows
the agent Pods DNS, the mirror, HTTPS to any address, and requests from
`check-review` and [`check-conflicts`](#resolve-conflicts):

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
            matchExpressions:
              - key: kubernetes.io/metadata.name
                operator: In
                values: [check-review, check-conflicts]
      ports:
        - port: 8080
  egress:
    - ports:
        - port: 53
          protocol: UDP
        - port: 53
          protocol: TCP
    - to:
        - namespaceSelector:
            matchLabels:
              kubernetes.io/metadata.name: git-k8s
          podSelector:
            matchLabels:
              app.kubernetes.io/name: git-k8s
      ports:
        - port: 8081
    - ports:
        - port: 443
```

To allow only Cursor's API over HTTPS, use a CNI plugin with DNS-based
rules, such as Cilium's `toFQDNs`.

To write an agentic check, give an `agent.Runner` the check's name, register
its flags, and call its `Run` method with a task. Set the check's `Remote`
to `mirror.Remote`, because `Run` gives the agent Pods the URL of the
check's remote. With a view type like the one in
[Write a check](#write-a-check), but with the key `docs`, this is a
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
	checks.Main[Branch](checks.Check{Name: "docs", Remote: mirror.Remote, SigningKey: signing.Key, Run: run})
}
```

`Run` commits the agent's changes with `in.CommitTree`, so a check whose
agent can edit needs `SigningKey: signing.Key`.

`Run` never returns an error, because a check that returns one keeps its
last result's notes, which don't count a run that the call started. It
also returns the agent's `Result`, with the files that the agent changed,
so a check can build another kind of commit from them with
`agent.ApplyFiles` and `in.CommitTree`.

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
  conflicts. If a commit can't be replayed by itself, such as a merge, a
  commit whose replay conflicts, or a commit with an author that git refuses
  or whose date git would change, or if the replays don't have every change
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

The core program sets `status.diverged` when the
[mirror's copy diverges](#divergence) from the external repository. The
mirror resolves a divergence by the same rule as the check. It moves one
side to the other side's head only if that head keeps every change that the
moving side made, so once one side's head keeps both sides' changes, such as
after the check's push, the mirror moves the other side to it.

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
can change. Nor does it run one for a conflict in a file that's larger than 8
MiB on either side, more than the check reads to look for conflict markers.

Each commit that the check pushes makes a new head, so every check runs
again on it. A merge, and a replay of the branch's whole change as one
commit, have a `Git-K8s-Fixer: conflicts` trailer and count toward
`maxAutomatedCommits`. When the agent resolves the conflicts, the merge or
replay also has a `Git-K8s-Agent: conflicts` trailer, which makes `check-risk`
rate the branch high. A replay of one commit keeps that commit's message,
so it counts only if the original did, but the check pushes replays only
while the branch is under the limit, like any fix. When neither git nor the
agent resolves the conflicts, the check fails with the reason and leaves the
branch for a person, because a wrong resolution is worse than none.

The check [signs](#sign-commits) the commits that it pushes, like any fix.
A replay keeps the author of the commit that it replays, but git-k8s is its
committer, so a forge verifies the replay with git-k8s's key.

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
the conflicts check resolves that merge when it conflicts. `BRANCH` takes no
check results, because it has no parent, so the check reports on it with
`ResolvingDivergence` [events](#events) instead. The check waits while
`resolve/BRANCH` holds work that hasn't landed, and reports that nothing is
left to resolve once `BRANCH` contains the external repository's head, or
when the external repository's head contains `BRANCH`'s head, because the
mirror then moves `BRANCH` to it. To let the check resolve a diverged
`main`, add the check to `main`'s policy, and give `resolve/main` the parent
`main` with a rule:

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
on its head. Until either side's head keeps every change that the other
side made, the check records a `Warning` event that says which of these to
do. Then it reports that nothing is left to resolve, because the mirror
moves the other side to that head.

The check fetches from the mirror and pushes to it, as the other checks do,
and its agent Pods fetch from the mirror with tokens that are bound to them,
so the check reads no repository credentials. It reads Secrets only for the
[signing key](#sign-commits). The mirror lets a check update only a branch
that has a parent, and create none, so give the service account
`check-conflicts` in the namespace `check-conflicts` the branch-name prefix
`resolve/` when you install the core program:

```sh
go run ./cmd/git-k8s generate -registry=REGISTRY -base=cgr.dev/chainguard/git:latest -- -branch-prefix=check-conflicts/check-conflicts=resolve/ | kubectl apply -f -
```

Pass it with the core program's other flags, such as the `-branch-prefix` of
a controller that starts branches. Without the prefix, the mirror refuses to
create `resolve/BRANCH`, and the check reports `Error` for a diverged branch
without a parent. A prefix holds in every repository, so with it, the check
can fetch every repository's copy, and create, update, and delete the
branches under `resolve/` in each, as a controller that starts branches can.

To install `check-conflicts`, build the agent runner's image as for
`check-review`, and pass its digest with `-agent-image`. Without
`-agent-image`, the check resolves only what git can, and runs no agent.
Then map the check's service account to `conflicts` in the
`git-k8s-checks` ConfigMap:

```sh
go run ./cmd/check-conflicts generate -registry=REGISTRY -base=cgr.dev/chainguard/git:latest -- -agent-image="${image}" | kubectl apply -f -
kubectl -n git-k8s patch configmap git-k8s-checks --type=merge \
  -p '{"data":{"check-conflicts.check-conflicts":"conflicts"}}'
```

`check-conflicts` takes the same flags as `check-review`, and `-union`, a
comma-separated list of path patterns in the gitattributes format whose
conflicts git resolves by keeping the lines of both sides. Its agent Pods run
in their branch's namespace, as `check-review`'s do, so that namespace needs
the Secret that holds the Cursor API key, and must opt in to check Pods, as
[Install](#install) describes. The agent Pods also need the
[NetworkPolicy](#agentic-checks) that `check-review`'s need, which lets
`check-conflicts` reach them too.

### Run agents from a controller

A controller, or a check that needs a `Job` that `Run` doesn't build, runs
an agent with `Runner.RunJob`. Its `Job` names the repository, the commits
to check out, the task, the agent's tools, and the runner's image if it
isn't `-agent-image`. The mirror accepts a token that's bound to a Pod only
from a check's Pod, so a controller's `Job` names the repository's URL and
the Secret with the repository's credentials. A check's `Job` sets `Mirror`
and the URL of the check's remote instead, and the check's `Running` result
must name the run's Pod in its `pod` field, as `Run` does. `Run` builds a
`Job` from a check's branch, so both start the same Pods, within the same
`-max-pods` and `-max-runs-per-day` limits. The `Job`'s namespace must be
the namespace of the object that the controller reconciles, because
`RunJob` declares the Pod with `kube.Own`, which puts it there. The Secrets
that the Pod reads must be in that namespace too. For a check, the
`Runner`'s name must be the check's name, and that namespace must opt in to
check Pods, as [Install](#install) describes.

Call `RunJob` on each reconcile with the `JobState` that the last call
left. The state names the run's Pod and counts the runs that `RunJob`
started and didn't give back. `RunJob` changes it on each call, so store
all of it after each call with the object that the job is for, such as in
the object's status, so a controller that restarts follows the same run.
`MarshalText` encodes the state as one string, such as for one of a check's
notes, and `UnmarshalText` decodes it. `RunJob` declares the Pod
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

`agent.UsageNotes` turns what a run used into notes like `Run`'s, and
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

## Check results

Only the core program writes `status.checks`. A check sends each new result
to the core program's results endpoint:

1. The check reads the token that `generate` mounts in its Pod: a token for
   the check's service account with the audience `git-k8s-results`, which
   the kubelet renews before it expires.
2. It sends the result and the token in a `PUT` request to
   `RESULTS_URL/NAMESPACE/TRACKEDBRANCH/CHECK`. `RESULTS_URL` is the check's
   `-results-url` flag, `http://git-k8s.git-k8s.svc/results` by default. The
   request also names the `TrackedBranch` generation that the check read, and
   the core program waits until its cache has the `TrackedBranch` at that
   generation. The check's cache can get a `TrackedBranch` first, so until
   then, the core program also reads the `TrackedBranch` from the API server,
   at most once a second, to learn whether it's gone.
3. The core program verifies the token with a TokenReview for that
   audience, and rejects the result unless the `git-k8s-checks` ConfigMap
   maps the token's service account to a check, as
   [Check service accounts](#check-service-accounts) describes. If that
   check isn't `CHECK`, the core program rejects the result.
4. The core program also rejects a result for a branch without a parent, a
   result for a check that the branch's merge policy doesn't list, a result
   that isn't for the branch's current commits, a `Pending` result, a
   result without a [scope](#result-scopes) or without the fields that its
   scope needs, a result with a field that the core program doesn't know,
   and a result over its size limits. The `checks` package sends an `Error`
   result instead of one with a state or size that the core program
   rejects, with a message that says why.
5. The core program holds the result in memory and starts a reconcile of
   the `TrackedBranch`. The results controller writes the result with
   server-side apply, and the core program answers the request once its
   cache shows the result.

The core program runs one replica, because the mirror's volume has one
writer, so the replica that gets a request writes the result. If the result
isn't written within 10 seconds, the core program answers
`503 Service Unavailable` and closes the connection, and the check tries
again on a new connection. While the core program restarts, nothing answers,
and the check tries again too. The tries wait longer each time, up to 2
seconds, so 10 tries span about 11 seconds. A restart can take longer, as
[Install](#install) describes. If 10 tries fail, the check's reconcile fails,
and kube retries it, which runs the check again.

If the branch changed since the check read it, the core program answers
`409 Conflict`, and the check drops the result, because the change runs the
check again. That includes a `TrackedBranch` that was deleted and created
again. If the `TrackedBranch` was deleted, the core program answers `410 Gone`
as soon as the API server shows that, and the check drops the result. Its
reconcile succeeds, so kube doesn't run the check again. If the core
program rejects the result with `400 Bad Request`, or the token's service
account with `403 Forbidden`, the check logs why and sends nothing more for
that branch until the branch changes or the check restarts. Any other
answer, such as a `404 Not Found` from a `-results-url` with the wrong
path, fails the check's reconcile, and kube retries it.

### Result scopes

A result is for the branch's head in `commit`. Its `scope` says what else
it's for, and which other fields it has:

- `Head`: the head with any parent head. The result has neither
  `parentCommit` nor `mergeBase`.
- `Parent`: the head with the parent's head in `parentCommit`, such as
  `base`'s result. The result has no `mergeBase`.
- `Change`: what the head changes on top of the merge base in `mergeBase`,
  with any parent head, such as `risk`'s rating of the change. The result
  has no `parentCommit`, and it counts for a landing only while its merge
  base is the parent's head.

The core program and the `TrackedBranch` schema reject a result without a scope
or without the fields that its scope needs, so a missing field can't make a
result count for more commits. The `checks` package sets the scope from the
check's `UsesParent` and `SameChange`, and the verdict's `UsesParent` and
`MergeBase`. The merge controller treats a result with a scope that it
doesn't know, such as one from a later release, as `Pending`.

### Security model

The results endpoint and the `git-k8s-check-results` admission policy keep
each check's service account to its own entry in `status.checks`.
`generate` grants a program what its packages call, so a check's RBAC rules
include nothing for `trackedbranches/status`. A check needs no permission to
create its results token, because it reads the token that `generate` mounts
in its Pod. The core program writes only the entry of the check that the
token's service account runs, so one check's token can't write another
check's entry. The policy is a backstop. It rejects status writes by checks,
and changes to `status.checks` by service accounts other than the core
program's, even when a role grants them status access. See
[Install](#install).

`check-gotest` runs tests in Pods, and `check-review`, `check-conflicts`,
and `check-deps` run agents in Pods, so `generate` grants all four
permission to create, patch, and delete Pods in every namespace. The
`git-k8s-check-pods` admission policy keeps those Pods out of the `git-k8s`
and `check-*` namespaces, and makes them run as their namespace's `default`
service account. The core program doesn't map a `default` service account
to a check unless the `git-k8s-checks` ConfigMap has an entry for it, so
don't add one. Without that policy, any of them can run a Pod as another
check's service account and mount a `git-k8s-results` or `git-k8s-mirror`
token, which the core program accepts as that check's, to send its results
or to fetch and push as it. It can also run a Pod as the core program's
service account, which writes every check's result. Anyone else
who can create Pods in a check's namespace or in the `git-k8s` namespace can
do the same, because the policy covers only checks. That includes
`git-k8s-deps`, which runs update Pods, so `generate` lets it create Pods in
every namespace.

The tokens have the audience `git-k8s-results`, and the mirror's tokens
have the audience `git-k8s-mirror`. The API server accepts neither, and the
results endpoint and the mirror each accept only their own, so a token sent
to one of them can't call the API server or the other, and a token for the
API server can't send results. The endpoint uses plain HTTP inside the
cluster, so anything that can read the traffic between Pods can copy a
token and send that check's results until the token expires, within an
hour, or the check's Pod is deleted.

No check can request tokens, because `generate` mounts each check's tokens
for the mirror and the results endpoint, so a copied token stays bound to
the check's Pod. The core program can request tokens for its own service
account, to send to Octo STS, as [Security](#security) describes, but
neither endpoint treats that service account as a check.

kube doesn't fence writes, and the results controller writes all of
`status.checks` at once. The core program runs one replica, but two of its
Pods can overlap, as [Install](#install) describes, and the old Pod can put
back earlier results. Checks other than `approval` run again on an earlier
result, which is for earlier commits or isn't final, or keep it for a head
that makes the same change. If the agent's Pod is
gone, `check-review` can then run its agent again, which costs as much as a
new run. If someone removed the `approve` annotation, though, the old Pod
can put back `approval`'s `Passed` result until `check-approval` sends
`Failed` again, and the merge controller can merge the branch in that
window.

### Write a result by hand

The results endpoint accepts only checks' tokens. People who can patch
`trackedbranches/status` can write a result directly instead, for example to
unblock a branch whose check is broken:

```sh
kubectl patch trackedbranch TRACKEDBRANCH --subresource=status --type=merge \
  -p '{"status":{"checks":{"gotest":{"commit":"SHA","scope":"Head","state":"Passed","message":"passed by hand"}}}}'
```

Replace `TRACKEDBRANCH` with the name of the `TrackedBranch` object, and `SHA`
with the branch's head. Checks other than `approval` don't run again on commits
that already have a `Passed`, `Failed`, or `Fixed` result, so the result
stays until the branch moves. For a check whose result depends on the
parent, such as `base`, or that keeps results for the same change, such as
`risk`, set `scope` to `Parent` instead, `parentCommit` to the parent's
head, and `mergeBase` to `null`. A merge patch keeps the fields of the
earlier result that it doesn't set, such as the merge base of a `risk`
result, and the API server rejects a result with the scope `Parent` and a
merge base.

For a branch that lands by squash or rebase, also set `filesOnly` to `true`
if the check sets `FilesOnly`, as the built-in checks do. Otherwise the
result counts as `Pending` for the commit that the landing makes, as
[Which results count](#which-results-count) describes. A check without
`FilesOnly` runs again on a result with `filesOnly`.

The results controller writes all of `status.checks` at once, from its
cache, so a result that you write while it writes another result can be
lost. Check that your result is there afterward.

## Merge gates

`when` is a [CEL](https://cel.dev) expression. It has one variable,
`checks`, which maps each check that the policy lists to an object with
`passed` (bool), `state` (string), and `outputs` (map of strings). A check
without a result for the branch's current commits has state `Pending`. All of
CEL works, for example `int(checks.risk.outputs.lines) < 500` or
`checks.all(c, checks[c].passed)`. In CEL, `&&` and `||` give a result when
one side decides it, even if the other side is an error, such as a missing
output. Without `when`, every listed check must pass.

The repositories controller compiles each `when` when it reads the
`TrackedRepository`, so a syntax error, a misspelled field such as
`checks.gofmt.pased`, or a check that the policy doesn't list, such as
`checks.gofmy.passed`, makes the `TrackedRepository` not `Ready`, with the
reason `InvalidMergePolicy`, instead of holding branches back later. For a check
whose name has a hyphen, write `checks["go-vet"].passed`, because CEL reads
`checks.go-vet` as a subtraction. Each evaluation can cost at most 100,000,
which stops an expression that loops over the checks many times.

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
   on the new head, except that checks with `SameChange`, such as `risk`,
   keep their results when the merge makes the same change, and an approval
   still holds, as [Which results count](#which-results-count) describes. A
   branch that already contains the parent skips this step.
3. When the gate passes for the new head, the merge controller lands the
   branch, as [Landing methods](#landing-methods) describes, and the next
   branch moves to the front. When a squash or rebase landing first pushes
   its commit to the branch for the checks, as
   [Which results count](#which-results-count) describes, the branch stays
   at the front while they run on it.

The branches behind the front keep their heads, so each landing runs the
checks again on one branch, and only the checks that set `UsesParent`, such
as `base`, on the others. The parent's `status.queue` lists its
queue, front first. Each queued branch's `status.queued` records when it
joined, the head that the merge controller last kept in the queue, and its
place, from 1 at the front, which the `QUEUE` column shows. A queued
branch's state is `Queued`, and the `Landed` condition's message says what
it waits for, such as `2 of 3 in main's queue`.

A branch leaves the queue when one of these happens:

- It lands.
- Someone pushes a commit without a `Git-K8s-Fixer` trailer to it, or
  pushes a head that doesn't contain the one before. Fix commits keep the
  branch's place, including the `base` check's merge of the parent. The
  merge controller trusts the trailer, so a person who adds it to a commit
  keeps the branch's place, but the checks still run on the new head.
- It changes both in the mirror and in the external repository, so it
  [diverges](#divergence).
- Its checks finish without its gate passing, such as a test that fails
  after the merge of the parent. At the front, it leaves sooner, as soon
  as the `base` check fails or the gate fails with its unfinished checks
  counted as passing.
- A squash or rebase landing sets its state to `NeedsRebase`, as
  [Landing methods](#landing-methods) describes. The branch doesn't join
  again until its head or its parent's head changes.
- Someone deletes the branch, which deletes its `TrackedBranch`.
- Its parent goes away, or the parent's merge policy goes away or can't be
  evaluated.

A branch that leaves joins at the back when its gate passes again. A
reconcile that fails, such as one in which the mirror can't read its copy
of the repository, doesn't take a branch out of the queue. The branch keeps
its place while kube tries the reconcile again.

Three choices shape the queue:

- **Where the queue lives.** The queue is in `TrackedBranch` status, so it
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
repositories controller listed. If the parent moved after that, the check
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
`-identity-email` flags change, and [signs](#sign-commits) the commits if
the `TrackedRepository` names a signing key. It takes commit times from the
commits that it copies, so making the same landing again makes the same
commits.

When the branch is one commit on top of the parent's head, a squash
fast-forwards the parent to it. A rebase does the same for a branch with no
merge commits after the parent's head, because copying its commits changes
nothing. When the parent already has the files at the branch's head, a squash
sets the branch's state to `NothingToLand` and changes nothing. A rebase does
that only when the parent already has every commit's change, because it
leaves out each commit that changes nothing.

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
`check-risk` compares them with the parent's head. `check-approval` compares
only files, and an approval is for the change, which the new commit makes
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
dropped the trailers, `check-risk` would rate the squashed commit `low` when
it rates it again, so the commit wouldn't need an approval, and the parent's
history wouldn't show which changes came from agents. Dropping `FilesOnly`
wouldn't fix that, because the check would read the same squashed message.

Some results also hold for heads that the check didn't see. A check with
`SameChange` in its `checks.Check`, such as `check-risk`, rates the branch's
change: what its head changes on top of its merge base with the parent's
head. Its `Passed` and `Failed` results name that merge base in `mergeBase`.
When the parent or the head moves, and the head still makes the same change,
the framework keeps the result without running the check. `check-approval`
compares an approved commit's change with the head's the same way. A head
makes the same change as an earlier head when both of these are true:

- Merging the earlier head into the new head's merge base, with the earlier
  head's merge base as the base, is clean and gives the new head's files.
- The new head changes no file that the earlier head doesn't, and leaves each
  file that it changes with the mode that the earlier head leaves it with.

So a clean merge of the parent, such as `check-base`'s at the front of the
[merge queue](#merge-queue), a rebase or a squash that doesn't resolve a
conflict, and the commit that a squash or rebase landing makes all make the
same change as the head before them. A commit that adds, removes, or changes
code doesn't, and neither does a merge that resolves a conflict.

The comparison is conservative: when it can't tell, the changes differ. They
differ for any of these:

- A head with no merge base with the parent's head, or with more than one.
- A merge that conflicts, such as when the parent and the branch both change
  a binary file or a submodule.
- A change to a file that the parent renamed, or whose mode the parent
  changed, since the earlier head's merge base.
- A change whose list of files takes more than 8 MiB.

The merge ignores `.gitattributes` files, as `check-base`'s does, so a branch
can't make a conflicting merge clean. A comparison runs at most five git
commands, however many commits the heads have. Each check's program
remembers the merge bases and answers that it computes, up to 4,096 of each,
and starts over when it has that many.

A result that names a merge base counts for landing only while that merge
base is the parent's head. A branch lands only when it contains the parent's
head, so the files that land are then the parent's files with the change
that the result is for. A verdict that also depends on files outside the
change, such as `check-risk`'s rating of a change to a `go.mod` file, which
compares the file with every `go.mod` file at the merge base, names the
parent's head in `parentCommit` instead, so it holds only for that head.

When the counted results pass the gate, the controller lands the new commit
without another round of checks. It moves the parent to the commit in the
mirror's copy, if the parent is still at the head that the checks saw. The
same atomic update deletes the branch, if the branch is still at its head,
or moves the branch to the new commit when `deleteLandedBranches` is off. A
branch that stays is then at its parent's head, so it stays `Landed` instead
of showing commits that the parent doesn't have. If the parent or the branch
moved since the repositories controller listed them, the update changes
neither, and the controller tries again.

When the gate doesn't pass on the counted results alone, the controller
moves the branch to the new commit in the mirror's copy instead, if the
branch is still at its head, and sets the branch's state to `Rewritten`.
The checks run on the new commit, and when the gate passes, the parent
fast-forwards to it. In a [merge queue](#merge-queue), the branch keeps its
place at the front until then. An approval of the branch's head that names
its full SHA holds for the new commit, which makes the same change.

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
`TrackedRepository`'s `ExternalSynced` condition is then `False` with the reason
`SyncFailed` and a message such as
`the external repository refused updates to c/auth ([remote rejected] (deletion prohibited); remote: error: denying ref deletion for refs/heads/c/auth)`,
which ends with the messages that the external repository sent, and the
mirror tries again at each poll. A rewritten branch that the
external repository refused still lands. If the merge policy deletes landed
branches, the mirror then deletes the branch in the external repository,
unless the external repository refuses that too. To clear the condition,
let the external repository accept the update, such as by allowing force
pushes to and deletions of proposal branches.

## Sign commits

`check-base`, `check-gofmt`, `check-review`, `check-conflicts`, and
`check-deps` make commits: merges of a parent into a branch, formatting
fixes, agents' fixes, and the commits that resolve conflicts and
divergences. The merge controller makes the commits of
[squash and rebase landings](#landing-methods), including those that it
moves the branch to for another round of checks. A fast-forward landing
makes none, because it moves the parent to a commit that's already on the
branch. `git-k8s-deps` makes the commits of
[dependency updates](#dependency-updates). To sign these commits, make an
SSH key for signing only, put it in its own Secret in the `TrackedRepository`'s
namespace, and name the Secret in the `TrackedRepository`:

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

git-k8s signs with git's SSH signature format, `gpg.format=ssh`. Git runs
`ssh-keygen` to sign, so the images of `git-k8s`, `check-base`,
`check-gofmt`, `check-review`, `check-conflicts`, `check-deps`, and
`git-k8s-deps` need it, and the `cgr.dev/chainguard/git` image that
[Install](#install) and
[Install the dependency controller](#install-the-dependency-controller) use
has it. The key must be unencrypted, in the OpenSSH format that `ssh-keygen`
writes. Ed25519 and RSA signatures come out the same every time, so a check
still makes the same fix commit from the same inputs, a landing makes the
same commits, and an update of the same parent head makes the same commit;
ECDSA signatures don't. Without `signingKeyRef`, these commits aren't
signed.

git-k8s doesn't support keyless signing with
[gitsign](https://github.com/sigstore/gitsign), which signs with a
short-lived certificate from Sigstore for an OIDC identity, such as a
service account token, instead of a long-lived key, because:

- GitHub doesn't show gitsign signatures as verified, so a rule that
  requires signed commits rejects them.
- The public Sigstore service accepts tokens only from OIDC issuers that it
  knows, such as GKE and EKS clusters. Other clusters, including the kind
  cluster that the end-to-end test uses, need Sigstore services of their
  own.
- Signatures from gitsign differ every time, as ECDSA signatures do, so
  each retry of a fix makes a different commit.

[Future work](future-work.md#sign-commits-with-gitsign) lists what
supporting it needs.

The key needs a Secret of its own, because the `secretRef` Secret holds the
external repository's credentials, which only the core program and the
`prepare` containers of `git-k8s-deps`'s update Pods use. The programs that
sign read the whole signing Secret, so with a Secret of its own, the checks
and `git-k8s-deps` never hold the credentials. A check or a landing reports
an error instead of signing if `signingKeyRef` names the `secretRef` Secret,
and `git-k8s-deps` logs the error instead of pushing the update.

Only the core `git-k8s` program, `check-base`, `check-gofmt`, `check-review`,
`check-conflicts`, `check-deps`, and `git-k8s-deps` read the signing Secret,
through the `signing` package, which no other program links. The checks read
it only to sign a commit that their policy lets them push, the merge
controller only when a squash or rebase landing makes commits, and
`git-k8s-deps` only when it commits an update. `check-review`,
`check-conflicts`, and `check-deps` commit their agents' changes in their own
processes, and `git-k8s-deps` commits what its update Pods made in its own
process, so agent Pods and update Pods never get the key.

`generate` lets each program that reads a Secret get every Secret in the
namespaces that it watches, which is every namespace unless you pass
`-watch-namespace`. The checks and `git-k8s-deps` reach repositories through
the mirror and read no other Secret, so signing is what lets `check-base`,
`check-gofmt`, `check-review`, `check-conflicts`, `check-deps`, and
`git-k8s-deps` read Secrets, including the `secretRef` Secrets. A
compromised program that signs can read an external repository's
credentials, and push to the external repository without the mirror.
[Sign commits in the mirror](future-work.md#sign-commits-in-the-mirror)
describes how to take that away. Other programs don't read the key, but
`check-gotest` can create Pods, and a Pod can mount any Secret in its
namespace. `check-gotest` doesn't give its test Pods the signing Secret,
and the [admission policies](#install) let it create Pods only in
namespaces that opt in to check Pods.

For each commit, the program that signs it writes the key to a file with
mode 0600 in a new directory with mode 0700 under `/tmp`, passes git the
file's path, and removes the directory when the commit is done. `/tmp` is
an `emptyDir` volume on the node's disk that outlives the container, so a
program that's killed while it signs leaves the key there until the program
restarts and removes it, or until the Pod is deleted. The key never appears
in a command's arguments or environment, in a log, or in an error.

### Set up the forge

A forge shows a commit as verified when the key that signed it belongs to
the commit's committer. On GitHub:

1. As the account that git-k8s commits as, such as a bot account, go to
   **Settings** > **SSH and GPG keys** > **New SSH key**, set **Key type**
   to **Signing Key**, and add `git-k8s-signing.pub`. Or run
   `gh ssh-key add git-k8s-signing.pub --type signing` as that account.
2. Set the `-identity-email` flag of `git-k8s`, `check-base`, `check-gofmt`,
   `check-review`, `check-conflicts`, `check-deps`, and `git-k8s-deps` to an
   email address that the account has verified, such as its
   `ID+USERNAME@users.noreply.github.com` address, and set the
   `-check-identity-email` flag of `git-k8s-deps` to the same address.
   GitHub marks a commit **Verified** only when its committer email belongs
   to the account that has the key. To pass a flag, add it after `--` in the
   `generate` command, as in [Install](#install).

A GitHub App can't have a signing key. GitHub signs the commits that an App
makes through its API, but git-k8s makes commits with git, so it signs them
with an account's key even when it pushes with an App's token. GitHub
verifies a signature no matter which credential pushed the commit.

### Protected branches

Checks push their commits to the branch that they check in the mirror's
copy. When a branch lands, the merge controller moves the parent there, and
can delete the branch or, in a squash or rebase landing, replace its
commits. `git-k8s-deps` pushes and deletes the branches under its prefix
there. The mirror then pushes each change to GitHub, as the account that
the `secretRef` Secret's credentials belong to, or as Octo STS's GitHub App
for a repository that [gets tokens from Octo STS](#github-repositories).
GitHub's branch protection rules and rulesets apply to the mirror's pushes:

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
  branch. The checks can include git-k8s's own [check runs](#check-runs).
  git-k8s doesn't wait for those to show a branch's results before it lands
  the branch, so GitHub can refuse a landing at first, and git-k8s retries it.
- **Require signed commits** refuses a landing unless GitHub verifies the
  signature of every commit that it adds to the parent. That includes
  people's commits, which even a squash or rebase landing adds as they are
  when it has nothing to change, so people have to sign with a key on their
  GitHub account and use a committer email that the account has verified.
- **Require linear history** rejects the merge commits that `check-base`
  and `check-conflicts` make. Leave it off for a parent whose merge policy
  lets `base` or `conflicts` push and lands branches by `FastForward`, the
  default. `Squash` and `Rebase` landings add no merge commits to the
  parent.
- **Block force pushes** affects git-k8s only on branches that land by
  `Squash` or `Rebase`, where it stops the mirror from replacing their
  commits in GitHub, as [Landing methods](#landing-methods) describes.
  git-k8s only fast-forwards parents, and checks add commits on top of the
  branches that they check.
- **Restrict deletions** on a branch keeps it in GitHub after
  `deleteLandedBranches` deletes it in the mirror's copy.

When GitHub refuses the mirror's push of a check's commit, a landing, or a
branch from `git-k8s-deps`, the change stays in the mirror's copy, and the
reason that GitHub gives shows up on the `TrackedRepository`. Its
`ExternalSynced` condition is `False` with the reason `SyncFailed`, and its
message names each branch that GitHub refused and ends with GitHub's
messages, which name the rule. The mirror tries again at each poll, as
[Landing methods](#landing-methods) describes for branches that the
external repository won't delete or rewrite.

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
`Git-K8s-Deps: go MODULE VERSION` trailer, and the controller
[signs](#sign-commits) it when the repository has a `signingKeyRef`. The
same update of the same parent head always makes the same commit, unless an
ECDSA key signs it.

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

The controller skips a `go.mod` file that's larger than 8 MiB, and logs a
warning. When the parent's list of files from `git ls-tree` is larger than
16 MiB, about 150,000 files, the controller changes nothing for the parent
until its head moves. It remakes a branch whose head has a `go.mod` file or
a list of files larger than these limits.

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
and can edit files. The check [signs](#sign-commits) and pushes what the
agent changed as a fix with `Git-K8s-Fixer: deps` and `Git-K8s-Agent: deps`
trailers, and `check-gotest` tests the new head.

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

- The `prepare` init container fetches the parent's head from the external
  repository with the repository's credentials. It's the only container that
  gets them.
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
the controller has its result. A deleted Pod counts until the kubelet stops
its containers. Update Pods set a termination grace period of 2 seconds,
the kubelet's minimum, instead of the default 30, because a container's
first process ignores `SIGTERM` unless it handles the signal, as the shells
in the `prepare` and `update` containers don't. When an update fails, the
controller logs why and tries again after `-interval`. An update also fails
when an image's name isn't valid, when kube still can't schedule the update
Pod 5 minutes after creating it, and when a Secret is still missing or an
image still can't be pulled 5 minutes after the container can start.

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

The controller reads the parent's head from the mirror and pushes its
branches there, so the core program must give its service account the
controller's prefix, as [The mirror](#the-mirror) describes. The controller
also refuses to push branches outside the prefix. It reads Secrets only to
sign its commits, and `config/policy.yaml` stops it from approving or
changing `TrackedBranch` objects.

The mirror accepts a token that's bound to a Pod only from a check's Pod, so
the `prepare` container fetches the parent from the external repository
instead. When the parent moves, the mirror pushes it to the external
repository soon after, but an update Pod can start in between. Then the
`prepare` container finds the parent at another commit and exits with
status 3. The first time that happens on a parent's head, the controller
tries those updates again after a minute, or after `-interval` if that's
shorter. After that, they wait for `-interval`, or until the parent moves.
[Let update Pods fetch from the mirror](future-work.md#let-update-pods-fetch-from-the-mirror)
proposes a fix.

### Install the dependency controller

To install `git-k8s-deps` and `check-deps`, build and push the agent runner's
image. In each namespace with dependency branches, create the
`cursor-api-key` Secret and opt the namespace in to check Pods, as
[Agentic checks](#agentic-checks) describes. `git-k8s-deps` runs its result
containers from that image, and `check-deps` runs agents in it. Then map
`check-deps`'s service account to `deps` in the `git-k8s-checks` ConfigMap:

```sh
go run ./cmd/git-k8s-deps generate -registry=REGISTRY -base=cgr.dev/chainguard/git:latest -- -result-image="${image}" | kubectl apply -f -
go run ./cmd/check-deps generate -registry=REGISTRY -base=cgr.dev/chainguard/git:latest -- -agent-image="${image}" | kubectl apply -f -
kubectl -n git-k8s patch configmap git-k8s-checks --type=merge \
  -p '{"data":{"check-deps.check-deps":"deps"}}'
```

Pass the core program `-branch-prefix=git-k8s-deps/git-k8s-deps=deps/`, with
the controller's namespace, service account, and `-prefix`. The mirror
refuses the controller until the core program gives its service account the
prefix, as [The mirror](#the-mirror) describes.

Upgrade the core program first, because it installs `config/policy.yaml`
when it starts, and the second policy there stops `git-k8s-deps` from
changing `TrackedBranch` objects. With `-install-policies=false`, apply
`config/policy.yaml` instead. The policy recognizes `git-k8s-deps` as the
service account `git-k8s-deps` in the namespace `git-k8s-deps`, where
`generate` installs it unless you set `-namespace`. For another service
account, add an entry with an empty value for it to the `git-k8s-checks`
ConfigMap, as [Check service accounts](#check-service-accounts) describes.
The policy then treats the service account as a check, which can't change
`TrackedBranch` objects.

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
| `-go-image` | `cgr.dev/chainguard/go` by digest | Image that runs `go get`; it needs `go`, `git`, `sh`, `base64`, `sha256sum`, `tail`, and `cut` |
| `-git-image` | `cgr.dev/chainguard/git` by digest | Image that fetches the source; it needs `git` and `sh` |
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
that has git 2.43 or later. Then wait for the core program to create the
`git-k8s-checks` ConfigMap, and map each check's service account to its
check there, as [Check service accounts](#check-service-accounts) describes:

```sh
for program in git-k8s check-base check-gofmt check-risk check-approval check-gotest; do
  go run "./cmd/${program}" generate -registry=REGISTRY -base=cgr.dev/chainguard/git:latest | kubectl apply -f -
done
kubectl -n git-k8s wait --for=create configmap/git-k8s-checks --timeout=5m
kubectl -n git-k8s patch configmap git-k8s-checks --type=merge -p '
data:
  check-base.check-base: base
  check-gofmt.check-gofmt: gofmt
  check-risk.check-risk: risk
  check-approval.check-approval: approval
  check-gotest.check-gotest: gotest
'
```

Replace `REGISTRY` with a registry and repository prefix that your cluster
can pull from, such as `ghcr.io/you`. To pass flags to a program, add them
after `--`, as in this command for `check-risk`:

```sh
go run ./cmd/check-risk generate -registry=REGISTRY -base=cgr.dev/chainguard/git:latest -- -sensitive='auth/**' | kubectl apply -f -
```

To give test Pods a module proxy and a shared build cache, also install
`go-cache`. [Share modules and build outputs](#share-modules-and-build-outputs)
shows how.

To upgrade, install the core program, `git-k8s`, before the checks, as this
loop does. The core program updates the `TrackedBranch` CustomResourceDefinition
when it starts, and an older one rejects results with fields that it doesn't
know, which newer checks can send. A check sends nothing more for a branch
after a rejected result until the branch changes or the check restarts, so
the branch waits for that check until then.

To upgrade an installation from before the mirror, follow
[Upgrade from before the mirror](#upgrade-from-before-the-mirror) instead.

`check-gotest`, `git-k8s-deps`, and the [agentic checks](#agentic-checks)
fetch the source in their Pods with the image in `-git-image`, and
`check-gotest` and `git-k8s-deps` run Go with the one in `-go-image`. By
default, those flags name Chainguard's `git` and `go` images by digest, so
moving a tag, on the registry or on a mirror between it and your cluster,
can't change what those Pods run. With `-go-cache`, `check-gotest`'s Pods
fetch the source with `check-gotest`'s own image instead, which `generate`
names by digest.

`-git-image`, `-go-image`, `-agent-image`, and `-result-image` are kube
image flags. If you set one to an image by tag, `generate` resolves the tag
with your registry credentials, and writes the image by digest into the
Deployment's arguments. A program that starts with a tag in one of those
flags resolves it before it starts its controllers, or exits if it can't.
So the Pods name every image by digest. Each container has the pull policy
`IfNotPresent`, and a node pulls each image once. Pass digests where you
can, so that nothing has to resolve a tag. To run newer images, upgrade the
programs, or set the flags. For how kube resolves tags, see
[Name images by digest](../kube/README.md#name-images-by-digest) in kube's
README.

The core program keeps the mirror's copies on a PersistentVolumeClaim that
`generate` adds for its `kube.Volume`, at
`/var/lib/git-k8s/NAMESPACE/NAME.git`. The claim asks for 1 GiB of the
cluster's default StorageClass unless you pass `-volume-size` or
`-storage-class` to `generate`. A volume has one writer, so the core program
runs one replica without leader election, and a rollout stops the old Pod
before it starts the new one. While the Pod restarts, the mirror, the
results endpoint, and the controllers are down, and checks retry. For more about volumes, see
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
locks until it's gone. A git command that runs past its timeout, or whose
request ends, gets `SIGTERM` and removes its own locks. Before each sync,
the mirror removes the copy's lock files that are older than the longest
that a git command can take, plus a minute in case the volume's clock
differs from the node's: 6 minutes and 10 seconds with the default
`-git-timeout`. Maintenance holds the locks under `objects/` for as long as
it runs, so the mirror removes those only once they're older than the
longest that maintenance can take, plus a minute: 1 hour, 1 minute, and 10
seconds with the default `-maintenance-timeout`. A newer lock might belong
to the other Pod. Until the mirror removes a lock, a sync or a
landing that needs the locked ref fails and tries again later. The
`TrackedRepository`'s `ExternalSynced` condition names the lock, for example
with the reason `UpdateFailed` when the sync couldn't update a branch in the
copy, or `SyncFailed` when the fetch couldn't record the external
repository's head.

Git packs a copy's objects in its maintenance. A fetch or a push would
start maintenance in the background, where git's timeout doesn't apply, so
the mirror turns that off and runs maintenance itself after each sync, when
git says the copy needs it. It maintains one copy at a time, beside the
copy's syncs, fetches, and pushes, which don't wait for it. Deleting a
copy, replacing it, or switching it to a new URL stops its maintenance, and
so does stopping the core program, which waits for git to exit. Maintenance
that runs past the core program's `-maintenance-timeout`, 1 hour by
default, gets `SIGTERM`, and so does the repack that it started. After
maintenance fails or times out, the mirror logs why and skips that copy's
maintenance for 6 hours, so a copy whose repack takes longer than the
timeout isn't repacked until you raise it. Maintenance that
gets `SIGKILL` instead, as when the Pod's grace period runs out, leaves
`objects/maintenance.lock`, which makes later maintenance skip the copy
without an error, so the mirror removes that lock once it's stale, like the
others.

The checks keep local copies of repositories in `/tmp/git-k8s`, on the
`emptyDir` volume that `generate` mounts at `/tmp`, and so does
`git-k8s-deps`. Like the mirror, they turn off the maintenance that a fetch
would start. Instead, at most once an hour for each copy, the reconcile that
opens the copy deletes the refs that the copy no longer needs, such as those
of deleted branches, and then runs maintenance if git says that the copy
needs it. The reconcile logs any failure and goes on. The program removes a
copy that no reconcile has opened for a week, such as the copy for a
`TrackedRepository` that no longer exists.

`generate` also writes a Service for the core program, which routes port 80
to port 8081 of its Pod, where one handler serves both the mirror and the
results endpoint. It mounts a token for the audience `git-k8s-results` in
each check's Pod, and a token for `git-k8s-mirror` in the Pod of each
program that fetches from the mirror. `git-k8s-deps` gets a results token
too, because it imports the `checks` package. It doesn't send results, and
the core program wouldn't accept them, because `git-k8s-deps` isn't a check.
If NetworkPolicies in the `git-k8s` namespace deny traffic by default, let
the Pods of the checks and `git-k8s-deps`, and the checks' test and agent
Pods, reach port 8081 of the core program's Pod.

`config/policy.yaml` holds four ValidatingAdmissionPolicies, which need
Kubernetes 1.30 or later. The first rejects every write to `TrackedBranch`
status by a check's service account, and every change to `status.checks` or
`status.diverged` by a service account other than the core program's.
`status.diverged` names the commit that `check-conflicts` merges or replays.
Checks have no RBAC rule to write status, so this policy is a backstop for a
role that grants one by mistake. It treats a service account as a check when
the `git-k8s-checks` ConfigMap has an entry for it, as
[Check service accounts](#check-service-accounts) describes, and when it's
`check-NAME` in the namespace `check-NAME`, even without an entry. The second
stops every git-k8s service account from setting the `approve` and
`approved-by` annotations, which are for people, and stops checks and
`git-k8s-deps` from changing a `TrackedBranch` object's spec, labels,
annotations, finalizers, owner references, or `managedFields`. A finalizer
that nobody removes would keep a deleted branch in its parent's merge
queue, and an owner reference to a missing object would make garbage
collection delete the `TrackedBranch` with its approval. The core program
writes status with server-side apply. When it stops setting a field, the
API server removes the field only if the core program's entry in
`managedFields` lists it. Without those entries, a branch that leaves the
merge queue would keep its place, and at the front of the queue it would
block every other branch. RBAC also keeps
every check except `check-gotest`, `check-review`, `check-deps`, and
`check-conflicts`, which own Pods, from patching `TrackedBranch` objects.
`generate` grants that permission to a program that owns objects, such as
these checks and `git-k8s-deps`, because it can't tell whether an owned
object needs a finalizer on its owner. The second policy denies the
annotation that kube adds with that finalizer, so these programs can own
only namespaced objects in the branch's namespace. The second policy also
lets only the core program create a `TrackedBranch` or change its spec, which
the core program copies from the `TrackedRepository`. The spec holds the
parent's merge policy, so anyone else who could change it, such as an
approver who can patch a `TrackedBranch`, could land the branch without its
checks. People can still label and annotate `TrackedBranch` objects. To change
a merge policy, change the `TrackedRepository`. The first two policies
identify the core program and the checks by the service accounts that
`generate` installs them with: `git-k8s` in the namespace `git-k8s`, and
`check-NAME` in the namespace `check-NAME`. The second identifies
`git-k8s-deps` the same way, as `git-k8s-deps` in the namespace
`git-k8s-deps`.

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
trusts. The mirror checks both for every check's Pods, such as
`check-gotest`'s test Pods and `check-review`'s agent Pods, as
[Who can fetch and push](#who-can-fetch-and-push) describes.

The fourth checks who approves, as [Approve a branch](#approve-a-branch)
describes.

Without the policies, most of that doesn't hold, so the repositories
controller sets a `PoliciesInstalled` condition on each `TrackedRepository`.
It's `False` until all four policies are installed with bindings that deny.

Each namespace that holds a `TrackedRepository` whose merge policy lists
`gotest`, `review`, or `deps`, or lists `conflicts` with `mayPush: true`
while `check-conflicts` runs with `-agent-image`, must opt in to check Pods
and enforce the
`restricted` Pod Security Standard, or the third policy denies the check's
Pods:

```sh
kubectl label namespace NAMESPACE git-k8s.imjasonh.com/check-pods=true pod-security.kubernetes.io/enforce=restricted
```

Replace `NAMESPACE` with the namespace of the `TrackedRepository`. The namespace
can't be `git-k8s` or start with `check-`. If it has the label
`pod-security.kubernetes.io/enforce-version`, the label's value must be
`latest`. Until it has both labels, the branch's `gotest`, `review`, or
`conflicts` result, or a `deps` result that runs an agent, stays `Running`,
and its message says why kube couldn't create the Pod. kube tries again with
backoff that grows to 5 minutes, plus up to 10% jitter, so it creates the Pod
within about 5.5 minutes after you label the namespace, without a new push.

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
and its message says to restart the core program, which installs
`config/policy.yaml` again when it starts. Restart the Deployment:

```sh
kubectl -n git-k8s rollout restart deployment/git-k8s
```

`PoliciesInstalled` also turns `False` while a policy's
`git-k8s.imjasonh.com/policy-version` annotation isn't the version that the
core program expects. If the annotation is missing, isn't a number, or is an
earlier version, as with the policies of an earlier release, the reason is
`Outdated`, and the message says to restart the core program, which installs
the policies from its release. If it's a later version, as with the policies
of a later release, the reason is `Newer`, and the message says to upgrade
the core program or, if you rolled it back, to restart it. The core program
can't tell a rollback from an upgrade that applies the policies first.

`PoliciesInstalled` also turns `False` when no binding for a policy denies
every request that the policy rejects. A binding can let some of them
through when its `validationActions` doesn't hold `Deny`, when its
`matchResources` sets resource rules, or when a selector in its
`matchResources` sets `matchLabels` or `matchExpressions`. If a binding's
policy reads parameters, as the first two do, the binding also lets some
through when its `paramRef.parameterNotFoundAction` isn't `Deny`, when it
has no `paramRef`, or when its `paramRef` doesn't name the `git-k8s-checks`
ConfigMap in the `git-k8s` namespace. Without a `paramRef`, the API server
evaluates the policy without parameters, and with a `paramRef` to another
ConfigMap, it evaluates the policy with that ConfigMap. Either way, the
policy ignores the entries in the `git-k8s-checks` ConfigMap. The API
server ignores the `paramRef` of a binding whose policy doesn't read
parameters, such as the third and fourth policies, so the condition does
too. The message gives a `kubectl patch` command that makes the binding
from `config/policy.yaml` deny all of them again, without a restart. For a
binding that someone set to `Warn`, the command is:

```sh
kubectl patch validatingadmissionpolicybinding git-k8s-branches --type=merge \
  -p '{"spec":{"validationActions":["Deny"]}}'
```

A binding set to `Warn` stops the core program the next time that it
starts, whether you restart it or a node drain or an upgrade does. The core
program's apply keeps the entries that others add to a binding's
`validationActions`, so it adds `Deny` next to `Warn`, and the API server
rejects a binding that has both. The core program exits, and exits again
each time that it restarts, so the mirror is down and nothing lands until
you patch or delete the binding. `PoliciesInstalled` reports a binding from
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
name as their parameter, and which the results endpoint and the mirror
read. The API server lets only someone who can read every ConfigMap create
a policy whose parameter is a ConfigMap, and it checks that as `get` on a
ConfigMap named `*`. No ConfigMap can have that name, so `generate` also
grants `get` on the name `*`, and the core program still can't read any
other ConfigMap.

The core program can't create other admission policies, but a compromised
core program could rewrite these policies, their bindings, and the
`git-k8s-checks` ConfigMap, to weaken them or to deny other requests in the
cluster. It already decides what lands, so it could land a branch without
its checks anyway. To keep the policies out of its reach, for example in a
cluster that manages admission policies separately, install it with
`-install-policies=false`, which also leaves out the permissions except
`get` on the `git-k8s-checks` ConfigMap, and apply `config/policy.yaml`
yourself:

```sh
go run ./cmd/git-k8s generate -registry=REGISTRY -base=cgr.dev/chainguard/git:latest -- -install-policies=false |
  kubectl apply -f -
kubectl apply -f config/policy.yaml
```

With `-install-policies=false`, the message of a `False` `PoliciesInstalled`
says to apply `config/policy.yaml` instead of restarting the core program.
For a policy from another release, it says to apply `config/policy.yaml`
from the core program's release. The core program doesn't apply the
manifest when it starts, so a binding set to `Warn` doesn't stop it, and the
condition doesn't report one while another binding for the same policy
denies.

### Check service accounts

The results endpoint and the [mirror](#the-mirror) treat a service account
as a check only when the `git-k8s-checks` ConfigMap in the `git-k8s`
namespace has an entry for it. Each key is `NAMESPACE.SERVICE_ACCOUNT`, and
its value is the check's name. A service account's name doesn't make it a
check, because anyone who can create namespaces and service accounts can
choose their names. `generate` installs `check-NAME` with the service
account `check-NAME` in the namespace `check-NAME`, so [Install](#install)
adds entries such as `check-gofmt.check-gofmt: gofmt`.

To install checks in a shared namespace, create the namespace first. Then
install each check with `generate -namespace=checks`, and add its entry:

```sh
kubectl create namespace checks
go run ./cmd/check-approval generate -registry=REGISTRY -base=cgr.dev/chainguard/git:latest -namespace=checks | kubectl apply -f -
kubectl -n git-k8s patch configmap git-k8s-checks --type=merge \
  -p '{"data":{"checks.check-approval":"approval"}}'
```

An entry with an empty value says that the service account isn't a check,
so it can't send results, or fetch from the mirror or push to it as a
check. The first two policies treat a service account with an entry as a
check even when the value is empty, and `check-NAME` in the namespace
`check-NAME` as a check even without an entry. That only limits those
service accounts: they can't change a `TrackedBranch` or its status even if
RBAC lets them patch them. The endpoint, the mirror, and
the policies ignore an entry for the core program's service account,
`git-k8s.git-k8s`, so an entry can't make the core program a check, or stop
it from writing results or changing `TrackedBranch` objects. Don't add an entry
for a namespace's `default` service account, because the checks that own
Pods run their Pods as that service account, as
[Security model](#security-model) describes. The core program applies the
ConfigMap without data, so restarting it keeps your entries.
Anyone who can change ConfigMaps in the `git-k8s` namespace can decide which
service accounts send which results, and which ones fetch and push as which
checks, so give that permission only to people who can install checks.

The results endpoint and the mirror read the ConfigMap at most once every 5
seconds while reads succeed, so a change to an entry, such as emptying it,
takes effect for them within 5 seconds. While reads fail, they use the
entries from the last read that succeeded for up to 30 seconds after it.
After that, the mirror answers `503 Service Unavailable` and the results
endpoint answers `500 Internal Server Error` until a read succeeds.

The third policy doesn't read the ConfigMap, so an entry doesn't change
which Pods a check can write. A check that owns Pods and runs as another
service account needs a policy of its own. The core program's
`-branch-prefix` names service accounts too, so a check such as
`check-conflicts` that runs as another service account needs that flag to
name its service account.

While the ConfigMap is missing, the API server denies every create and update
of a `TrackedBranch` or its status, including people's, with a message that says
`no params found for policy binding`, and the results endpoint and the
mirror treat no service account as a check. To create the ConfigMap again,
run `kubectl -n git-k8s create configmap git-k8s-checks`, or restart the
core program with `kubectl -n git-k8s rollout restart deployment/git-k8s`.
With `-install-policies=false`, apply `config/policy.yaml` instead. Then add
the entries again.

### Upgrade from before the mirror

To upgrade an installation from before the mirror, follow these steps in
order:

1. Grant the people who approve branches the `approve` verb. From step 3
   on, the `git-k8s-approvals` policy rejects approvals without it, and a
   new approval must set `approved-by` too, as
   [Approve a branch](#approve-a-branch) describes.
2. If `check-gotest`, `check-review`, `check-deps`, or `check-conflicts`
   runs, label the namespaces of its repositories as [Install](#install)
   describes. From step 3 on, the `git-k8s-check-pods` policy denies the
   check's Pods in a namespace without the labels.
3. Apply `config/policy.yaml`. If your checks write their own results to
   `TrackedBranch` status, as each did before the results endpoint, the policy
   rejects those writes, so branches get no new results until step 5.
4. Install the core program with `kubectl apply`, as the loop in
   [Install](#install) does, because server-side apply can't switch its
   Deployment to the `Recreate` strategy. `kubectl apply` replaces the rules
   of the core program's Role in the `git-k8s` namespace, which drops the
   rules for leader election and keeps the ones for the `git-k8s-checks`
   ConfigMap and the core program's own tokens, so keep the Role and its
   RoleBinding. Then delete the PodDisruptionBudget that the core program
   needed for two replicas:

   ```sh
   kubectl -n git-k8s delete --ignore-not-found poddisruptionbudget git-k8s
   ```

   On a cluster that enforces NetworkPolicies, the core program's
   NetworkPolicy then limits what test Pods can reach, as
   [Sandboxed checks](#sandboxed-checks) describes. If you set
   `check-gotest`'s `-goproxy`, set the same value on the core program, and
   if the proxy runs in the cluster, add a NetworkPolicy of your own that
   lets test Pods reach it. If you set `check-gotest`'s `-go-cache`, set the
   core program's `-go-cache-namespace`, as
   [Share modules and build outputs](#share-modules-and-build-outputs)
   describes.
5. Map the checks' service accounts to their checks in the
   `git-k8s-checks` ConfigMap, as [Install](#install) does, and then
   install the checks. They lose their RBAC rule for `trackedbranches/status`,
   and send their results to the core program.
6. If you applied the `test-pods` NetworkPolicy that an earlier version of
   this README described, delete it from each namespace that has a
   `TrackedRepository`. A cluster allows any connection that one of a Pod's
   NetworkPolicies allows, so that policy still lets test Pods reach the git
   remote:

   ```sh
   kubectl -n NAMESPACE delete --ignore-not-found networkpolicy test-pods
   ```

When the core program starts, it changes `status.checks` in the `TrackedBranch`
CustomResourceDefinition to an atomic map, which one field manager writes as
a whole, and only then installs `config/policy.yaml`. From that change on, a
status write from an old check that no policy rejects replaces all of
`status.checks` with that check's entry, which is why step 3 comes first. An
earlier core program that installs the earlier policy when it starts does
that again each time, so if it restarts before step 4, apply
`config/policy.yaml` again. While the earlier policy is installed, the core
program reports `PoliciesInstalled` as `False`. The results controller takes
over a branch's results the first time it writes them, and server-side apply
then removes the old checks from the branch's managed fields.

## What each program can do

git-k8s divides what each program can do, so that no single check can land
a change:

- A check can push only to branches that have a parent whose merge policy
  gives the check `mayPush: true`, and to the branches under a prefix that
  `-branch-prefix` gives it, such as `check-conflicts`' `resolve/`, except
  parents. Each push is a new head that every check runs on again, so a
  compromised check can't move a parent or skip a merge gate through the
  mirror, and the admission policies keep it to its own result. A check
  that doesn't [sign commits](#sign-commits) can't read Secrets or reach
  external repositories. One that does can read every Secret in the
  namespaces that it watches, including the external repositories'
  credentials, so a compromised one can push to an external repository
  without the mirror.
- The test container, which runs the branch's code, has no token and no
  credentials. The core program's NetworkPolicy lets it reach the core
  program's port for the mirror and the results endpoint, which both need a
  token, and the cluster's DNS servers, and with the flags that
  [Sandboxed checks](#sandboxed-checks) describes, a module proxy and
  `go-cache`. `check-gotest` creates the Pod but can't change
  NetworkPolicies. The init container's token can fetch only
  the branch's repository, only before the test container starts, and stops
  working when the Pod is deleted.
- An agent Pod's `agent` and `result` containers have no token and no git
  credentials. Its `prepare` init container's token can fetch only the
  branch's repository, and stops working when the Pod is deleted or the
  agent finishes.
- Tokens for the mirror and the results endpoint have their own audiences,
  `git-k8s-mirror` and `git-k8s-results`. The API server accepts neither,
  and each endpoint accepts only its own, not the other's or the API
  server's. The kubelet renews each check's tokens, which last an hour.
- The mirror runs git with `--end-of-options` before every argument that
  comes from a `TrackedRepository` or a push, and doesn't sync or list branches
  whose names start with `-`, so neither can pass git an option.

The core program is the only program that changes NetworkPolicies, which it
does in every namespace, the only one that gets tokens from Octo STS, and
the only one that pushes to external repositories. It decides what lands.
Agent Pods that a controller starts with `RunJob`, and the update Pods of
`git-k8s-deps`, get an external repository's credentials to fetch from it,
and the programs that sign commits can read them, as
[Limitations](#limitations) describes.

Kubernetes RBAC is the trust boundary. Anyone who can write a
`TrackedRepository` in a namespace chooses the external repository, and the
Secret or Octo STS identities that the core program uses there. Of the
service accounts, only those that the `git-k8s-checks` ConfigMap maps to
`NAME` can write the `NAME` result, but people who can write `TrackedBranch`
status in a namespace can write any result.
Such a result can name a Pod in that namespace for the mirror to let fetch
the repository, but the mirror accepts only a `Pending` Pod with the
controller label of a check whose result names it, on a branch whose merge
policy lists the check. Making such a Pod takes the right to create Pods in
that namespace, which already lets a Pod mount the repository's Secret.
Anyone who can create tokens for a check's service
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

The agent runner in `agent/runner` has its own tests, which its image build
also runs:

```sh
cd agent/runner && npm ci && npm test
```

The repository's daily dependency update upgrades the runner's npm
dependencies too, and runs these tests.

The end-to-end test installs every program with `generate` in a
[kind](https://kind.sigs.k8s.io/) cluster with a local registry. It runs a
git server on this machine as the external repository, which Pods reach
through the kind network's gateway. It pushes branches to that git server,
and to the mirror through `kubectl port-forward` with tokens from
`kubectl create token`. The git server accepts only commits signed with
their committer's key, as a forge that requires signed commits does, so the
test fails if git-k8s pushes an unsigned commit. A module proxy on this
machine serves `go-cache` a module that isn't on the internet. The test
reads `go-cache`'s metrics to check that a test Pod got the module through
it, and that a later Pod read its build outputs instead of compiling them.
It checks what test Pods can reach only if the cluster enforces
NetworkPolicies, which kindnet does only on kernels with `nfnetlink_queue`.
It needs Docker, `kubectl`, `git`, `ssh-keygen`, and `curl`, and installs
kind if it's missing:

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

The stress harness in `e2e/stress` measures how many branches git-k8s lands
per minute, and where each branch's time goes, on a kind cluster that its
`setup.sh` starts. Its scenarios push bursts of branches, some with
conflicts, failing tests, or high risk, to one or more repositories. CI runs
only its unit tests. To run a scenario, see
[`e2e/stress/README.md`](e2e/stress/README.md).

## Limitations

- The mirror polls external repositories; it doesn't receive webhooks. A
  push to an external repository takes up to `pollInterval` to reach
  git-k8s. Pushes to the mirror and landings reach the external repository
  at once.
- External repositories authenticate with HTTP basic auth only.
- The core program runs one replica, so the mirror, the results endpoint,
  and the controllers are down while it restarts.
- The mirror syncs branches, not tags.
- The test Pods' NetworkPolicy works only with a network plugin that
  enforces it.
- An approval holds only for heads that make the same change, as
  [Which results count](#which-results-count) defines. When the `base`
  check's merge of the parent at the front of the queue doesn't, such as
  when the parent renamed a file that the branch changes, the branch leaves
  the queue until someone approves the merge, then joins at the back.
- A check that doesn't finish at the front of a queue holds up the branches
  behind it while the front can still land.
- `check-base`, `check-gofmt`, `check-review`, `check-conflicts`,
  `check-deps`, and `git-k8s-deps` [sign commits](#sign-commits), so
  `generate` lets them read every Secret, including the external
  repository's credentials and the Cursor API key, which only the agent
  Pods of `check-review`, `check-conflicts`, and `check-deps` use.
  [Sign commits in the mirror](future-work.md#sign-commits-in-the-mirror)
  describes how to remove that. `check-gotest`, `check-review`,
  `check-conflicts`, and `check-deps` can also create Pods in every
  namespace that opts in to check Pods, and `check-conflicts` can even
  without `-agent-image`. `git-k8s-deps` can create Pods in every
  namespace. Installing these programs with `generate -watch-namespace`
  limits their Secrets and Pods to one namespace.
- The branch-name prefix `resolve/` lets `check-conflicts` fetch every
  repository's copy, and push under `resolve/` in each, even in a repository
  whose merge policies don't list the `conflicts` check.
- Agent Pods that a controller starts with `RunJob`, and the update Pods of
  `git-k8s-deps`, fetch from the external repository with its credentials,
  because the mirror accepts a token that's bound to a Pod only from a check's
  Pod. So with Octo STS, `git-k8s-deps` updates only a public repository, and
  while the external repository is behind the mirror, its updates wait, as
  [Update Pods](#update-pods) describes.
- `git-k8s-deps` keeps at most 256 KiB of first-seen times in its ConfigMap,
  and drops the oldest first, so after a restart, a version whose time it
  dropped waits `-min-age` again. When a write leaves out times, it logs a
  warning that says how many. With more than one shard, or for a moment while a
  Deployment with one replica rolls out, two controllers can write the
  ConfigMap at once, and the last write wins. Each one writes its times again
  the next time that it reads the module's versions, so a time is lost only
  when the controller that saw the version stops first.

[`future-work.md`](future-work.md) proposes fixes for these, and lists the
other known gaps.
