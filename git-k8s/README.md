# git-k8s

git-k8s runs a branch workflow on Kubernetes. It tracks a git repository's
branches as `GitBranch` objects, and keeps a copy of the repository on a git
server in the cluster, the mirror. It runs checks on branches that propose
changes to another branch, and checks can push commits that fix what they
find. When the parent's merge policy passes, git-k8s fast-forwards
the parent to the branch. The mirror pushes every change to the external
repository, such as one on GitHub, and takes the changes that people push
there.

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

The `git-k8s` program, which this README calls the core program, serves the
mirror and runs two controllers. Each check runs as its own program. The
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
  over the fresh results. When it passes, the controller fast-forwards the
  parent in the mirror's copy, but only if the parent still points to the
  commit that the checks saw, so it never overwrites a parent that moved in
  the meantime. It then deletes the branch if the policy says to, and the
  repositories controller pushes both changes to the external repository.

The checks and the merge controller read each branch's repository as a
`gitk8s.Repository`, a `GitRepository` without its status, so the
repositories controller's status writes don't run them again.

Git objects live in the mirror's copies, and each check that reads files
keeps a local copy of the repositories that it reads. Only commit SHAs go
into Kubernetes objects, and no object records a single push or check run,
so the API server holds a bounded amount of state.

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
tests start. That's why `generate` lets the core program get Pods. Any
program that can create Pods in the namespace can set the label, so the
label means `check-gotest` only as long as the other programs that create
Pods there don't set it.

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
  whitespace and where in each file the lines are. Each commit in the head
  replays at most one commit, and a commit that changes no file has no
  replay.
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
can't find one inside a larger commit, such as a squash.

Comparing the heads can take a long time when both sides rewrote the same
long stretch of history between two syncs. The mirror stops comparing a
branch's heads after 10 minutes 20 seconds, twice the longest that one git
command can take, and leaves the branch as it is on each side, with the
reason `CompareFailed`. It remembers what it decided about each branch,
including a comparison that failed or took too long, and doesn't compare
that branch's heads again until either side's head moves or the core
program restarts. To resolve a branch whose comparison took too long, push
the same commit to the branch in the mirror and in the external repository.

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
  changed commits to resolve conflicts, unless your changes are on lines
  that the removed commits changed or next to them. If you push it to the
  side that rewound, each commit that the other side added needs a replay
  in it. If the branch still diverges, push the result to both sides.

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

Only the core program reads Secrets. Each time the repositories controller
fetches from or pushes to an external repository, it reads the Secret that
`secretRef` names, and sends its `username` and `password` keys with HTTP
basic auth, or `git` as the username if the Secret has none. Checks and test
Pods reach only the mirror, with their own tokens, so `generate` doesn't let
them read Secrets. The [`credentials`](credentials/credentials.go) package
holds the only code that reads them, and is where other ways to
authenticate, such as SSH keys, belong.

The mirror reaches external repositories only over the network, with
`https`, `http`, or `git` URLs. A `url` that's a local path or a `file` URL
fails, so a `GitRepository` can't read another namespace's copy from the
core program's volume.

## Checks

| Program | Check | What it does |
| --- | --- | --- |
| `check-base` | `base` | Passes when the branch contains its parent's head, or the parent already contains the branch. Otherwise it merges the parent in with `git merge-tree`, and fails with the conflicting paths if the merge conflicts. |
| `check-gofmt` | `gofmt` | Formats every `.go` file outside `vendor` and `testdata` directories with `go/format`, and passes when nothing changes. |
| `check-risk` | `risk` | Always passes, and sets `outputs.level` to `high` when the change is larger than `-max-lines` or touches a path that matches a `-sensitive` glob, and to `low` otherwise. |
| `check-approval` | `approval` | Passes when the `git-k8s.imjasonh.com/approve` annotation on the `GitBranch` names the branch's head. A push after the approval needs a new one. |
| `check-gotest` | `gotest` | Runs `go test ./...` in a Pod that it declares with `kube.Own`, and fails with the end of the test output. See [Sandboxed checks](#sandboxed-checks). |

A check with `mayPush: true` pushes its fix commit to the branch in the
mirror, which moves the head and runs the checks again. Fix commits have a
`Git-K8s-Fixer: CHECK` trailer, and `maxAutomatedCommits` (default 5) limits
how many a branch can have, so two checks that undo each other's fixes stop.
The same inputs always produce the same fix commit, so two retries of one
fix push the same commit.

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
waits for it. Maintenance that runs past the timeout gets `SIGTERM`, but
the repack that it started keeps running until it finishes or the Pod
stops. A killed maintenance leaves `objects/maintenance.lock`, which makes
later maintenance skip the copy without an error, so the mirror removes
that lock once it's stale, like the others.

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
NetworkPolicies, which it does in every namespace. It holds the external
repositories' credentials and decides what lands.

Kubernetes RBAC is the trust boundary. Anyone who can write a
`GitRepository` in a namespace chooses the external repository and the
Secret that the core program uses there. Of the service accounts, only
`check-gotest`'s can write the `gotest` result, but people who can write
`GitBranch` status in a namespace can write it too. Such a result can name a
Pod in that namespace for the mirror to let fetch the repository, but the
mirror accepts only a `Pending` Pod with `check-gotest`'s controller label.
Making such a Pod takes the right to create Pods in that namespace, which
already lets a Pod mount the repository's Secret. Anyone who can create
tokens for a check's service account can push as that check, and anyone who
can create tokens for a controller's service account can do what its
`-branch-prefix` allows.

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

[`future-work.md`](future-work.md) proposes fixes for these, and lists the
other known gaps.
