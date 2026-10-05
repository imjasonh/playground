# Future work

This file lists the known gaps in git-k8s, roughly in priority order. Each
section describes the problem, a proposed fix, and what to settle before
building it, and notes the decisions made so far. The [README](README.md)
describes how git-k8s works today.

## Run an in-cluster git mirror

Every program that fetches or pushes holds the repository's credential: the
core program, `check-base`, `check-gofmt`, and `check-risk`. The credential
can push to any branch, so a compromised check can push straight to a parent
such as `main` and skip every merge gate. The admission policies protect only
Kubernetes objects. These four programs can also read Secrets in every
namespace, unless they're installed with kube's `generate -watch-namespace`.

The same design has more costs:

- Test Pods fetch from the remote, so no NetworkPolicy can block the rest of
  their traffic.
- Each of the four programs keeps its own copy of every repository.
- The controllers poll remotes, so a push takes up to `pollInterval`, 30
  seconds by default, to show up, and each poll lists every branch.

The decided fix is a git mirror in the cluster that's the source of truth
for each repository, and the only git server that checks and controllers use.
GitHub, and any other forge, is a downstream copy:

- The mirror keeps each repository on a PersistentVolume and serves it over
  smart HTTP, at a path such as `/NAMESPACE/REPOSITORY.git`.
- It syncs in both directions. It pushes every ref change to the external
  repository, and fetches from the external repository to pick up branches
  that people push there.
- Checks and test Pods fetch only from the mirror, and checks push fixes only
  to it. The mirror reads the commands at the start of each
  `git-receive-pack` request and applies its caller's push rules. A check can
  update only a branch that has a parent, never a parent, and only from the
  old commit that the push names. A controller that starts branches, such as
  the [dependency update controller](README.md#dependency-updates),
  can also create branches under its own prefix. Only the merge controller
  updates parents.
- When a branch changes on both sides between syncs, such as a person's push
  to GitHub and a check's fix pushed to the mirror, the mirror overwrites
  neither. It keeps the external repository's head under a separate ref,
  reports the branch as diverged, and leaves it to the
  [conflict resolution controller](#resolve-conflicts-in-a-controller).
- The mirror holds the only credentials for external repositories, so no
  other program reads Secrets. For a repository that gets
  [tokens from Octo STS](README.md#github-repositories), only the mirror
  requests tokens for the `GitRepository`'s `gitIdentity`, so the trust
  policy's `subject_pattern` narrows to the mirror's service account. The
  checks stop requesting tokens for Octo STS, so `generate` stops granting
  them `create` on `serviceaccounts/token`, and the risk that
  [Security](README.md#security) describes no longer applies to them.
- Every ref change passes through the mirror, so it tells git-k8s about each
  one as it happens, and git-k8s reconciles the repository at once. Only the
  mirror polls, and only the external repository, to find pushes that people
  made there. git-k8s doesn't rely on GitHub webhooks.
- A NetworkPolicy lets test Pods reach only the mirror and DNS.

Questions to settle first:

- When the mirror acknowledges a push from a check or the merge controller.
  Acknowledging it before syncing it to GitHub keeps git-k8s working through
  a GitHub outage, and acknowledging it after keeps the two from differing.
  The conflict resolution controller coalesces branches that differ, so
  acknowledging first fits GitHub's role as a downstream copy.
- How callers prove who they are. A projected service account token with an
  audience such as `git-k8s`, checked with a TokenReview, maps a caller to
  `check-NAME`. A test Pod runs without a service account token, so its init
  container needs its own projected token bound to the Pod.
- Where the mirror runs, in the core program or in its own Deployment. Its
  repositories live on a PersistentVolume, so one replica writes at a time,
  and backups matter.
- How a ref change starts a reconcile. kube can't queue a key from outside a
  reconcile, so either kube adds an API for it, or the mirror patches an
  annotation on the `GitRepository`.

## Authenticate check results with tokens

The check-results admission policy keeps each check to its own entry in
`status.checks` by looking at the service account that makes each write. A
result carries no proof of which check wrote it, so the merge controller can
trust results only as far as it trusts the policy, its binding, and the
`git-k8s-checks` ConfigMap that maps service accounts to checks.

The decided fix is for checks to stop writing `status.checks`. A check sends
each result to an endpoint in the core program, next to the mirror, with a
projected service account token. The core program verifies the token with a
TokenReview, and writes the result to the entry of the check that the token
proves, and no other. A check can't write another check's result, by mistake
or on purpose, because it can't write results at all:

- Checks lose write access to `GitBranch` status. They reconcile a view of
  `GitBranch` that declares no status, so kube doesn't write one and
  `generate` doesn't grant them access, and they read their earlier results
  through a second view.
- The core program finds the check for a token's service account the way the
  check-results policy does, from the `git-k8s-checks` ConfigMap or the
  `check-NAME` convention.
- The admission policy stays as a backstop. People with write access to
  `GitBranch` status can still write a result, for example to unblock a
  branch whose check is broken.

The endpoint uses the same token check as the mirror, so the two share it.

## Support GitHub Enterprise Server

A `GitRepository` gets [tokens from Octo STS](README.md#github-repositories)
only for a repository on github.com, because the public Octo STS service
issues tokens only for github.com. A repository on GitHub Enterprise Server
needs a Secret.

GitHub Enterprise Server needs its own Octo STS deployment, with a GitHub App
on that server. The programs then need the deployment's token exchange URL
and audience, and the server's web and REST API URLs. These can't be
`GitRepository` fields, because a tenant could then choose where the programs
send their service account tokens, and for which audience. They belong in
program flags, like `-fake-github`, or in a cluster-scoped object that only
administrators can change.

## Resolve conflicts in a controller

Two kinds of conflict stop a branch, and nothing resolves either one:

- `check-base` merges a branch's parent into it when the branch falls behind.
  When that merge conflicts, the check fails with the conflicting paths in
  its `conflicts` output, and the branch waits for a person.
- With the mirror, a branch can change both in the mirror and in the
  external repository between syncs. The mirror overwrites neither, so the
  branch stays diverged.

The decided fix is a separate conflict resolution controller that tries to
coalesce both kinds. For a merge that conflicts, it pushes a merge of the
parent that resolves the conflicts. For a diverged branch, it pushes a
commit to the mirror that contains both heads, and the mirror then
fast-forwards the external repository to it. Each resolution is a new head,
so every check runs again on it, and it counts toward the branch's
`maxAutomatedCommits`.

The controller tries a resolution that git can make by itself first, such as
one that `git rerere` recorded earlier. Otherwise, an agent can resolve the
conflict, as described in
[Run agents from a controller](README.md#run-agents-from-a-controller). The
agent works in a Pod whose files are the merge of both commits, with
conflict markers where they conflict, and edits the files that conflict. It
has no shell, so it can't build or test the result. The controller commits
the agent's files and pushes them, and the checks verify the result like any
other head. When neither works, the branch stays as it is, and the
controller reports why.

Questions to settle first:

- How to resolve a diverged parent. A resolution commit on a parent would
  skip the merge gates, so the controller could push it to a new child
  branch that lands through the gates like any other. GitHub branch rules
  that let only the mirror push to parents make this rare.
- Whether to merge or rebase. A merge keeps both histories, while a rebase
  rewrites commits that someone already pushed.
- Where the mirror reports divergence, such as a condition and the external
  repository's head in the `GitBranch`'s status, which the controller
  reconciles.

## Keep queued branches moving

Three things can stop a branch in a merge queue from landing, or hold up the
branches behind it:

- An approval names one head, so the front's merge of its parent needs a
  new approval. The branch leaves the queue until it gets one, then joins at
  the back. By the time it reaches the front again, other branches have
  landed, so it merges the parent in and needs another approval. While
  branches keep landing, it might never land.
- A check that never finishes at the front, such as one whose controller
  isn't running, holds up every branch behind it while the front can still
  land.
- A squash or rebase landing that pushes its commit to the front for the
  checks holds the front until the repository controller lists that
  commit. If someone pushes the branch's old head back before then, the
  listing doesn't change, so the branch holds the front until its head or
  its parent's head changes.

The proposed fixes are an approval that still counts after a clean merge of
the parent, and a time limit at the front of the queue, after which the
branch leaves it.

Questions to settle first:

- How `check-approval` learns that the commits since the approved head are
  clean merges of the parent. It reads only the `GitBranch`, so it can't
  read Secrets. It could trust an output of `check-base`, which would let a
  compromised `check-base` carry an approval over to code that nobody
  approved, or read the repository itself, which needs its credentials.
- How long the front can wait, and whether a branch that runs out of time
  goes to the back of the queue or waits for a new push.

## Test queued branches together

The front of a merge queue lands one branch at a time, so each landing waits
for a full run of every check. Testing the first few queued branches merged
together, and landing them all when the checks pass, cuts the wait. When the
checks fail, the queue has to find the branch that broke them, for example
by testing each half of the batch.

Questions to settle first:

- Where the combined commit lives. A branch that git-k8s owns, such as
  `queue/main`, would let the checks run on it as on any other branch.
- How many branches go in a batch.

## Share build caches

Each test Pod fetches its branch and builds it with an empty Go build cache.
The mirror gives test Pods a nearby place to fetch from, but not what earlier
Pods built. An in-cluster Go module proxy, and a shared build cache through
`GOCACHEPROG` or a ReadWriteMany volume, let a test Pod reuse what earlier
Pods downloaded and compiled. A module proxy in the cluster also lets tests
with dependencies run without giving them the internet through `-goproxy`.

## Require an approver who didn't write the change

`check-approval` reports who approved a branch, but not who wrote it, so a
gate can't require that someone other than the author approved. Reading
commits takes the repository's credential, which can push to any branch and
which `check-approval` doesn't have. With the
[in-cluster git mirror](#run-an-in-cluster-git-mirror), it could read
commits without one.

Questions to settle first:

- Whose authorship counts. The head is often a fix commit that a check
  pushed, so the authors to compare are those of the branch's commits
  without a `Git-K8s-Fixer` trailer.
- How to trust an author. A commit's author email is whatever the person who
  made the commit set, so the check needs verified commit signatures, and a
  way to map each signer to the Kubernetes username in `approved-by`.

## Sign commits and respect protected branches

Fix commits, merges of a parent into a branch, and landings aren't signed. A
forge that requires signed commits rejects them. With the mirror, every
change reaches GitHub as a push from the mirror's Octo STS identity, so
GitHub's branch rules have to let that identity push to protected branches.

The proposed fix is for the mirror to sign the commits that git-k8s makes,
with [gitsign](https://github.com/sigstore/gitsign), which signs keylessly
through Sigstore, or with an SSH key that only the mirror holds.

## Run more agents

Other checks and controllers could run agents with the `agent` package that
[Agentic checks](README.md#agentic-checks) describes:

- A check that fixes failing tests and pushes the fix. Its agent can't run
  the tests, because agents get no shell, so it works from the failures that
  `check-gotest` reports, and `check-gotest` tests the fix on the new head.
- A controller that writes a pull request's description from the branch's
  change and commit log, and rewrites it when the head moves. It needs the
  forge's API, such as GitHub's, which git-k8s doesn't call.

## Run agents in Cursor's cloud

[Agentic checks](README.md#agentic-checks) run a local agent in a Pod for
each branch head. A cloud agent runs on Cursor's machines instead, against a
repository that it can clone. The mirror is in the cluster, so a cloud agent
would work on GitHub, the downstream copy. Its pushes reach git-k8s through
the mirror's sync, and the conflict resolution controller coalesces any that
race a change in the mirror. The runner runs agents through a backend, so a
cloud backend can start a run from an agent Pod and report its verdict
through the same result transport, without changes to the checks.

Questions to settle first:

- Whether an agent Pod waits for a cloud agent's run, which happens outside
  the cluster, or the check follows the run itself.
- Which GitHub branches a cloud agent may push to.

## Push dependency branches to the mirror

[`git-k8s-deps`](README.md#dependency-updates) pushes dependency branches
with the repository's credentials, and its update Pods fetch with them too.
So the controller reads Secrets, and only its own code keeps its pushes
under its prefix. Once the [mirror](#run-an-in-cluster-git-mirror) exists,
the core program gives the service account `git-k8s-deps` in the namespace
`git-k8s-deps` the prefix `deps/`. The controller then pushes to the mirror
with a projected service account token and stops reading Secrets, and its
update Pods fetch from the mirror with tokens bound to the Pods, like test
Pods.

## Update npm and Cargo dependencies

[`git-k8s-deps`](README.md#dependency-updates) updates only Go modules. This
repository's `.github/scripts/update-js-dependencies.sh` and
`.github/scripts/update-rust-dependencies.sh` show what npm and Cargo take.
The first raises the version ranges in `package.json` with
`npm-check-updates` and runs `npm install`. The second runs `cargo update`,
which changes only `Cargo.lock`, within the ranges in `Cargo.toml`. Each
ecosystem needs a source of versions and their times for `-min-age`, an image
with its tools for update Pods, a list of the files that the controller
accepts from a Pod and that `check-deps`'s agent can't change, and
`check-risk` rules for its manifests.
