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
  the [dependency update controller](#update-dependencies-with-a-controller),
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
trust results only as far as it trusts the policy. The policy might not be
installed, and it recognizes checks only by their service account names.

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
- The core program maps service accounts to checks, so a check no longer has
  to run as `check-NAME` in the namespace `check-NAME`.
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

## Land branches through a merge queue

Branches land by fast-forward only. Each landing moves the parent, so no
other open branch contains the parent's head anymore. `check-base` merges the
parent into each of them, which changes their heads and runs every check
again, including a `go test` Pod. With N open branches, each landing costs
about N runs of every check.

The proposed fix is a queue for each parent. A branch whose checks pass,
apart from being behind its parent, joins the queue. Only the branch at the
front merges the parent in, runs its checks again, and lands. The others wait
instead of chasing the parent. Testing several queued branches together, and
landing them all when they pass, cuts the cost further.

Questions to settle first:

- Where the queue lives. It could be in each `GitBranch`'s status, written by
  the merge controller, or in a new object for each parent.
- How the queue orders branches, such as by when they were approved, by when
  they passed, or by a priority field.
- Whether queued branches merge the parent in, as `check-base` does, or
  rebase onto it.

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

## Start waiting go test Pods in order

`-max-pods` caps how many test Pods run at once, but the branches that wait
start in no particular order. The count also comes from the cache, which
hasn't seen Pods created moments earlier, so a burst of pushes can start a
Pod or two over the cap.

The proposed fix is to record when each branch started waiting, in the
check's outputs, and start the branch that has waited longest. Counting the
Pods that the process has created until the cache shows them keeps the cap
exact.

## Install the admission policies with the core program

`config/policy.yaml` is a separate install step. The `PoliciesInstalled`
condition reports when it's missing, but nothing installs it. The core
program could apply the policies when it starts, the way kube installs CRDs.
That needs RBAC to write ValidatingAdmissionPolicies, which a compromised
core program could use to weaken them. The core program already decides
what lands, so that may be acceptable. Once checks send results to the core
program instead of writing them, the check-results policy is a backstop, and
the policy that stops controllers from approving branches matters most.

## Support more ways to land

Landing fast-forwards the parent to the branch's head, so the parent ends up
at the commit that the checks tested. Squash and rebase landings, which many
forges offer, make a commit that no check saw, so they need either another
round of checks or a rule about which results still count.

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

## Update dependencies with a controller

This repository's dependency workflow updates every app's dependencies each
day, and opens a pull request that merges when the tests pass. A dependency
update controller could do the same for each repository that git-k8s tracks.

The proposed fix is a controller that polls for new versions of a
repository's dependencies, such as with `go list -m -u all` for Go modules,
on an interval that it sets with kube's `RequeueAfter`. When it finds
updates, it applies them and pushes the result to a new branch in the mirror
under its own prefix, such as `deps/`. The `GitRepository` tracks that prefix
with the updated branch, such as `main`, as its parent.

The decision is that dependency branches pass the same checks as any other
branch, and land as soon as they do. They need a person's approval only when
the change is risky, which the parent's merge gate already says, for example
`checks.risk.outputs.level == "low" || checks.approval.passed`. So
dependency branches need no gate of their own, and `when` doesn't need to
tell them apart from other branches.

When an update breaks the build or the tests, a local agent can change the
code to fit the dependency's new API, as described in
[Agentic checks](README.md#agentic-checks), and push the change to the
branch, within the branch's budget for automated commits. When the agent
can't fix it, the branch waits for a person.

Questions to settle first:

- How `check-risk` rates a dependency update. It counts changed lines today,
  and lines in `go.sum` say little about risk. A new major version, a new
  module, or code that the agent changed to fit a new API should make a
  change high risk, and a patch release shouldn't.
- Whether to update every dependency on one branch, as the dependency
  workflow does, or each on its own branch. Separate branches keep one bad
  update from holding back the rest, and keep each change small enough to
  rate low risk.
- Which ecosystems to support first. This repository's
  `update-go-dependencies.sh`, `update-js-dependencies.sh`, and
  `update-rust-dependencies.sh` show what each takes.
- How long to wait before taking a new version. Compromised releases are
  often pulled within days, so a delay keeps most of them out.
- What happens to a branch that hasn't landed when newer versions come out.
  The controller could push the newer versions to the same branch.
