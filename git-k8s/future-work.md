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
  other program reads Secrets.
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

## Get GitHub credentials from Octo STS

For a GitHub repository, git-k8s uses a long-lived basic-auth Secret, such as
a personal access token. [Octo STS](https://github.com/octo-sts/app)
exchanges an OIDC token for a GitHub App installation token that expires
within an hour. The token gets the permissions that a trust policy in the
repository's `.github/chainguard/` directory grants to the identity in the
OIDC token. This repository's dependency workflow uses it.

The decision is to use the public Octo STS service. With the mirror, only
git-k8s's own components talk to GitHub: the mirror, to sync, and the program
that reports check runs. Each exchanges its projected service account token,
whose subject is `system:serviceaccount:NAMESPACE:NAME`, for a GitHub token,
and gets a new one before the old one expires. A `GitRepository` names the
trust policies to use instead of a Secret:

- The mirror's identity gets `contents: write`, to sync branches in both
  directions.
- The identity that reports results gets `checks: write`, so each check's
  result also shows as a check run on its commit, and on the commit's pull
  request. Check runs copy git-k8s's results; they don't change them.

Checks need no GitHub credentials at all. GitHub grants `contents: write` for
a whole repository, not for branches, which is acceptable because only the
mirror holds it.

Questions to settle first:

- How to test it. Octo STS fetches the cluster's OIDC discovery document and
  keys, so the cluster's issuer has to be reachable from the public service,
  as on GKE and EKS. A kind cluster's issuer isn't, so the end-to-end test
  needs a fake token service.
- Whether to support GitHub Enterprise Server, which the public service
  doesn't reach.

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
conflict, as described in [Add agentic operators](#add-agentic-operators). A
local agent in a Pod that has both commits checked out from the mirror edits
the conflicting files, builds the result, and pushes it. When neither works,
the branch stays as it is, and the controller reports why.

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

A branch lands only when it contains its parent's head. Each landing moves
the parent, so no other open branch contains the parent's head anymore.
`check-base` merges the parent into each of them, which changes their heads
and runs every check again, including a `go test` Pod. With N open branches,
each landing costs about N runs of every check.

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

## Record who approved a branch

An approval is the `git-k8s.imjasonh.com/approve` annotation. Nothing
records who set it, and anyone who can patch a `GitBranch` can approve it.

The proposed fix is a ValidatingAdmissionPolicy rule. When the approve
annotation changes, a `git-k8s.imjasonh.com/approved-by` annotation must
equal `request.userInfo.username`, and `approved-by` can't change otherwise.
`check-approval` then reports the approver in its outputs, so a gate can
require, for example, that the approver isn't the commit's author.

Questions to settle first:

- Whether an approval can take two annotations. A `kubectl` plugin could set
  both, and a MutatingAdmissionPolicy could set `approved-by` by itself once
  that API is generally available.
- Who can approve. A policy parameter, such as a ConfigMap of groups, could
  limit approvals to the people in them.

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

## Add agentic operators

Some checks and controllers are better written as an AI agent than as code:

- A check that reviews a branch's change and passes or fails it. The first
  design called for one, but `check-approval` only reads a person's
  approval.
- A check that fixes a failing test and pushes the fix.
- A controller that writes a pull request's description.
- The [conflict resolution controller](#resolve-conflicts-in-a-controller),
  when git can't resolve a conflict by itself.
- The [dependency update controller](#update-dependencies-with-a-controller),
  when an update breaks the build.

The Cursor SDK (`@cursor/sdk`), which this repository's `nethack-agent` and
`its-not-jaws` use, runs an agent with a Cursor API token.

The decision is to start with local agents in Pods, and to add cloud agents
later. A local agent runs in a sandboxed Pod for each branch, like
`check-gotest`'s, with the branch checked out from the mirror as its working
directory. The SDK is a Node package, so the Pod's image holds Node and a
small runner, and the operator creates the Pod and reads its result, as
`check-gotest` does with its test Pods. The agent sees only the files and
tools that the operator gives it, which limits what it can do when the code
that it reads tries to steer it.

A cloud agent runs on Cursor's machines, against a repository that it can
clone. The mirror is in the cluster, so a cloud agent would work on GitHub,
the downstream copy. Its pushes reach git-k8s through the mirror's sync, and
the conflict resolution controller coalesces any that race a change in the
mirror. An interface that hides where the agent runs, with a fake for tests
like `its-not-jaws`'s mock backend, lets operators move to cloud agents
without other changes.

Questions to settle first:

- What it costs. The SDK reports each run's token usage, which
  `nethack-agent` turns into a dollar cost. A budget for each branch, like
  `maxAutomatedCommits`, and for each day, keeps a loop of runs from costing
  too much.
- How much to trust an agent. It reads code from the branch, which can tell
  it what to do, so its results and fixes need the same limits as any
  check's: token-authenticated results, the budget for automated commits,
  and no credentials beyond the mirror.
- Where the Cursor API token lives. A Secret that only the agent's Pod
  mounts keeps it from every other program.
- What to do when two runs disagree. An agent can give a different answer
  each time, so a result for a commit stays until the commit changes.
- How an operator follows a cloud agent's run, which happens outside the
  cluster, and which GitHub branches a cloud agent may push to.

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
[Add agentic operators](#add-agentic-operators), and push the change to the
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
