# Future work

This file lists the known gaps in git-k8s, roughly in priority order. Each
section describes the problem, a proposed fix, and what to settle before
building it, and notes the decisions made so far. The [README](README.md)
describes how git-k8s works today.

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

## Keep the mirror up while it restarts

The core program runs one replica, because only one process can write the
mirror's copies. While it restarts, during a rollout or after its node
fails, checks can't fetch or push, branches don't land, and test Pods retry
their fetches. A volume that can't move between zones keeps the core program
down while its zone is down.

The proposed fix is several replicas, each with its own copy of every
repository. One replica, the leader, takes pushes, and acknowledges a push
once another replica has it too. The other replicas serve fetches, and one
of them takes over when the leader stops.

Questions to settle first:

- How a replica catches up when it starts, such as by fetching from the
  leader.
- How to choose a new leader without losing a push that the old leader
  acknowledged.
- How a push that reaches another replica gets to the leader. `kube.Serve`
  runs on every replica, and `kube.Trigger` queues a reconcile only on the
  replica that reconciles the object.
- How kube installs it. `generate` gives a program with a `kube.Volume` one
  claim and one replica, so a volume for each replica needs a StatefulSet,
  which `generate` doesn't write.

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

## Require an approver who didn't write the change

`check-approval` reports who approved a branch, but not who wrote it, so a
gate can't require that someone other than the author approved.
`check-approval` doesn't read commits today, but it could fetch them from the
[mirror](README.md#the-mirror) with its mirror token, without the
repository's credential.

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
