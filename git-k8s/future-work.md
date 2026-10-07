# Future work

This file lists the known gaps in git-k8s, roughly in priority order. Each
section describes the problem, a proposed fix, and what to settle before
building it, and notes the decisions made so far. The [README](README.md)
describes how git-k8s works today.

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

## Keep the mirror up while it restarts

The core program runs one replica, because only one process can write the
mirror's copies. While it restarts, during a rollout or after its node
fails, checks can't fetch, push, or send results, branches don't land, and
test Pods retry their fetches. A volume that can't move between zones keeps
the core program down while its zone is down.

The proposed fix is several replicas, each with its own copy of every
repository. One replica, the leader, takes pushes, and acknowledges a push
once another replica has it too. The other replicas serve fetches, and one
of them takes over when the leader stops. The results endpoint already
works with several replicas: a replica that doesn't write a branch's results
answers `503`, and the check tries again on a new connection.

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

Two things can hold up the branches behind the front of a merge queue:

- A check that never finishes at the front, such as one whose controller
  isn't running, holds up every branch behind it while the front can still
  land.
- A squash or rebase landing that pushes its commit to the front for the
  checks holds the front until the repositories controller lists that
  commit. If someone pushes the branch's old head back before then, the
  listing doesn't change, so the branch holds the front until its head or
  its parent's head changes.

The proposed fix is a time limit at the front of the queue, after which the
branch leaves it.

Questions to settle first:

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
`check-approval` already reads the repository from the
[mirror](README.md#the-mirror) to compare an approved commit's change with
the head's, so it could read the commits' authors too.

Questions to settle first:

- Whose authorship counts. The head is often a fix commit that a check
  pushed, so the authors to compare are those of the branch's commits
  without a `Git-K8s-Fixer` trailer.
- How to trust an author. A commit's author email is whatever the person who
  made the commit set, so the check needs verified commit signatures, and a
  way to map each signer to the Kubernetes username in `approved-by`.

## Sign commits in the mirror

`check-base`, `check-gofmt`, `check-review`, `check-conflicts`,
`check-deps`, the merge controller, and `git-k8s-deps` sign their commits
with a key that they read from a Secret, so a compromised check can sign
anything with it. The key is also the only reason that the checks and
`git-k8s-deps` can read Secrets, and `generate` lets them read every Secret
in the namespaces that they watch, including the external repositories'
credentials, which they don't use. The [mirror](README.md#the-mirror) could
hold the key instead and sign for them, for example through a program that
git's `gpg.ssh.program` setting runs, so that none of them reads Secrets.

Every change reaches GitHub as a push from the mirror. For a repository
that gets [tokens from Octo STS](README.md#github-repositories), the mirror
pushes as Octo STS's GitHub App. Branch protection rules and rulesets have
to let that App push to protected branches without a pull request, by
adding it to their bypass lists. An App can't have a signing key, so the
commits stay signed with a bot account's key, with that account's email
address as their committer.

## Sign commits with gitsign

Keyless signing with [gitsign](https://github.com/sigstore/gitsign) leaves
no long-lived key to protect, but git-k8s doesn't support it, for the
reasons in [Sign commits](README.md#sign-commits). Supporting it needs:

- Verification of Sigstore signatures on GitHub, so that a rule that
  requires signed commits accepts the commits that gitsign signs.
- A private Sigstore for the end-to-end test: a Fulcio certificate
  authority that accepts tokens from the kind cluster's service account
  issuer, and a Rekor transparency log.

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
the mirror's sync, and the [conflicts check](README.md#resolve-conflicts)
coalesces any that race a change in the mirror. The runner runs agents
through a backend, so a cloud backend can start a run from an agent Pod and
report its verdict through the same result transport, without changes to the
checks.

Questions to settle first:

- Whether an agent Pod waits for a cloud agent's run, which happens outside
  the cluster, or the check follows the run itself.
- Which GitHub branches a cloud agent may push to.

## Let update Pods fetch from the mirror

[`git-k8s-deps`](README.md#update-pods) reads branches from the mirror and
pushes its branches there, but its update Pods fetch the parent from the
external repository with the repository's credentials. The mirror accepts a
token that's bound to a Pod only from a check's Pod, which a `Running`
result names. So an update Pod gets credentials that can push to any
branch, a repository that gets tokens from Octo STS has to be public, and
right after the parent moves, an update can find it at another commit in the
external repository. The mirror could also accept a Pending Pod that a
controller with a branch-name prefix names in a record that only the
controller's service account can write, and that has the controller's label.
Update Pods, and agent Pods that a controller starts with `RunJob`, could
then fetch from the mirror with tokens bound to the Pods, like test Pods.
Once the mirror also [signs commits](#sign-commits-in-the-mirror),
`git-k8s-deps` stops reading Secrets.

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
