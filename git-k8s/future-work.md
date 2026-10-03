# Future work

This file lists the known gaps in git-k8s, roughly in priority order. Each
section describes the problem, a proposed fix, and what to settle before
building it. The [README](README.md) describes how git-k8s works today.

## Put git access behind a proxy in the core program

Every program that fetches or pushes holds the repository's credential: the
core program, `check-base`, `check-gofmt`, and `check-risk`. The credential
can push to any branch, so a compromised check can push straight to a parent
such as `main` and skip every merge gate. The admission policies protect only
Kubernetes objects. These four programs can also read Secrets in every
namespace, because kube's `generate` grants them cluster-wide `get` on
Secrets.

The same design has two more costs. Test Pods fetch from the remote, so no
NetworkPolicy can block the rest of their traffic. And each of the four
programs keeps its own copy of every repository.

The proposed fix is a smart-HTTP git server in the core program, at a path
such as `/NAMESPACE/REPOSITORY.git`:

- Checks and test Pods fetch from it instead of from the remote. It serves
  fetches from its own cache, which it fetches into with its credential.
- Checks push fixes through it. It reads the commands at the start of each
  `git-receive-pack` request, and allows an update only to a branch that has
  a parent, never to a parent, and only from the old commit that the push
  names. Then it forwards the push with its credential.
- Only the core program reads Secrets, so the checks need no access to
  Secrets.
- A NetworkPolicy lets test Pods reach only the core program's Service and
  DNS.

Questions to settle first:

- How callers prove who they are. A projected service account token with an
  audience such as `git-k8s`, checked with a TokenReview, maps a caller to
  `check-NAME`. kube has no API for TokenReview, so the core program needs
  its own small client, or kube needs one.
- How a test Pod authenticates. It runs without a service account token, so
  its init container needs its own projected token bound to the Pod, or a
  short-lived token that the proxy issues.
- How the proxy scales. It puts the core program in the path of every fetch
  and push. Every replica can serve the proxy, even though only the leader
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

## Share repository and build caches

The core program, `check-base`, `check-gofmt`, and `check-risk` each keep a
bare copy of every repository in `/tmp`. Each fetches a repository's full
history the first time, and loses its copy when its Pod restarts. Each test
Pod fetches its branch from the remote and builds with an empty Go build
cache.

The proxy leaves one copy of each repository. Beyond that:

- A PersistentVolume keeps the cache across restarts.
- A partial clone (`--filter=blob:none`) skips file contents that no check
  reads. It needs a promisor remote that git can reach, with credentials,
  when it fetches missing objects later.
- An in-cluster Go module proxy, and a shared build cache through
  `GOCACHEPROG` or a ReadWriteMany volume, let a test Pod reuse what earlier
  Pods downloaded and compiled. A module proxy in the cluster also lets
  tests with dependencies run without giving them the internet through
  `-goproxy`.

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
forge that requires signed commits rejects them, and a forge that protects
`main` has to let git-k8s's credential bypass that protection to land
anything.

Possible fixes, which work together:

- Sign commits with [gitsign](https://github.com/sigstore/gitsign), which
  signs keylessly through Sigstore, or with an SSH key that only the core
  program holds.
- Give landings their own credential, so that only the core program can push
  to protected branches. Until the proxy exists, the checks mustn't be able
  to read that credential. kube's `generate -watch-namespace` can limit them
  to the namespace that holds the repositories, with the landing credential
  in another namespace.

## Receive webhooks

The controllers poll remotes, so a person's push takes up to `pollInterval`,
30 seconds by default, to show up. Each poll lists every branch of the
repository.

The proposed fix is an endpoint in the core program for push webhooks from
forges such as GitHub, GitLab, and Gitea. It checks each webhook's signature
against a secret for its repository, then reconciles the matching
`GitRepository` at once. Polling stays as the fallback.

Questions to settle first:

- How a webhook starts a reconcile. kube can't queue a key from outside a
  reconcile, so either kube adds an API for it, or the endpoint patches an
  annotation on the `GitRepository`.
- How to expose the endpoint, through an Ingress or a Gateway route, and its
  TLS.

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
core program could use to weaken them. The core program can already push to
every parent, so that may be acceptable.

The policies recognize a check only by the service account `check-NAME` in
the namespace `check-NAME`. An install that puts checks in other namespaces,
such as one install for each team, can't write results. A policy parameter
that lists the check service accounts would remove that constraint.

## Support more ways to authenticate

Remotes authenticate with HTTP basic auth only. SSH keys, and GitHub App
installation tokens, which expire after an hour, need support in
`credentials.Remote` and in the test Pods' fetch.

## Support more ways to land

Landing fast-forwards the parent to the branch's head, so the parent ends up
at the commit that the checks tested. Squash and rebase landings, which many
forges offer, make a commit that no check saw, so they need either another
round of checks or a rule about which results still count.

## Add an agentic code review check

The first design called for a check that reviews a branch with a model and
approves it. `check-approval` only reads a person's approval. A review check
needs network access and an API key, which is another reason to give each
check its own credentials instead of the repository's.

## kube changes that git-k8s would use

These belong in kube, in their own pull requests:

- `generate` grants `patch` on every reconciled type. kube removes a
  finalizer that a controller no longer needs, which takes `patch`, so
  dropping the grant needs another way to remove finalizers that an earlier
  version of a program added.
- kube installs CRDs only for types that a controller reconciles. A program
  that only owns a custom type doesn't know all of the type's versions, so
  it can't safely update the CRD. It could still create a missing CRD and
  never update it.
- kube has no Events API, so landings and fix pushes show up only in logs and
  conditions. An event intent that kube carries out after a reconcile, and
  that groups repeats, would show them in `kubectl describe`.
- `Apply` drops `status`, so a controller can write another controller's
  status only by reconciling a view of its type, as each check does.
- The cache lags a controller's own writes, so a reconcile that runs just
  after a write can repeat work.
- The proxy needs a TokenReview client, and webhooks need a way to queue a
  reconcile from outside one.
