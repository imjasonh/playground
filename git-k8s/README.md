# git-k8s

git-k8s runs a branch workflow on Kubernetes. It tracks a remote git
repository's branches as `GitBranch` objects and runs checks on branches
that propose changes to another branch. Checks can push commits that fix
what they find. When the parent's merge policy passes, git-k8s fast-forwards
the parent to the branch.

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

The `git-k8s` program runs two controllers, and each check runs as its own
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
  over the fresh results. When it passes, the controller fast-forwards the
  parent with `git push --force-with-lease`, so a parent that moved in the
  meantime is never overwritten. It then deletes the branch if the policy
  says to.

The checks and the merge controller read each branch's repository as a
`gitk8s.Repository`, a `GitRepository` without its status, so the
repositories controller's status writes don't run them again.

Git objects stay in local bare repositories, one for each `GitRepository`
in each program. Only commit SHAs go into Kubernetes objects, and no object
records a single push or check run, so the API server holds a bounded amount
of state.

After a branch lands, `kubectl get gitbranches` shows what's still open:

```
NAME                    BRANCH   HEAD                                       PARENT   STATE              AGE
app-c-auth-f684729ccf   c/auth   d28547a6c959905ea8dc037ac37541167a50638c   main     WaitingForChecks   9s
app-main-9157892a7c     main     610a7734a0b4d1bc1991a669d9feb35fd159219b                               48s
```

The `Merged` condition's message explains a `WaitingForChecks` state, for
example `checks: approval Failed, base Passed, gofmt Passed, risk Passed (high)`.

## Checks

| Program | Check | What it does |
| --- | --- | --- |
| `check-base` | `base` | Passes when the branch contains its parent's head, or the parent already contains the branch. Otherwise it merges the parent in with `git merge-tree`, and fails with the conflicting paths if the merge conflicts. |
| `check-gofmt` | `gofmt` | Formats every `.go` file outside `vendor` and `testdata` directories with `go/format`, and passes when nothing changes. |
| `check-risk` | `risk` | Always passes, and sets `outputs.level` to `high` when the change is larger than `-max-lines` or touches a path that matches a `-sensitive` glob, and to `low` otherwise. |
| `check-approval` | `approval` | Passes when the `git-k8s.imjasonh.com/approve` annotation on the `GitBranch` names the branch's head. A push after the approval needs a new one. |
| `check-gotest` | `gotest` | Runs `go test ./...` in a Pod that it declares with `kube.Own`, and fails with the end of the test output. See [Sandboxed checks](#sandboxed-checks). |
| `check-review` | `review` | Has an AI agent review the branch's change against its parent in a sandboxed Pod. It passes or fails with the agent's reasoning as its message, and sets `outputs.summary` and the run's token counts. With `mayPush: true`, the agent can also fix what it finds. See [Agentic checks](#agentic-checks). |
| `check-conflicts` | `conflicts` | Passes when merging the parent into the branch has no conflicts. When the merge conflicts, or the branch diverged from the external repository, it pushes a merge that git or an AI agent resolved, or fails when neither can. When a side of a diverged branch rewound, it replays the other side's commits onto that side's head instead of merging. See [Resolve conflicts](#resolve-conflicts). |

A check with `mayPush: true` pushes its fix commit to the branch, which moves
the head and runs the checks again. Fix commits have a `Git-K8s-Fixer:
CHECK` trailer, and `maxAutomatedCommits` (default 5) limits how many a
branch can have, so two checks that undo each other's fixes stop. The same
inputs always produce the same fix commit, so two retries of one fix push the
same commit.

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
	checks.Main[Branch](checks.Check{Name: "readme", Remote: credentials.Remote, Run: run})
}
```

`in.Repo` fetches the branch and its parent into the program's local
repository. A verdict with a `Fix` commit asks the framework to push it.
Both need `Remote: credentials.Remote`, which reads the repository's
Secret. `generate` grants a program what its packages call, so a check that
reads only the `GitBranch`, such as `check-approval`, leaves `Remote` out,
and its program can't read Secrets.

### Sandboxed checks

The checks that read files run in their controller's process. A check that
runs the branch's code, such as `go test`, runs it in a Pod instead.
`check-gotest` declares one Pod for each head with `kube.Own`, and reports
`Running` until the Pod finishes:

- An init container fetches the head from the repository. It's the only
  container that gets the repository's credentials, as environment
  variables from the Secret.
- The test container runs `go test ./...` as user 65532 with no service
  account token, no privileges, a read-only root file system, and
  `GOPROXY=off`, so tests can't download modules.
- If fetching fails, the check starts a new Pod, up to three times.
- At most `-max-pods` test Pods, 10 by default, run at once across all
  namespaces. A branch that would start another reports `Running` and waits
  until one finishes.

kube deletes a Pod when the check stops declaring it: after the check records
the Pod's result, or when the branch moves to a new head. Owner references
delete the Pods with their `GitBranch`. Set `-runtime-class` to run the Pods
under a sandboxing runtime such as gVisor, and `-go-image`, `-git-image`,
`-timeout`, and `-goproxy` to change the rest.

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
agent Pod. When kube can't create a Pod, the check says so, and the
program's log says why.

The agent's prompt holds the first 200,000 bytes of the diff and lists
every path that the change touches, so the agent can read the files that
the diff leaves out. The check fails a change that touches more than 1,000
paths.

When the policy lets the check push, the agent can also edit the files.
The check commits what changed on the head, and pushes it like any other
fix, with a `Git-K8s-Fixer: review` trailer and within
`maxAutomatedCommits`. A fix leaves `.cursorignore` files as they are. If
a path in the head isn't valid UTF-8, the run fails before the agent
starts. Without `mayPush`, the agent's files are read-only.

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
  including the check's own fixes and `check-base`'s merges of the parent.
  A branch that has used them all reports `Running` until you raise the
  limit.
- `-max-runs-per-day`, 100 by default, is the most runs that the program
  starts in any 24 hours. The program counts them in memory, so the count
  starts over when it restarts, and each shard keeps its own count.
- `-max-pods`, 10 by default, is the most agent Pods that run at once
  across all namespaces.

If the branch moves before the agent's Pod fetches it, the agent doesn't
run, so the run doesn't count toward `maxAgentRuns` or `-max-runs-per-day`,
and the new head starts a run of its own. If the branch's head is the same
a minute later, such as when the branch moved back, the check fetches it
again in a new Pod, which counts as a run.

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
waits for one, but it doesn't count toward `maxAgentRuns`.

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
review:

```sh
docker build -t REGISTRY/agent-runner agent/runner
docker push REGISTRY/agent-runner
image="$(docker inspect -f '{{index .RepoDigests 0}}' REGISTRY/agent-runner)"
go run ./cmd/check-review generate -registry=REGISTRY -base=cgr.dev/chainguard/git:latest -- -agent-image="${image}" | kubectl apply -f -
kubectl -n NAMESPACE create secret generic cursor-api-key --from-literal=api-key=KEY
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
  commit whose replay conflicts, the check replays the branch's whole change
  since `base` as one commit on top of the external repository's head
  instead. Git and the agent resolve that commit's conflicts as they resolve
  a merge's, with `base` as the merge base, and the agent's prompt says not
  to bring back what the rewind removed.
- If the branch rewound in git-k8s, the check replays the external
  repository's commits onto the branch's head one at a time. It pushes the
  result to the side that rewound, so each commit that the external
  repository added needs a replay in it. A replay is a commit that removes
  and adds the same lines in the same files as the original, ignoring the
  unchanged lines around them. A merge commit, and a commit that changes no
  file, have no replay. So the check resolves no conflicts here, and fails
  and leaves the divergence for a person when a commit has no replay or
  doesn't replay unchanged.
- If both sides rewound, the check replays the branch's commits onto the
  external repository's head if that head has none of the commits that the
  branch removed. Otherwise, it replays the external repository's commits onto
  the branch's head if that head has none of the commits that the external
  repository removed. In this case, it never replays the branch's whole
  change as one commit, and fails when neither replay works.

A head keeps a side's changes when it has none of the commits that the side
removed, and has each commit that the side added, or a replay of it if the
head doesn't contain `base`. The check passes when one side's head already
keeps every change that the other side made.

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
check's fix. `resolve/BRANCH` then lands on `BRANCH` through `BRANCH`'s
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
the parent since `base`. If a commit can't be replayed unchanged, for
example because it changes lines that the rewind removed, the parent stays
diverged until the external repository's head contains the parent's head
again. If the parent rewound in git-k8s instead, replay the external
repository's commits onto the parent's head, and push the result to the
external repository with a lease on its head. The check fails, and says
which of these to do, until either side's head keeps every change that the
other side made. Then it passes, because the mirror moves the other side to
that head.

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
conflicts git resolves by keeping the lines of both sides. Its agent Pods
need the NetworkPolicy that `check-review`'s need, with ingress from the
namespace `check-conflicts`.

### Run agents from a controller

A controller, or a check that needs a `Job` that `Run` doesn't build, runs
an agent with `Runner.RunJob`. Its `Job` names the repository, the
Secret with the repository's credentials, the commits to check out, the
task, the agent's tools, and the runner's image if it isn't
`-agent-image`. `Run` builds a `Job` from a check's branch, so both start
the same Pods, within the same `-max-pods` and `-max-runs-per-day` limits.

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
the run back and waits a minute for a `Job` with the new head. While the
run waits, the status's `Moved` is true. If a call after that minute has
the same `Job`, `RunJob` fetches the commits again in a new Pod, which
counts as a run. A run ends after three Pods fail to fetch the commits or
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
kubectl apply -f config/policy.yaml
```

Replace `REGISTRY` with a registry and repository prefix that your cluster
can pull from, such as `ghcr.io/you`. To pass flags to a program, add them
after `--`, as in `go run ./cmd/check-risk generate -registry=REGISTRY -- -sensitive='auth/**'`.

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
gateway, and pushes branches to it. It needs Docker, `kubectl`, and `git`,
and installs kind if it's missing:

```sh
GIT_K8S_KIND_E2E=1 go test -v -count=1 ./e2e/kind/
```

CI runs it when `git-k8s/` or `kube/` changes. To keep the cluster
afterward, set `GIT_K8S_KIND_KEEP=1`. If your network can't reach `cgr.dev`,
set `GIT_K8S_KIND_CHAINGUARD=docker.io/chainguard`.

The end-to-end test builds the agent runner's image with Docker, and runs
`check-review` with the `fake` backend, which needs no API key. The fake
agent fails a change that adds a line with `DO NOT MERGE` in it, and deletes
those lines when the check can push. It runs `check-conflicts` with the
`fake` backend too. There, the fake agent resolves each conflict by keeping
the branch's lines and then the other side's, and fails a conflict with
`DO NOT MERGE` in it.

## Limitations

- The controllers poll remotes; they don't receive webhooks. A check's status
  write runs the repositories controller again, so a check's fix is listed
  soon after the check pushes it. The controller lists a repository at most
  once every 5 seconds, or every `pollInterval` if that's shorter.
- Remotes authenticate with HTTP basic auth only.
- `check-gotest` runs Pods in the `GitBranch`'s namespace and doesn't add a
  NetworkPolicy, so a test can reach anything that the namespace's Pods can.
- `check-review` and `check-conflicts` read repository credentials, so
  `generate` lets them read every Secret, including the Cursor API key,
  which only their agent Pods use. Like `check-gotest`, they can also create
  Pods in every namespace, and `check-conflicts` can even without
  `-agent-image`. Installing them with `generate -watch-namespace` limits
  their Secrets and Pods to one namespace.

[`future-work.md`](future-work.md) proposes fixes for these, and lists the
other known gaps.
