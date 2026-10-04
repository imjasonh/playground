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

The core program, `git-k8s`, runs three controllers and an endpoint that
accepts check results. Each check runs as its own program. Every controller
is a `kube.For` reconciler:

- The **repositories** controller lists each repository's branches with
  `git ls-remote` and declares a `GitBranch` for each tracked branch with
  `kube.Own`. The spec holds the branch's head, its parent's head, and the
  parent's merge policy. When a branch disappears from the remote, kube
  deletes its `GitBranch`, because the reconcile stops declaring it. A remote
  can't be watched, so the controller asks to run again after `pollInterval`.
- Each **check** controller reconciles a view of `GitBranch` without a
  status, so it can't write status. It reads its last result through a view
  that declares only its own entry in `status.checks`, so it never sees
  another check's result. It sends each new result to the core program.
  Results record the commits they're for, and the merge controller ignores
  results for older commits.
- The **results** controller writes check results to `status.checks`. Each
  result goes to the entry of the check that sent it. See
  [Check results](#check-results).
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
`status.checks`. The framework reads the check's last result through the
view, and sends each new result to the core program. This `main` package,
next to the others in `cmd/`, is a complete check that fails branches
without a `README.md`:

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

The core program accepts at most 16 outputs, with names of up to 63 bytes.
The framework shortens messages and output values to 1,024 bytes, the most
that the core program accepts.

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

## Check results

Only the core program writes `status.checks`. A check sends each new result
to the core program's results endpoint:

1. The check gets a token for its service account with the audience
   `git-k8s-results`, and reuses it until 10 minutes before it expires.
2. It sends the result and the token in a `PUT` request to
   `RESULTS_URL/NAMESPACE/GITBRANCH/CHECK`. `RESULTS_URL` is the check's
   `-results-url` flag, `http://git-k8s.git-k8s.svc/results` by default. The
   request also names the `GitBranch` generation that the check read, and
   the core program waits until its cache has that generation.
3. The core program verifies the token with a TokenReview for that
   audience, and maps the token's service account to a check. `generate`
   installs each check with the service account `check-NAME` in the
   namespace `check-NAME`, which maps to the check `NAME`. If that check
   isn't `CHECK`, the core program rejects the result.
4. The core program also rejects a result for a check that the branch's
   merge policy doesn't list, a result that isn't for the branch's current
   commits, a `Pending` result, and a result over its size limits.
5. The core program holds the result in memory and starts a reconcile of
   the `GitBranch`. The results controller writes the result with
   server-side apply, and the core program answers the request after the
   write.

Only one replica of the core program writes a branch's results. With the two
replicas that `generate` runs by default, that's the replica that holds the
leader lease. If another replica gets the request, or the result isn't written
within 10 seconds, the core program answers `503 Service Unavailable`, and the
check tries again. If 10 tries fail, the check's reconcile fails, and kube
retries it, which runs the check again. If the branch changed since the check
read it, the core program answers `409 Conflict`, and the check drops the
result, because the change runs the check again.

### Security model

A check can't write another check's result, because it can't write
`GitBranch` status at all. `generate` grants a program what its packages
call, so a check's RBAC rules let it create tokens for its own service
account, and include nothing for `gitbranches/status`. The core program
writes only the entry of the check that the token's service account runs,
so one check's token can't write another check's entry.

The tokens have the audience `git-k8s-results`, so a token sent to the core
program can't call the API server, and a token for the API server can't send
results. The endpoint uses plain HTTP inside the cluster, so anything that
can read the traffic between Pods can copy a token and send that check's
results until the token expires, within an hour.

The `git-k8s-check-results` admission policy is a backstop. It rejects
status writes by checks, and changes to `status.checks` by service accounts
other than the core program's, even when a role grants them status access.
See [Install](#install).

### Write a result by hand

The results endpoint accepts only checks' tokens. People who can patch
`gitbranches/status` can write a result directly instead, for example to
unblock a branch whose check is broken:

```sh
kubectl patch gitbranch GITBRANCH --subresource=status --type=merge \
  -p '{"status":{"checks":{"gotest":{"commit":"SHA","state":"Passed","message":"passed by hand"}}}}'
```

Replace `GITBRANCH` with the name of the `GitBranch` object, and `SHA` with
the branch's head. Checks other than `approval` don't run again on commits
that already have a `Passed`, `Failed`, or `Fixed` result, so the result
stays until the branch moves. For a check whose result depends on the
parent, such as `base`, also set `parentCommit` to the parent's head.

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
kubectl apply -f config/policy.yaml
for program in git-k8s check-base check-gofmt check-risk check-approval check-gotest; do
  go run "./cmd/${program}" generate -registry=REGISTRY -base=cgr.dev/chainguard/git:latest | kubectl apply -f -
done
```

Replace `REGISTRY` with a registry and repository prefix that your cluster
can pull from, such as `ghcr.io/you`. To pass flags to a program, add them
after `--`, as in `go run ./cmd/check-risk generate -registry=REGISTRY -- -sensitive='auth/**'`.

`config/policy.yaml` holds two ValidatingAdmissionPolicies. The first
rejects every write to `GitBranch` status by a check's service account, and
every change to `status.checks` by a service account other than the core
program's. Checks have no RBAC rule to write status, so this policy is a
backstop for a role that grants one by mistake. The second stops every
git-k8s service account from setting the approve annotation, which is for
people, and stops checks from changing `GitBranch` objects at all. kube lets
each controller patch the type that it reconciles, so without the second
policy, a check can approve a branch.

The policies identify the core program and the checks by the service
accounts that `generate` installs them with: `git-k8s` in the namespace
`git-k8s`, and `check-NAME` in the namespace `check-NAME`. The repositories
controller sets a `PoliciesInstalled` condition on each `GitRepository`.
It's `False` until both policies are installed with bindings that deny.

### Upgrade from checks that write status

If your installed checks write their own results to `GitBranch` status, as
each did before the results endpoint, upgrade in this order, which the
commands in [Install](#install) follow:

1. Apply `config/policy.yaml`. The earlier policy stops the core program
   from writing results, and this one rejects the installed checks' status
   writes, so branches get no new results until step 3.
2. Install the core program. It changes `status.checks` in the `GitBranch`
   CustomResourceDefinition to an atomic map, which one field manager
   writes as a whole, and starts the results endpoint.
3. Install the checks. They lose their RBAC rule for `gitbranches/status`,
   and send their results to the core program.

After step 2, a status write from an old check replaces all of
`status.checks` with that check's entry, so make sure that the policy from
step 1 is installed first. The results controller takes over a branch's
results the first time it writes them, and server-side apply then removes
the old checks from the branch's managed fields.

## Test

The unit tests call each reconciler with `kube.Fake` and a real git server
that runs in the test process:

```sh
go test -race ./...
```

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

## Limitations

- The controllers poll remotes; they don't receive webhooks. Writing a
  check's result runs the repositories controller again, so a check's fix is
  listed soon after the check pushes it. The controller lists a repository
  at most once every 5 seconds, or every `pollInterval` if that's shorter.
- Remotes authenticate with HTTP basic auth only.
- `check-gotest` runs Pods in the `GitBranch`'s namespace and doesn't add a
  NetworkPolicy, so a test can reach anything that the namespace's Pods can.

[`future-work.md`](future-work.md) proposes fixes for these, and lists the
other known gaps.
