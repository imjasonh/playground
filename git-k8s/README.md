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
```

Replace `REGISTRY` with a registry and repository prefix that your cluster
can pull from, such as `ghcr.io/you`. To pass flags to a program, add them
after `--`, as in `go run ./cmd/check-risk generate -registry=REGISTRY -- -sensitive='auth/**'`.

`config/policy.yaml` holds two ValidatingAdmissionPolicies. The first lets
the service account of `check-NAME` change only `status.checks.NAME`, and
stops every other service account, including the core program's, from
changing `status.checks`. A check that doesn't run as `check-NAME` in the
namespace `check-NAME` needs an entry in the `git-k8s-checks` ConfigMap to
write results. Server-side apply already keeps the controllers' writes
apart; the policy stops a buggy or compromised check from writing another
check's result. The second stops every git-k8s service account from setting
the approve annotation, which is for people, and stops checks from changing
`GitBranch` objects at all.

Without the policies, none of that holds, so the repositories controller
sets a `PoliciesInstalled` condition on each `GitRepository`. It's `False`
until both policies are installed with bindings that deny.

### Admission policies

The core program installs `config/policy.yaml` when it starts, before it
reconciles. It labels the policies, their bindings, and their ConfigMap with
`kube.imjasonh.github.io/managed-by=git-k8s`, and applies them again each
time it starts, but doesn't watch them. The policies name the core program's
service account and keep their ConfigMap in the `git-k8s` namespace, so
install the core program in that namespace, as `generate` does unless you set
`-namespace`.

If a policy or its binding goes missing, `PoliciesInstalled` turns `False`,
and its message says to restart the core program. Only the replica that
holds the leader election lease installs `config/policy.yaml`, so deleting a
standby replica's Pod doesn't install it again. Restart the Deployment:

```sh
kubectl -n git-k8s rollout restart deployment/git-k8s
```

`PoliciesInstalled` also turns `False` when no binding for a policy denies
every request that the policy rejects. A binding can let some of them
through when its `validationActions` doesn't hold `Deny`, when its
`paramRef.parameterNotFoundAction` isn't `Deny`, when its `matchResources`
sets resource rules, or when a selector in its `matchResources` sets
`matchLabels` or `matchExpressions`. The message gives a `kubectl patch`
command that makes the binding from `config/policy.yaml` deny all of them
again, without a restart. For a binding that someone set to `Warn`, the
command is:

```sh
kubectl patch validatingadmissionpolicybinding git-k8s-branches --type=merge \
  -p '{"spec":{"validationActions":["Deny"]}}'
```

A binding set to `Warn` stops the core program the next time that it
starts, whether you restart it or a node drain or an upgrade does. The core
program's apply keeps the entries that others add to a binding's
`validationActions`, so it adds `Deny` next to `Warn`, and the API server
rejects a binding that has both. The core program exits, each replica that
takes the lease after it exits too, and nothing lands until you patch or
delete the binding. `PoliciesInstalled` reports a binding from
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

`generate` grants the core program `create` and `patch` on the two policies,
their bindings, and the `git-k8s-checks` ConfigMap, by name, and `get` on the
ConfigMap, which the bindings name as their parameter. The API server lets
only someone who can read every ConfigMap create a policy whose parameter is
a ConfigMap, and it checks that as `get` on a ConfigMap named `*`. No
ConfigMap can have that name, so `generate` also grants `get` on the name
`*`, and the core program still can't read any other ConfigMap.

The core program can't create other admission policies, but a compromised
core program could rewrite these policies, their bindings, and their
ConfigMap, to weaken them or to deny other requests in the cluster. It
already decides what lands, so it could land a branch without its checks
anyway. To keep the policies out of its reach, for example in a cluster that
manages admission policies separately, install it with
`-install-policies=false`, which also leaves out the permissions, and apply
`config/policy.yaml` yourself:

```sh
go run ./cmd/git-k8s generate -registry=REGISTRY -base=cgr.dev/chainguard/git:latest -- -install-policies=false |
  kubectl apply -f -
kubectl apply -f config/policy.yaml
```

With `-install-policies=false`, the message of a `False` `PoliciesInstalled`
says to apply `config/policy.yaml` instead of restarting the core program.
The core program doesn't apply the manifest when it starts, so a binding set
to `Warn` doesn't stop it, and the condition doesn't report one while another
binding for the same policy denies.

### Check service accounts

The policies recognize a check by the service account that makes each
write. `generate` installs `check-NAME` with the service account
`check-NAME` in the namespace `check-NAME`, and the policies treat that
service account as the check `NAME`. For a check that runs as another
service account, such as a check installed with `generate -namespace=checks`,
add an entry to the `git-k8s-checks` ConfigMap in the `git-k8s` namespace.
Each key is `NAMESPACE.SERVICE_ACCOUNT`, and its value is the check's name:

```sh
kubectl -n git-k8s patch configmap git-k8s-checks --type=merge \
  -p '{"data":{"checks.check-approval":"approval"}}'
```

An entry overrides the `check-NAME` convention, so an entry with an empty
value stops that service account from writing results. The policies ignore
an entry for the core program's service account, `git-k8s.git-k8s`, so an
entry can't let the core program write a result or stop it from changing
`GitBranch` objects. The core program applies the ConfigMap without data, so
restarting it keeps your entries.
Anyone who can change ConfigMaps in the `git-k8s` namespace can decide which
service accounts write which results, so give that permission only to people
who can install checks.

While the ConfigMap is missing, the API server denies every create and update
of a `GitBranch` or its status, including people's, with a message that says
`no params found for policy binding`. To create the ConfigMap again, run
`kubectl -n git-k8s create configmap git-k8s-checks`, or restart the core
program with `kubectl -n git-k8s rollout restart deployment/git-k8s`. With
`-install-policies=false`, apply `config/policy.yaml` instead.

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

- The controllers poll remotes; they don't receive webhooks. A check's status
  write runs the repositories controller again, so a check's fix is listed
  soon after the check pushes it. The controller lists a repository at most
  once every 5 seconds, or every `pollInterval` if that's shorter.
- Remotes authenticate with HTTP basic auth only.
- `check-gotest` runs Pods in the `GitBranch`'s namespace and doesn't add a
  NetworkPolicy, so a test can reach anything that the namespace's Pods can.

[`future-work.md`](future-work.md) proposes fixes for these, and lists the
other known gaps.
