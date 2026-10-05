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

`url` must be an `https://`, `http://`, `git://`, or `ssh://` URL, or an
scp-like address with a user name, such as `git@example.com:app.git`. Without
a user name, write an `ssh://` URL, such as `ssh://example.com/~/app.git`. The
API server rejects other URLs, and git-k8s runs git with `GIT_ALLOW_PROTOCOL`
set to those transports. Its git commands put `--end-of-options` before every
URL, branch, and commit, so git can't read one as an option. git-k8s doesn't
track branches whose names start with `-` or aren't valid ref names.

Put credentials in `secretRef`, not in `url`. `kubectl get gitrepositories`
shows each URL, and `check-gotest` copies it into its Pod specs.

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
in each program. Only commit SHAs go into Kubernetes objects. Apart from
[events](#events), which the API server deletes after an hour by default, no
object records a single push or check run, so the API server holds a bounded
amount of state.

After a branch lands, `kubectl get gitbranches` shows what's still open:

```
NAME                    BRANCH   HEAD                                       PARENT   STATE              AGE
app-c-auth-f684729ccf   c/auth   d28547a6c959905ea8dc037ac37541167a50638c   main     WaitingForChecks   9s
app-main-9157892a7c     main     610a7734a0b4d1bc1991a669d9feb35fd159219b                               48s
```

The `Merged` condition's message explains a `WaitingForChecks` state, for
example `checks: approval Failed, base Passed, gofmt Passed, risk Passed (high)`.

## Events

The controllers record an event about a `GitBranch` each time they change
the remote:

| Reason | From | When |
| --- | --- | --- |
| `PushedFix` | `check-NAME` | A check pushed a fix commit to the branch. |
| `Landed` | `merge` | The merge controller fast-forwarded the parent to the branch. |
| `DeletedBranch` | `merge` | The merge controller deleted the branch after it landed. |

`kubectl describe gitbranch GITBRANCH` lists a branch's events. After the
merge controller deletes a branch, the repositories controller deletes its
`GitBranch`, so list the namespace's events instead:

```sh
kubectl get events --sort-by=.metadata.creationTimestamp
```

After `c/fmt` in the end-to-end test lands, the output looks like this:

```
LAST SEEN   TYPE     REASON          OBJECT                           MESSAGE
14s         Normal   PushedFix       gitbranch/app-c-fmt-793d86522b   pushed 5d0c2e9a71b4 to c/fmt: 1 of 2 Go files need gofmt: util/add.go
9s          Normal   Landed          gitbranch/app-c-fmt-793d86522b   fast-forwarded main from 0e4f8a2c9d13 to c/fmt at 5d0c2e9a71b4
9s          Normal   DeletedBranch   gitbranch/app-c-fmt-793d86522b   deleted c/fmt at 5d0c2e9a71b4 after it landed on main
```

kube drops events when it falls behind on writing them, and the API server
deletes events after an hour by default. To audit what landed, use the
remote's history. `generate` grants `create` and `patch` on events to the
`git-k8s` program and to every check program. A check that never pushes a
fix, such as `check-approval`, gets the grant too, because the `checks`
package that every check uses records `PushedFix`.

## Checks

| Program | Check | What it does |
| --- | --- | --- |
| `check-base` | `base` | Passes when the branch contains its parent's head, or the parent already contains the branch. Otherwise it merges the parent in with `git merge-tree`, and fails with the conflicting paths if the merge conflicts. |
| `check-gofmt` | `gofmt` | Formats every `.go` file outside `vendor` and `testdata` directories with `go/format`, and passes when nothing changes. |
| `check-risk` | `risk` | Always passes, and sets `outputs.level` to `high` when the change is larger than `-max-lines` or touches a path that matches a `-sensitive` glob, and to `low` otherwise. |
| `check-approval` | `approval` | Passes when the `git-k8s.imjasonh.com/approve` annotation on the `GitBranch` names the branch's head, and sets `outputs.approver` to the `git-k8s.imjasonh.com/approved-by` annotation. A push after the approval needs a new one. See [Approve a branch](#approve-a-branch). |
| `check-gotest` | `gotest` | Runs `go test ./...` in a Pod that it declares with `kube.Own`, and fails with the end of the test output. See [Sandboxed checks](#sandboxed-checks). |

A check with `mayPush: true` pushes its fix commit to the branch, which moves
the head and runs the checks again. Fix commits have a `Git-K8s-Fixer:
CHECK` trailer, and `maxAutomatedCommits` (default 5) limits how many a
branch can have, so two checks that undo each other's fixes stop. The same
inputs always produce the same fix commit, so two retries of one fix push the
same commit.

### Approve a branch

An approval is two annotations on the `GitBranch`: `approve`, which names
the commit, and `approved-by`, which names you. Set both in one request:

```sh
kubectl annotate --overwrite gitbranch GITBRANCH git-k8s.imjasonh.com/approve=SHA \
  git-k8s.imjasonh.com/approved-by="$(kubectl auth whoami -o jsonpath='{.status.userInfo.username}')"
```

The `git-k8s-approvals` policy in `config/policy.yaml` enforces these rules:

- Setting, changing, or removing the `approve` or `approved-by` annotation
  requires the `approve` verb on the `GitBranch`. `generate` grants that
  verb to no program, so grant it to the people who approve:

  ```sh
  kubectl create role approver --verb=get,list,watch,patch,approve --resource=gitbranches.git-k8s.imjasonh.com
  kubectl create rolebinding approver --role=approver --group=GROUP
  ```

- A request that sets or changes `approve` must set `approved-by` to the
  username that sends it.
- A request that removes `approve` must remove `approved-by` too.
- A request that changes only `approved-by` takes over the approval, so
  `approve` must name a commit, and the request must set `approved-by` to
  the username that sends it.

On Kubernetes 1.36 or later, `kubectl apply -f config/approved-by.yaml`
installs a MutatingAdmissionPolicy that sets `approved-by` to your username
when you set or change `approve`, and removes it when you remove `approve`,
so one annotation approves:

```sh
kubectl annotate --overwrite gitbranch GITBRANCH git-k8s.imjasonh.com/approve=SHA
```

The mutating policy leaves `approved-by` alone when the request changes it
as well, and `git-k8s-approvals` checks every approval either way.

To take over an existing approval of the same commit, set both annotations
as in the first command. Setting only `approve` leaves that approval and its
`approved-by` as they are. Admission policies see only the object that a
request produces, so the mutating policy can't tell that the request set
`approve` again. `check-approval` reports the new approver after a takeover.

`check-approval` reports `approved-by` as `outputs.approver`, so a merge gate
can require particular approvers:

```yaml
when: >-
  checks.approval.passed &&
  checks.approval.outputs.approver in ["alice@example.com", "bob@example.com"]
```

An approval without `approved-by`, such as one from before the policy was
installed, still passes with an empty `outputs.approver`, so the branch waits
at a gate like this one until someone approves it again.

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
A `Fixed` result also has the output `fix`, so a verdict with a `Fix` can
have at most 15 other outputs, or the framework reports `Error` and doesn't
push the fix. The framework shortens messages and output values to 1,024
bytes, the most that the core program accepts.

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

Both of a test Pod's containers meet the `restricted`
[Pod Security Standard](https://kubernetes.io/docs/concepts/security/pod-security-standards/).
An admission policy keeps `check-gotest` to its own Pods, in namespaces that
opt in to test Pods and enforce the `restricted` standard. See
[Install](#install).

## Check results

Only the core program writes `status.checks`. A check sends each new result
to the core program's results endpoint:

1. The check reads the token that `generate` mounts in its Pod: a token for
   the check's service account with the audience `git-k8s-results`, which
   the kubelet renews before it expires.
2. It sends the result and the token in a `PUT` request to
   `RESULTS_URL/NAMESPACE/GITBRANCH/CHECK`. `RESULTS_URL` is the check's
   `-results-url` flag, `http://git-k8s.git-k8s.svc/results` by default. The
   request also names the `GitBranch` generation that the check read, and
   the core program waits until its cache has the `GitBranch` at that
   generation.
3. The core program verifies the token with a TokenReview for that
   audience, and maps the token's service account to a check. `generate`
   installs each check with the service account `check-NAME` in the
   namespace `check-NAME`, which maps to the check `NAME`. If that check
   isn't `CHECK`, the core program rejects the result.
4. The core program also rejects a result for a check that the branch's
   merge policy doesn't list, a result that isn't for the branch's current
   commits, a `Pending` result, and a result over its size limits. The
   `checks` package sends an `Error` result instead of one with a state or
   size that the core program rejects, with a message that says why. The
   core program drops fields that it doesn't know, as the API server does
   by default.
5. The core program holds the result in memory and starts a reconcile of
   the `GitBranch`. The results controller writes the result with
   server-side apply, and the core program answers the request once its
   cache shows the result.

Only one replica of the core program writes a branch's results. With the two
replicas that `generate` runs by default, that's the replica that holds the
leader lease. If another replica gets the request, or the result isn't written
within 10 seconds, the core program answers `503 Service Unavailable` and
closes the connection, and the check tries again on a new connection. If 10
tries fail, the check's reconcile fails, and kube retries it, which runs the
check again. kube-proxy's iptables and nftables modes send each connection to
a replica at random, so with N replicas, all 10 tries miss the one that
writes the branch's results with probability `((N-1)/N)^10`. That's about 1
in 1,000 with two replicas, 1 in 58 with three, and 1 in 9 with five.

If the branch changed since the check read it, the core program answers
`409 Conflict`, and the check drops the result, because the change runs the
check again. If the core program rejects the result with `400 Bad Request`,
or the token's service account with `403 Forbidden`, the check logs why and
sends nothing more for that branch until the branch changes or the check
restarts.

### Security model

The results endpoint and the `git-k8s-check-results` admission policy keep
each check's service account to its own entry in `status.checks`.
`generate` grants a program what its packages call, so a check's RBAC rules
include nothing for `gitbranches/status`. They don't let a check create
tokens either, because the check reads the token that `generate` mounts in
its Pod. The core program writes only the entry of the check that the
token's service account runs, so one check's token can't write another
check's entry. The policy is a backstop. It rejects status writes by checks,
and changes to `status.checks` by service accounts other than the core
program's, even when a role grants them status access. See
[Install](#install).

Neither stops a check that creates Pods from running a Pod as another
service account, and no admission policy in this release does.
`check-gotest` runs tests in Pods, so `generate` grants it permission to
create, patch, and delete Pods in every namespace. It can run a Pod as
another check's service account and mount a `git-k8s-results` token that the
core program accepts as that check's. It can also run a Pod as the core
program's service account, which writes every check's result. Anyone else
who can create Pods in a check's namespace or in the `git-k8s` namespace can
do the same.

The tokens have the audience `git-k8s-results`, so a token sent to the core
program can't call the API server, and a token for the API server can't send
results. The endpoint uses plain HTTP inside the cluster, so anything that
can read the traffic between Pods can copy a token and send that check's
results until the token expires, within an hour, or the check's Pod is
deleted.

kube doesn't fence writes, and the results controller writes all of
`status.checks` at once, so a replica that hasn't noticed that its leader
lease expired can put back earlier results. Checks other than `approval` run
again on an earlier result, which is for earlier commits or isn't final. If
someone removed the approve annotation, though, the replica can put back
`approval`'s `Passed` result until `check-approval` sends `Failed` again, and
the merge controller can merge the branch in that window.

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

`generate` also writes a Service for the core program, which routes port 80
to the results endpoint on port 8081 of each replica, and mounts a token for
the audience `git-k8s-results` in each check's Pod. The core program's
container waits 5 seconds before it stops, so that the Service stops sending
it results first. That wait needs Kubernetes 1.30 or later. If
NetworkPolicies in the `git-k8s` namespace deny traffic by default, let the
checks' Pods reach port 8081 of the core program's Pods.

`config/policy.yaml` holds four ValidatingAdmissionPolicies. The first
rejects every write to `GitBranch` status by a check's service account, and
every change to `status.checks` by a service account other than the core
program's. Checks have no RBAC rule to write status, so this policy is a
backstop for a role that grants one by mistake. The second stops every
git-k8s service account from setting the `approve` and `approved-by`
annotations, which are for people, and stops checks from changing
`GitBranch` objects at all. RBAC also keeps every check except
`check-gotest`, which owns the Pods that run tests, from patching
`GitBranch` objects. `generate` grants that permission to a check that owns
objects, because it can't tell whether an owned object needs a finalizer on
its owner. The second policy denies the annotation that kube adds with that
finalizer, so a check can own only namespaced objects in the branch's
namespace. The first two policies identify the core program and the checks
by the service accounts that `generate` installs them with: `git-k8s` in
the namespace `git-k8s`, and `check-NAME` in the namespace `check-NAME`.

The third keeps each check to its own Pods. `generate` lets a check that
declares Pods with `kube.Own`, such as `check-gotest`, create, patch, and
delete Pods in every namespace, because RBAC can't limit those verbs to the
Pods that a program created. kube labels each Pod that `check-NAME` declares
with `kube.imjasonh.github.io/controller=check-NAME`. The policy lets the
check change or delete only Pods with that label, and its new Pods must have
it. A new Pod's name must be `NAME-ID`, where `ID` has no hyphens, so that a
check can't take the name of another check's next Pod and block it. The check
can't write Pods in the `git-k8s` or `check-*` namespaces. Elsewhere, it
creates and changes Pods only in namespaces that have the label
`git-k8s.imjasonh.com/check-pods=true` and enforce the `restricted` Pod
Security Standard at version `latest`. It can delete its Pods in a namespace
without those labels, so it can clean up after a namespace drops them. Its
Pods must run as their namespace's `default` service account, and a new Pod
can't set `spec.nodeName`.

The policy itself enforces the `baseline` Pod Security Standard, more strictly
for capabilities and sysctls. It denies these fields in containers, init
containers, and ephemeral containers:

- The node's network, PID, and IPC namespaces
- `hostPath` volumes and host ports
- Privileged containers and added capabilities
- An unmasked `/proc`, the `Unconfined` seccomp profile, and Windows host
  processes
- The `Unconfined` AppArmor profile, SELinux users and roles, SELinux types
  other than the container types that `baseline` allows, and sysctls
- Probes and lifecycle handlers that set `host`, which make the kubelet
  connect from the node to another address

Pod Security admission enforces the rest of `restricted`, such as running as
a non-root user. An exemption in the cluster's Pod Security admission
configuration that covers a check's Pods, by user, RuntimeClass, or
namespace, weakens only that rest. The policy doesn't limit node selectors,
affinity, tolerations, or `runtimeClassName`, so a compromised check can
schedule Pods onto any node, including tainted ones, and start them without
the RuntimeClass that `-runtime-class` sets. To require that RuntimeClass,
add a ValidatingAdmissionPolicy that denies a Pod with the label
`kube.imjasonh.github.io/controller=check-gotest` unless its
`spec.runtimeClassName` is the RuntimeClass.

The policy matches every service account whose namespace or name starts with
`check-`. Of those, only `check-NAME` in the namespace `check-NAME`, as
`generate` installs the `NAME` check, can write Pods. Any other, such as an
unrelated service account named `check-deployer`, can't write Pods at all. A
check that runs as another service account needs a policy of its own. If that
policy reads parameters, its binding must set
`parameterNotFoundAction: Allow`. The API server looks up a binding's
parameters before it evaluates the policy's match conditions, so with `Deny`,
every Pod write in the cluster fails while the parameters are missing.

In a namespace that opts in, a compromised check's Pods can still mount the
namespace's Secrets, ConfigMaps, and PersistentVolumeClaims, run as its
`default` service account, and mount tokens for that account with any
audience. A service that accepts those tokens must check which Pod a token is
bound to, and that the Pod has the label of the check that the service
trusts.

The fourth checks who approves, as [Approve a branch](#approve-a-branch)
describes.

Without the policies, most of that doesn't hold, so the repositories
controller sets a `PoliciesInstalled` condition on each `GitRepository`. It's
`False` until all four policies are installed with bindings that deny. It's
also `False` while a policy's `git-k8s.imjasonh.com/policy-version`
annotation isn't the version that the core program expects. If the
annotation is missing, isn't a number, or is an earlier version, as with the
policies of an earlier release, the reason is `Outdated`, and the message
says to apply `config/policy.yaml` from the core program's release. If it's a
later version, as with the policies of a later release, the reason is
`Newer`, and the message says to upgrade the core program or, if you rolled
it back, to apply `config/policy.yaml` from its release. The core program
can't tell a rollback from an upgrade that applies the policies first.

Each namespace that holds a `GitRepository` whose merge policy lists `gotest`
must opt in to test Pods and enforce the `restricted` Pod Security Standard,
or the third policy denies the test Pods:

```sh
kubectl label namespace NAMESPACE git-k8s.imjasonh.com/check-pods=true pod-security.kubernetes.io/enforce=restricted
```

Replace `NAMESPACE` with the namespace of the `GitRepository`. The namespace
can't be `git-k8s` or start with `check-`. If it has the label
`pod-security.kubernetes.io/enforce-version`, the label's value must be
`latest`. Until the namespace has both labels, the branch's `gotest` result
stays `Running`, and its message says why kube couldn't create the Pod. kube
tries again with backoff that grows to 5 minutes, plus up to 10% jitter, so it
creates the Pod within about 5.5 minutes after you label the namespace,
without a new push.

If `check-gotest` already runs, label the namespaces of its repositories
before you apply `config/policy.yaml`. Otherwise the policy denies their test
Pods until you do.

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
step 1 is installed first. While the earlier policy is installed, the core
program reports `PoliciesInstalled` as `False` with the reason `Outdated`.
The results controller takes over a branch's results the first time it
writes them, and server-side apply then removes the old checks from the
branch's managed fields.

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
