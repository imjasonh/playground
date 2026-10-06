# git-k8s stress harness

The stress harness measures how many branches git-k8s lands per minute, and
how long each branch takes from push to landing. It runs against a kind
cluster with git-k8s, `go-cache`, and the `base`, `gofmt`, `risk`,
`approval`, and `gotest` checks installed with their production settings. A
scenario pushes a burst of branches to a git
server on your machine and plays their developers and reviewer: it pushes
fixes for failing tests, merges `main` into conflicting branches to resolve
the conflicts, and approves high-risk heads. The harness records how each
branch moves through the checks and the merge queue, and then verifies what
landed.

A scenario takes minutes and loads the whole machine, so CI doesn't run
scenarios. CI runs the harness's unit tests with the rest of the module's
tests; they don't need a cluster.

## Before you begin

You need the following:

- A Linux machine with Docker, [kind](https://kind.sigs.k8s.io/), `kubectl`,
  and `git`.
- The Go version in `git-k8s/go.mod`.
- For CPU numbers, cgroup v2, which Docker uses on most current Linux
  distributions. Without it, a run notes that it isn't recording CPU.
- For PNG charts, Chrome or Chromium. Without either, pass `-png=false` to
  `chart` to write only SVG files.

`setup.sh` pulls `registry:2`, kind's node image, and Chainguard's `git`,
`go`, and `static` images, and runs `crane` with `go run`. To set up without
internet access, see `GK_STRESS_DOCKER_IMAGES` in
[Setup options](#setup-options).

## Set up the cluster

From the `git-k8s` directory, run the following:

```bash
export GK_STRESS_STATE=/tmp/gk-stress
bash e2e/stress/setup.sh
```

`setup.sh` starts the following, and leaves them running when it exits:

- A registry container on `127.0.0.1:5300`.
- A kind cluster with one node.
- A git server on your machine, which holds the scenarios' repositories in
  place of GitHub. Pods reach it through the kind network's gateway.
- A module proxy on your machine, which is `go-cache`'s upstream. It serves
  only `example.com/greet`, the one module that test repositories use besides
  the standard library.

It builds git-k8s, `check-base`, `check-gofmt`, `check-risk`,
`check-approval`, `check-gotest`, and `go-cache` from your checkout with each
program's `generate` command, and installs them with their default replicas
and flags. It writes what the harness needs to `$GK_STRESS_STATE/env`, and
prints the images that it installed, by digest.

Only the following differ from a production install:

- The programs' images come from the local registry, and `setup.sh` builds
  them for your machine's platform only.
- The external repositories are on your machine, so fetches and pushes have
  no network latency.
- `go-cache` gets modules from the local module proxy instead of
  `proxy.golang.org`.

To measure a change, run `setup.sh` again from the checkout that has the
change, with the same `GK_STRESS_STATE`. It builds and installs the programs
from the checkout that you run it from, and reuses the git server, the module
proxy, and the git server's password from the state directory. Each run
records the Deployments' images, so you can confirm which build a run
measured.

### Setup options

`setup.sh` reads the following environment variables:

| Variable | Default | Description |
| --- | --- | --- |
| `GK_STRESS_STATE` | `/tmp/gk-stress` | The directory for the env file, logs, binaries, the git server's repositories, and runs. |
| `GK_STRESS_CLUSTER` | `gk-stress` | The kind cluster's name. |
| `GK_STRESS_REGISTRY` | `gk-stress-registry` | The registry container's name. |
| `GK_STRESS_REGISTRY_PORT` | `5300` | The registry's port on `127.0.0.1`. |
| `GK_STRESS_GIT_PORT` | `18700` | The git server's port. |
| `GK_STRESS_CHAINGUARD` | `cgr.dev/chainguard` | Where Chainguard's images come from. If your network can't reach `cgr.dev`, set it to `docker.io/chainguard`. |
| `GK_STRESS_DOCKER_IMAGES` | Not set | If `1`, `setup.sh` copies Chainguard's images into the registry with Docker instead of `crane`, and takes them from Docker's local cache when the cache has them. Setup then works without internet access if Docker has those images, `registry:2`, and kind's node image. It needs a Docker version whose `docker push` has the `--platform` flag. |
| `GK_STRESS_NXDOMAIN` | Not set | If `1`, `setup.sh` configures CoreDNS to answer every name outside the cluster with NXDOMAIN. Set it only on a machine whose DNS server doesn't answer. On such a machine, every git command that a check or test Pod runs against the mirror waits about 4 seconds for a DNS lookup to time out, and those waits swamp the measurements. |

### Compare two builds side by side

To compare two checkouts, give each setup its own state directory, cluster,
registry, and ports, and run `setup.sh` from each checkout. For example, for
the second setup:

```bash
export GK_STRESS_STATE=/tmp/gk-stress-b GK_STRESS_CLUSTER=gk-stress-b
export GK_STRESS_REGISTRY=gk-stress-b-registry GK_STRESS_REGISTRY_PORT=5301 GK_STRESS_GIT_PORT=18701
bash e2e/stress/setup.sh
```

The `run`, `verify`, and `cleanup` commands use the setup that
`GK_STRESS_STATE`, or their `-state` flag, names. Run scenarios against one setup at a time, so that they
don't compete for CPU, and alternate between the setups.

## Run a scenario

From the `git-k8s` directory, run the following:

```bash
go run ./e2e/stress run -scenario clean
```

Each scenario gets its own namespace with one or more GitRepository objects.
Each one's `main` policy has the `base`, `gofmt`, `risk`, `approval`, and
`gotest` checks. A branch lands when `base`, `gofmt`, and `gotest` pass, and
either `risk` rates it low or `approval` passes. The policy lets `base` and
`gofmt` push, which gives it a merge queue, and sets `deleteMergedBranches`.
The GitRepositories poll every 2 seconds.

Before the burst, the harness lands one branch in each repository to warm the
caches. After the burst, it waits for the landings to reach the git server,
verifies the result, saves the cluster's state and the programs' logs, and
analyzes the run. If verification finds a problem, the command exits with an
error after it writes the run's summary.

| Scenario | Branches |
| --- | --- |
| `clean` | `-n` branches (default 20) that each add a file and its test. |
| `mixed` | 24 branches. 7 are unformatted, and `gofmt` fixes them. 2 have failing tests, and the harness pushes fixes. 2 pairs conflict, and after one branch of a pair lands, the harness merges `main` into the other and resolves the conflict. 2 are high risk, one that adds more than 200 lines and one that adds a module to `go.mod`, and the harness approves them. The other 9 are clean. With `-n`, the counts scale. |
| `landing` | 10 branches with three commits each in a repository that lands with `Rebase`, and 10 more in one that lands with `Squash`. |
| `parallel` | `-repos` repositories (default 4) with `-n` branches each (default 10). |
| `nogotest` | `clean` without the `gotest` check. |
| `big` | `clean` with 100 branches and a 120-minute timeout. |
| `poll30` | 8 clean branches, pushed 7 seconds apart, to a repository without `gotest` that polls every 30 seconds, the default. |

`run` has the following flags:

| Flag | Default | Description |
| --- | --- | --- |
| `-scenario` | `clean` | The scenario to run. |
| `-n` | The scenario's | Branches per repository. |
| `-repos` | The scenario's | Repositories, for `clean`, `nogotest`, `big`, and `parallel`. |
| `-poll` | `2s` | Each GitRepository's `pollInterval`. `default` leaves it out, for the 30-second default. `poll30` always leaves it out. |
| `-stagger` | The scenario's | The time between first pushes. Only `poll30` staggers them by default. |
| `-approve-delay` | `15s` | How long the reviewer waits before it approves a high-risk head. |
| `-timeout` | `45m`, or `120m` for `big` | How long the burst can take. |
| `-warmup` | `true` | Whether to land one branch in each repository before the burst. |
| `-out` | `$GK_STRESS_STATE/runs/SCENARIO-TIME` | The run's directory. `report` and `chart` label each run with its directory's name. |
| `-state` | `$GK_STRESS_STATE`, or `/tmp/gk-stress` | The directory that `setup.sh` wrote. |

A scenario's namespace stays after the run, and its GitRepositories keep
polling the git server. Before the next run, delete earlier scenarios'
namespaces:

```bash
go run ./e2e/stress cleanup
```

## Read a run

A run writes the following to its directory:

- `summary.md` and `summary.json`: the measurements, described later in this
  section, and the verification result.
- `timeline.txt`: what happened, in seconds after the first push.
- `log.jsonl`: every record that the harness took. It has the changes to
  GitBranches, Pods, and Events that the harness watched, the refs on the git
  server, CPU samples every second, the programs' metrics every 10 seconds,
  and the harness's own actions.
- `plan.json`: the scenario's repositories and branches.
- `branches.tsv` and `fronts.tsv`: one row per branch, and one per landing
  from a busy queue.
- `graph-REPO.txt`: `git log --graph` of each repository's `main` on the git
  server, with each commit's `Git-K8s-Fixer` trailer.
- `verify.json`: what verification checked, and the problems that it found.
- `images.txt`: each Deployment's image, by digest.
- `gitobjects.yaml` and `pods.txt`: the GitRepositories, GitBranches, and
  Pods at the end.
- `logs/`: the logs of git-k8s and each check since the scenario started,
  with Kubernetes's timestamps.
- `work/`: the harness's clones of the repositories.

`summary.md` has these measurements, among others:

| Measure | Description |
| --- | --- |
| Drain | The time from the first push to the last landing. |
| Landings per minute | Overall, from the first landing to the last, and over the middle 80% of landings. |
| Push to landed | Each branch's time from its first push to its landing. "Where each branch's time went" splits it into pickup, checks, time in the queue behind other branches, and time at the front. |
| Busy cycle | The time from one landing to the next in a repository whose queue already had the next branch. A queue lands one branch per busy cycle, so this time limits its throughput. "Front of the queue" splits it into the base merge, the checks, and the landing, and times the test Pod's containers. |
| Test Pods | How many test Pods ran, and how many at once. |
| CPU | The kind node's CPU, by group, and the host's. |
| Results that waited for the endpoint's timeout | Check reconciles that failed after the results endpoint's 10-second wait, which holds one of the check's workers. |
| Results for deleted branches | The results endpoint's `410 Gone` answers for branches that landed and went away before their checks finished. |
| Verification | Every planned branch landed, `main` has the expected files, `gofmt -l` and `go test ./...` pass on `main`, each landing passed the gate, each high-risk branch landed with an approval of its landed head, and each commit that a check pushed has a `Git-K8s-Fixer` trailer. |

To summarize a run again from its records, for example after you change the
analysis, run the following:

```bash
go run ./e2e/stress analyze RUN_DIR...
```

To verify a run again, run `go run ./e2e/stress verify RUN_DIR...`. It needs
the git server and module proxy of the setup that ran the scenario.

## Compare runs

To compare runs, write a report and charts from their directories:

```bash
go run ./e2e/stress report -out report.md RUN_DIR...
go run ./e2e/stress chart -out charts RUN_DIR...
```

Replace `RUN_DIR` with one or more run directories, in the order that you
want in the tables and legends.

`report` writes two tables with a row for each run. The first has throughput,
latency by phase, the busy cycle, work, and node CPU. The second has the
git-k8s image's digest, errors, the waits for the results endpoint, the
`410 Gone` answers, and the host's CPU, so that you can tell which build ran
and how busy the machine was.

`chart` writes `landings.svg`, with every run's cumulative landings, and
`queue-depth.svg`, with every run's branches in merge queues. For each run,
it writes `RUN-queue.svg`, with each repository's queue and the running test
Pods, and `RUN-cpu.svg`, with the kind node's CPU by group. It also writes a
PNG file of each chart with headless Chrome or Chromium. Without either, it
writes only the SVG files and exits with an error; to skip the PNG files,
pass `-png=false`.

## Caveats

- The control plane, git-k8s, the checks, and the test Pods all run on one
  kind node. They share your machine's CPUs with each other and with anything
  else that runs on the machine, such as other kind clusters. Busy cycles get
  longer when test Pods compete for CPU. Compare runs only when the host CPU
  row shows similar load from outside the node.
- The git server and module proxy run on your machine, so fetches, pushes,
  and module downloads take less time than they do against GitHub and
  `proxy.golang.org`.
- The test repositories are small, and their tests take milliseconds, so a
  test Pod's time is mostly starting containers, fetching, and building.
- Kubernetes records container start and finish times in whole seconds, so
  the test Pod table has whole seconds too.
- Landing order and timing depend on when polls and checks happen to run, so
  the same scenario varies by several seconds from run to run. To compare two builds, run their scenarios back to
  back on the same machine, and run each scenario more than once.

## Clean up

To delete scenario namespaces, run `go run ./e2e/stress cleanup`. To stop
everything that `setup.sh` started, run the following:

```bash
bash e2e/stress/teardown.sh
```

`teardown.sh` stops the git server and module proxy, and deletes the kind
cluster and the registry container. It leaves the state directory, with its
runs and logs.

## Test the harness

The harness's unit tests don't need a cluster:

```bash
go test ./e2e/stress
```
