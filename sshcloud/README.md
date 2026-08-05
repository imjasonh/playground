# sshcloud — SSH App Cloud

Platform services for an SSH-only PaaS: users `ssh foo.com` to join or pick an
app; apps speak SSH on `:22` and run in Firecracker microVMs.

Design: [`docs/ssh-app-cloud-design.md`](../docs/ssh-app-cloud-design.md).

> **Prototype safety boundary:** this branch is suitable for local/KVM and
> CIDR-restricted GCP smoke tests. It is not ready for public self-service.
> Jailer-grade VMM isolation, workload identity/mTLS, optional audited egress,
> hard-host-loss policy, and broader OCI runtime compatibility remain open.

## Layout

| Path | Role |
|------|------|
| `cmd/gateway` | Public SSH entry (join, menu, deploy, proxy) |
| `cmd/agent` | Host agent: Firecracker lifecycle + HTTP API |
| `cmd/guestinit` | Tiny guest PID 1 trampoline (OCI entrypoint/cmd/env/workdir) |
| `cmd/fortune` | Sample SSH app — deploy as a normal digest-pinned OCI image |
| `cmd/mkrootfs` | Optional offline ext4 builder (test/dev; not the deploy path) |
| `cmd/ocirootfs` | Materialize digest-pinned OCI image → cached ext4 |
| `cmd/orchestrator` | Placement + cross-host migrate HTTP API |
| `internal/firecracker` | Firecracker API client, TAP, pause/snapshot/restore |
| `internal/snapshot` | Snapshot package format + local/GCS blob stores |
| `internal/placement` | user/app → host ID map (memory or Firestore) |
| `internal/store` | users / keys / apps (memory or Firestore) |
| `internal/migrate` | Cross-host Sleep→Evict→Adopt |
| `internal/rootfs` | ext4 build via mkfs.ext4 + debugfs (`BuildFromDir`) |
| `internal/ocirootfs` | OCI pull (go-containerregistry) → unpack → ext4 cache + boot spec |
| `internal/guestinit` | Exec boot-spec Entrypoint/Cmd with Env + WorkingDir as PID 1 |
| `internal/apppack` | Pack a linux binary into a minimal OCI image (tests / demos) |
| `internal/cutover` | Deploy drain/kick dual-instance cutover |
| `internal/genid` | Generation ids (`g…`) + `app.gen` agent names |
| `internal/agent` | Instance manager (boot, idle sleep, wake, adopt/evict) |
| `hack/fetch-firecracker-assets.sh` | Download firecracker + kernel |
| `hack/run-firestore-tests.sh` | Store/placement tests vs Firestore emulator |
| `terraform/` | GCP env: Firestore, GCS, secrets, gateway, orchestrator, agent MIG + ko images |

## Build & test

Requires Go 1.25+ (`GOTOOLCHAIN=auto` downloads if needed):

```bash
cd sshcloud
go test ./...
go test -race ./...
go build -o bin/gateway ./cmd/gateway
go build -o bin/agent ./cmd/agent
go build -o bin/guestinit ./cmd/guestinit
go build -o bin/fortune ./cmd/fortune
go build -o bin/ocirootfs ./cmd/ocirootfs
```

Firecracker e2e needs `/dev/kvm` + `CAP_NET_ADMIN` (TAP). Without KVM, unit
tests still pass; `Manager.Ensure` returns a clear error.

Firestore tests skip unless `FIRESTORE_EMULATOR_HOST` is set (or use the helper):

```bash
bash hack/run-firestore-tests.sh
```

## Run — process backend (no KVM)

`-fortune-bin` is a **local cert-hop shortcut** only (not the deploy path). It
runs `cmd/fortune` as a subprocess so you can exercise join → proxy without
Firecracker. Menu will be empty until you deploy an app against a real agent.

```bash
go build -o bin/fortune ./cmd/fortune
go run ./cmd/gateway -listen 127.0.0.1:2222 -fortune-bin ./bin/fortune
ssh -p 2222 -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null join@127.0.0.1
```

## Run — Firecracker backend (normal deploy)

Fortune is a normal app: build/push an OCI image, then `ssh deploy@…`.

```bash
# 1) platform assets + agent
bash hack/fetch-firecracker-assets.sh
go build -o bin/guestinit ./cmd/guestinit
go run ./cmd/gateway -user-ca ./ssh_user_ca &  # once, to create CA; Ctrl-C after
go build -o bin/agent ./cmd/agent
sudo ./bin/agent \
  -listen 127.0.0.1:8080 \
  -work-dir /tmp/sshcloud-agent \
  -firecracker "$PWD/_assets/firecracker" \
  -kernel "$PWD/_assets/vmlinux" \
  -ca-pub "$PWD/ssh_user_ca.pub" \
  -guestinit "$PWD/bin/guestinit" \
  -idle 5m \
  -snap-dir /tmp/sshcloud-agent/snapshots

# 2) gateway → agent
go run ./cmd/gateway -listen 127.0.0.1:2222 -agent-url http://127.0.0.1:8080

# 3) join, then deploy fortune (digest-pinned image)
#    Interactive TUI:
ssh -p 2222 join@127.0.0.1
ssh -p 2222 deploy@127.0.0.1
#    Or non-interactive (SSH exec args; used by terraform local-exec):
ssh -p 2222 join@127.0.0.1 demo
ssh -p 2222 deploy@127.0.0.1 \
  fortune --image='repo@sha256:…' --tier=tiny --strategy=kick --yes
ssh -p 2222 fortune@127.0.0.1
```

Guest boot always uses `init=/platform-init` (`cmd/guestinit`), which reads
`/platform-boot.json` from the image config (Entrypoint, Cmd, Env, WorkingDir).
Missing/empty boot spec fails the cold boot. Optional `-rootfs` / `-boot-spec`
exist only for test/dev Ensures without an image.

### OCI image → ext4 rootfs

Allowed apps are digest-pinned (`repo@sha256:…`) Linux/amd64 images with an
empty/root OCI `User` and no declared OCI volumes. PID 1 runs as guest root,
must listen on `:22`, accept arbitrary platform principals, trust the user CA
at `/run/platform/ssh_user_ca.pub`, and present the injected Ed25519 host key at
`/run/platform/ssh_host_ed25519_key`. The kernel is platform-supplied.

`guestinit` mounts proc, sysfs, devtmpfs/devpts, and a bounded `/tmp` before
exec. This is still an appliance-style OCI subset, not a full container
runtime: layer UID/GID/xattrs, non-root users, OCI volumes, cgroups, DNS/egress,
and graceful `StopSignal` supervision are not yet supported.

`internal/ocirootfs.Materialize` pulls with
[go-containerregistry](https://github.com/google/go-containerregistry)
(`remote.Image`, linux/amd64, Google ADC + standard credential keychains), applies layers with
OCI whiteouts through Go's traversal-resistant `os.Root`, builds ext4 via
`rootfs.BuildFromDir`, and caches by digest hex
under `-work-dir/oci-rootfs` (plus `<hex>.boot.json` for PID 1 spec).
Uncompressed unpack is capped at 1 GiB and 100,000 entries. Registry hosts are
allowlisted in deployed gateway/agent processes to prevent image-ref SSRF.
Every cold boot injects `cmd/guestinit`
as `/platform-init` (`-guestinit`) and the resolved boot spec as
`/platform-boot.json`. Base rootfs boots use `-boot-spec` (default
`<rootfs>.boot.json`).

```bash
go run ./cmd/ocirootfs -cache-dir /tmp/oci-rootfs \
  ghcr.io/me/app@sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef
```

Agent `POST /v1/instances/ensure` accepts `"image": "repo@sha256:…"` (required
for real apps), `"gen"`, and `"no_idle"`. `Config.RootfsResolver` (wired in
`cmd/agent`) materializes that digest. `gen` names a parallel microVM as
`app.gen` so drain cutover can run two revisions.

`TestDeployFortuneE2E` packs `cmd/fortune` with `internal/apppack`, runs
`RunDeploy`, and checks cutover Ensure + OCI materialize.

### Deploy cutover

A new digest is a new rootfs/generation. The gateway (`-drain-timeout`, default
5m) pins each SSH session to `store.App.ActiveGen`.

| Strategy | Behavior |
|----------|----------|
| **drain** (default) | Pre-boot new gen; new sessions → new; old stay until disconnect or timeout, then kick + destroy old |
| **kick** | Cancel old sessions, stop old VM, cut over immediately |

`internal/cutover.Controller` is wired in `cmd/gateway` (agent or orchestrator
`POST /v1/ensure` + `/v1/stop`).

### Snapshot sleep / wake

- Package: `vm.state` + `vm.mem` + `rootfs.ext4` + `meta.json` (tap/IP/MAC).
- Agent API: `POST /v1/instances/sleep`, `POST /v1/instances/wake` (or
  `ensure`, which wakes if sleeping), `GET /v1/instances/status?user=&app=`.
- Default store is local under `-snap-dir`; production uses `-gcs-bucket`.
- TAP is kept across sleep; wake restores into the same network identity.

### Cross-host migrate

Flow: acquire a durable placement lease → freeze the outer gateway session →
source `Sleep`/`Evict` → target `Adopt` → CAS placement commit → thaw. The
outer client SSH connection remains open and its bounded channel window holds
input during the move; the app receives a fresh backend SSH session after thaw.
Generic app-session state is therefore reset rather than transparently morphed.

```bash
go run ./cmd/orchestrator \
  -listen 127.0.0.1:8090 \
  -hosts host-a=http://127.0.0.1:8080,host-b=http://127.0.0.1:8081 \
  -default-host host-a

curl -X POST http://127.0.0.1:8090/v1/migrate \
  -d '{"user":"alice","app":"fortune","gen":"g…","to":"host-b"}'
```

Agent APIs: `POST /v1/instances/evict`, `POST /v1/instances/adopt`. Migration
is generation-aware. The orchestrator also exposes:

```text
POST /v1/hosts/cordon  {"host":"host-a","cordoned":true}
POST /v1/hosts/drain   {"host":"host-a"}
GET  /v1/hosts         # capacity, reservations, cordon state
```

Host drain groups active and draining generations per app, reserves their
aggregate target capacity, moves them under one placement lease, and commits
the app's host pointer once. Snapshot metadata includes a platform compatibility
ID and production uses Firecracker's portable `T2` CPU template, so a rollout
cannot restore into a mismatched VMM/kernel/CPU baseline.

Orchestration unit test (httptest agent stubs, no VMs):
`go test ./internal/migrate -run TestMigrateOrchestration`.

### Real KVM e2e (CI + local)

Free GitHub `ubuntu-latest` x86_64 runners expose nested virt (`/dev/kvm`).
When `sshcloud/` changes, the `sshcloud-kvm` job in `.github/workflows/test.yml`
enables KVM access, builds a fortune rootfs, and runs (fails if any test skips):

- `TestKVMSleepWake` — boot → snapshot sleep → wake → dial guest `:22`
- `TestKVMCrossHostMigrate` — sleep/evict on A → adopt on B (shared store)

Locally (Linux + KVM; Firecracker runs as your user, `sudo ip` for TAP):

```bash
# one-time: ensure /dev/kvm is usable
echo 'KERNEL=="kvm", GROUP="kvm", MODE="0666", OPTIONS+="static_node=kvm"' \
  | sudo tee /etc/udev/rules.d/99-kvm4all.rules
sudo udevadm control --reload-rules && sudo udevadm trigger --name-match=kvm

bash hack/run-kvm-e2e.sh   # not as root
```

### Chaos coverage in CI

Normal Go CI runs deterministic fault injection (also under the race detector):

- real SSH client → gateway → cert hop → app sessions across live drain and kick
- snapshot pause/create/publish/resume failure matrix and incomplete packages
- unexpected Firecracker process death, lifecycle fencing, and resource reservations
- deploy persistence/hold failures plus admission-vs-deploy linearization
- stale-placement refusal, expiring lease takeover, and operation-journal reconciliation
- placement-lease fencing, best-fit capacity scheduling, and multi-generation host drain
- bounded live-session freeze/reconnect with timeout kick fallback
- cancellation of a backend that stalls during its SSH handshake

The KVM job adds substrate-dependent chaos: a canceled/failed snapshot publish
must resume a dialable guest, and a fresh manager must recover a sleeping guest
from the durable snapshot through ordinary `Ensure`. Cloud IAM, firewall/NAT,
and Terraform replacement behavior are not exercised in CI; this repository
does not have a disposable GCP project. Local fakes deliberately do not claim
to validate provider semantics.

## Status

Implemented and covered at package/integration level:

- [x] Owner-scoped routing, join/menu/deploy UX, busy admission
- [x] Gateway-minted user certificates and normal digest-pinned fortune app
- [x] Per-instance Ed25519 app host identity pinned through gateway→agent
- [x] Shell/exec/subsystem, PTY/env/resize/signal, stderr, and exact exit forwarding
- [x] Bounded, classified wake retry with in-session status
- [x] Hardened OCI unpack, authenticated pulls, boot-spec PID 1, ext4 cache
- [x] Firecracker boot plus consistent pause→disk→memory snapshots
- [x] Atomic snapshot package publication and restart-on-Ensure recovery
- [x] Serialized deploy cutover, same-artifact idempotency, drain/kick fencing
- [x] Real `tiny` (1 vCPU/128 MiB) and `small` (2 vCPU/512 MiB) resources
- [x] Generation-aware migrate primitives and placement-after-readiness
- [x] Durable placement leases/CAS, capacity-aware bin packing, cordon + host drain
- [x] Bounded gateway freeze/thaw with backend-session reconnect
- [x] Gateway drain/no-idle reconciliation and snapshot platform-version fencing
- [x] Agent-host SSH relay for the separate-VM GCP gateway data path
- [x] Authenticated internal APIs, narrow VPC firewall edges, private-host NAT
- [x] Content-addressed platform assets and opt-in Terraform fortune bootstrap
- [x] Unit/Firestore/KVM suites plus Terraform and tagged-test CI validation
- [x] Handshake/join/app/session/deploy/wake/awake-VM admission limits
- [x] Durable pending/retiring deploy reconciliation and bounded snapshot retention
- [x] TAP firewall isolation: guest-initiated host/VPC/metadata/egress traffic denied
- [x] Liveness/readiness and correlated placement/host diagnostics

Required before public/self-service use:

- [ ] Workload identity + mTLS in place of interim bearer tokens
- [ ] Firecracker jailer/seccomp and a privileged TAP helper (agent VMM is not
      yet a production-strength host boundary)
- [ ] Optional audited guest internet egress allowlist (current policy is deny-all)
- [ ] Distributed deploy-state CAS (placement operations are now leased)
- [ ] Session leases/heartbeats (current no-idle hold is not crash-expiring)
- [ ] Automatic pre-termination MIG hooks (manual drain-before-replace is available;
      auto-healing after a hard failure remains abrupt)
- [ ] Long-term snapshot quota/accounting (current versions retain current+previous with grace)
- [ ] External key management, encrypted remote Terraform state, rotation drills
- [ ] Manual first apply/drain/rollout validation in an operator-owned environment
      (there is no disposable GCP project available to CI)
