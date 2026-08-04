# sshcloud — SSH App Cloud

Platform services for an SSH-only PaaS: users `ssh foo.com` to join or pick an
app; apps speak SSH on `:22` and run in Firecracker microVMs.

Design: [`docs/ssh-app-cloud-design.md`](../docs/ssh-app-cloud-design.md).

## Layout

| Path | Role |
|------|------|
| `cmd/gateway` | Public SSH entry (join, menu, deploy, proxy) |
| `cmd/agent` | Host agent: Firecracker lifecycle + HTTP API |
| `cmd/fortune` | Sample SSH app (verifies platform user certs) |
| `cmd/mkrootfs` | Build fortune ext4 rootfs for Firecracker |
| `cmd/ocirootfs` | Materialize digest-pinned OCI image → cached ext4 |
| `cmd/orchestrator` | Placement + cross-host migrate HTTP API |
| `cmd/api` | Internal control API stub |
| `internal/firecracker` | Firecracker API client, TAP, pause/snapshot/restore |
| `internal/snapshot` | Snapshot package format + local/GCS blob stores |
| `internal/placement` | user/app → host ID map (memory or Firestore) |
| `internal/store` | users / keys / apps (memory or Firestore) |
| `internal/migrate` | Cross-host Sleep→Evict→Adopt |
| `internal/rootfs` | ext4 build via mkfs.ext4 + debugfs (`BuildFromDir`) |
| `internal/ocirootfs` | OCI pull (go-containerregistry) → unpack → ext4 cache |
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
go build -o bin/gateway ./cmd/gateway
go build -o bin/agent ./cmd/agent
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

```bash
go build -o bin/fortune ./cmd/fortune
go run ./cmd/gateway -listen 127.0.0.1:2222 -fortune-bin ./bin/fortune
# optional durable store (emulator or real project):
#   FIRESTORE_EMULATOR_HOST=127.0.0.1:8080 \
#   go run ./cmd/gateway -firestore-project sshcloud-test …
ssh -p 2222 -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null join@127.0.0.1
```

## Run — Firecracker backend

```bash
# 1) assets
bash hack/fetch-firecracker-assets.sh
go build -o _assets/fortune ./cmd/fortune
go run ./cmd/gateway -user-ca ./ssh_user_ca &  # once, to create CA; Ctrl-C after
go run ./cmd/mkrootfs -fortune _assets/fortune -ca-pub ssh_user_ca.pub -out _assets/fortune-rootfs.ext4

# 2) agent (needs root/KVM for TAP + microVMs)
# Idle VMs snapshot to <work-dir>/snapshots (or -gcs-bucket) after -idle.
sudo ./bin/agent \
  -listen 127.0.0.1:8080 \
  -work-dir /tmp/sshcloud-agent \
  -firecracker "$PWD/_assets/firecracker" \
  -kernel "$PWD/_assets/vmlinux" \
  -rootfs "$PWD/_assets/fortune-rootfs.ext4" \
  -ca-pub "$PWD/ssh_user_ca.pub" \
  -idle 5m \
  -snap-dir /tmp/sshcloud-agent/snapshots

# 3) gateway → agent (single host)
go run ./cmd/gateway -listen 127.0.0.1:2222 -agent-url http://127.0.0.1:8080

# or gateway → orchestrator (placement-aware Ensure across hosts)
go run ./cmd/orchestrator \
  -listen 127.0.0.1:8090 \
  -hosts host-a=http://127.0.0.1:8080 \
  -default-host host-a
go run ./cmd/gateway -listen 127.0.0.1:2222 -orchestrator-url http://127.0.0.1:8090
```

Guest boot: `init=/fortune -- -listen 0.0.0.0:22 -ca /ca.pub` on a static
TAP subnet; gateway shows a wake loading line (`Starting fortune…`), mints a
user cert, and dials `guestIP:22`.

### OCI image → ext4 rootfs

Public apps are digest-pinned (`repo@sha256:…`). PID 1 must listen on `:22`
and trust the platform user CA at `/ca.pub` or `/run/platform/ssh_user_ca.pub`
(the agent still injects `/ca.pub` via debugfs). The kernel is platform-supplied,
not taken from the image.

`internal/ocirootfs.Materialize` pulls with
[go-containerregistry](https://github.com/google/go-containerregistry)
(`remote.Image`, linux/amd64, anonymous public registries), applies layers with
OCI whiteouts, builds ext4 via `rootfs.BuildFromDir`, and caches by digest hex
under `-work-dir/oci-rootfs`. Uncompressed unpack is capped at 1 GiB.

```bash
go run ./cmd/ocirootfs -cache-dir /tmp/oci-rootfs \
  ghcr.io/me/app@sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef
```

Agent `POST /v1/instances/ensure` accepts optional `"image": "repo@sha256:…"`,
`"gen"`, and `"no_idle"`. When `image` is set, `Config.RootfsResolver` (wired
in `cmd/agent`) materializes that digest instead of cloning `-rootfs`. `gen`
names a parallel microVM as `app.gen` so drain cutover can run two revisions.

### Deploy cutover

A new digest is a new rootfs/generation. The gateway (`-drain-timeout`, default
5m) pins each SSH session to `store.App.ActiveGen`.

| Strategy | Behavior |
|----------|----------|
| **drain** (default) | Pre-boot new gen; new sessions → new; old stay until disconnect or timeout, then kick + destroy old |
| **kick** | Cancel old sessions, stop old VM, cut over immediately |

`internal/cutover.Controller` is wired in `cmd/gateway` (agent or orchestrator
`POST /v1/ensure` + `/v1/stop`). Local fortune ignores gens (routing-only).

### Snapshot sleep / wake

- Package: `vm.state` + `vm.mem` + `rootfs.ext4` + `meta.json` (tap/IP/MAC).
- Agent API: `POST /v1/instances/sleep`, `POST /v1/instances/wake` (or
  `ensure`, which wakes if sleeping), `GET /v1/instances/status?user=&app=`.
- Default store is local under `-snap-dir`; production uses `-gcs-bucket`.
- TAP is kept across sleep; wake restores into the same network identity.

### Cross-host migrate

Flow: source `Sleep` → `Evict` (keep shared snapshot) → target `Adopt` →
update placement. Orchestrator:

```bash
go run ./cmd/orchestrator \
  -listen 127.0.0.1:8090 \
  -hosts host-a=http://127.0.0.1:8080,host-b=http://127.0.0.1:8081 \
  -default-host host-a

curl -X POST http://127.0.0.1:8090/v1/migrate \
  -d '{"user":"alice","app":"fortune","to":"host-b"}'
```

Agent APIs: `POST /v1/instances/evict`, `POST /v1/instances/adopt`.

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

## Status

- [x] Routing, session admission, memory store
- [x] SSH gateway: join, menu, busy reject
- [x] User CA + cert hop (process or Firecracker)
- [x] Host agent + Firecracker client + rootfs builder
- [x] Snapshot-on-sleep (local + GCS store; idle loop; wake on ensure)
- [x] Cross-host migrate (Sleep→Evict→Adopt + placement)
- [x] Real Firecracker KVM e2e in GitHub Actions (`sshcloud-kvm` job)
- [x] Gateway wake loading TUI + placement-aware dial (`-orchestrator-url`)
- [x] Deploy TUI (digest-pinned register + drain/kick cutover)
- [x] Firestore store (users/keys/apps) + placement (`-firestore-project`)
- [x] Terraform + ko (Firestore, GCS, secrets, gateway VM, orchestrator, agent MIG)
- [x] OCI image → ext4 rootfs (`internal/ocirootfs`; agent Ensure `"image"` hook)
- [x] Deploy cutover (drain/kick dual-instance; session pin per generation)
- [ ] Gateway freeze-buffer during migrate
