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
| `cmd/orchestrator` | Placement + cross-host migrate HTTP API |
| `cmd/api` | Internal control API stub |
| `internal/firecracker` | Firecracker API client, TAP, pause/snapshot/restore |
| `internal/snapshot` | Snapshot package format + local/GCS blob stores |
| `internal/placement` | user/app → host ID map |
| `internal/migrate` | Cross-host Sleep→Evict→Adopt |
| `internal/rootfs` | ext4 build via mkfs.ext4 + debugfs |
| `internal/agent` | Instance manager (boot, idle sleep, wake, adopt/evict) |
| `hack/fetch-firecracker-assets.sh` | Download firecracker + kernel |

## Build & test

Requires Go 1.25+ (`GOTOOLCHAIN=auto` downloads if needed):

```bash
cd sshcloud
go test ./...
go build -o bin/gateway ./cmd/gateway
go build -o bin/agent ./cmd/agent
go build -o bin/fortune ./cmd/fortune
```

Firecracker e2e needs `/dev/kvm` + `CAP_NET_ADMIN` (TAP). Without KVM, unit
tests still pass; `Manager.Ensure` returns a clear error.

## Run — process backend (no KVM)

```bash
go build -o bin/fortune ./cmd/fortune
go run ./cmd/gateway -listen 127.0.0.1:2222 -fortune-bin ./bin/fortune
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

# 3) gateway → agent
go run ./cmd/gateway -listen 127.0.0.1:2222 -agent-url http://127.0.0.1:8080
```

Guest boot: `init=/fortune -- -listen 0.0.0.0:22 -ca /ca.pub` on a static
TAP subnet; gateway mints a user cert and dials `guestIP:22`.

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
- [ ] Gateway freeze-buffer during migrate, deploy TUI, Firestore
- [ ] Terraform
