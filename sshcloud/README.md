# sshcloud — SSH App Cloud

Platform services for an SSH-only PaaS: users `ssh foo.com` to join or pick an
app; apps are OCI images that speak SSH on `:22`, run in Firecracker microVMs.

Design: [`docs/ssh-app-cloud-design.md`](../docs/ssh-app-cloud-design.md).

## Layout

| Path | Role |
|------|------|
| `cmd/gateway` | Public SSH entry (join, menu, deploy, proxy) |
| `cmd/orchestrator` | Placement, wake/sleep, deploy cutover, quotas |
| `cmd/agent` | Host agent: Firecracker lifecycle on GCE VMs |
| `cmd/api` | Internal control API (not a public deploy API) |
| `internal/route` | SSH username → hub/app routing |
| `internal/session` | Per user×app session admission (max 1) |
| `internal/names` | Username/app name validation + reserved set |
| `internal/store` | Persistence interface (memory stub; Firestore later) |
| `images/fortune` | Sample app image (SSH server + fortune) |
| `terraform/` | GCP + ko wiring (stub) |

## Build & test

Requires Go 1.25+ (`GOTOOLCHAIN=auto` downloads if needed):

```bash
cd sshcloud
go test ./...
go build -o bin/gateway ./cmd/gateway
go build -o bin/orchestrator ./cmd/orchestrator
go build -o bin/agent ./cmd/agent
go build -o bin/api ./cmd/api
```

## Run the gateway (local)

```bash
go build -o bin/fortune ./cmd/fortune
go run ./cmd/gateway -listen 127.0.0.1:2222 -fortune-bin ./bin/fortune

# in another terminal:
ssh -p 2222 -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null join@127.0.0.1
# pick a username → app menu → select fortune
ssh -p 2222 -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null fortune@127.0.0.1
```

With `-fortune-bin`, the gateway mints a short-lived user cert and proxies SSH
into the fortune process (stand-in for a Firecracker microVM). Without it,
fortune runs as an in-process stub.

State is in-memory (lost on restart). Keys default to `./ssh_host_ed25519_key`
and `./ssh_user_ca` (+ `.pub`).

## Status

- [x] Routing, session admission (max 1 / user×app), memory store
- [x] SSH gateway: join, menu, busy reject
- [x] User CA + cert hop into local `cmd/fortune` backend
- [ ] Deploy TUI, Firestore, Firecracker host agent
- [ ] Orchestrator / Terraform
