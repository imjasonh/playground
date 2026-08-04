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

## Status

Scaffold + pure-Go routing/session admission. Gateway does not yet speak SSH;
Firecracker, certs, and Terraform come next.
