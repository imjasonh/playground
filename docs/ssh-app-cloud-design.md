# Design: SSH App Cloud

> **Status: design / pre-implementation.** Working name **SSH App Cloud** — a
> public PaaS where apps deploy an OCI image that speaks SSH on port 22, and
> users connect with `ssh <owner>.<app>@foo.com`. No HTTP. Runtime is Firecracker
> microVMs on a GCE MIG, with platform services in Go + Terraform
> (`terraform-provider-ko`).

### Locked decisions

| Topic | Decision |
|-------|----------|
| Product | Public PaaS (self-serve), individual developers in v1 |
| Connect URL | `ssh <owner>.<app>@foo.com` (username form only in v1) |
| Naming | Owner-scoped app names (`alice.fortune`) |
| Auth | SSH public keys registered **cloud-wide** per user; reusable across all of that user’s apps |
| Onboarding | Reserved platform handler `ssh join@foo.com` (gateway built-in, not a microVM) |
| First demo | `fortune` — **requires joining first** |
| “No shell” | No host/login shell; apps may offer PTY, git subsystems, long-lived multi-client sessions |
| Deploy unit | OCI image whose PID 1 speaks SSH on `:22` |
| SSH stack | Bundled in the image (no platform sshd helper in v1) |
| Image source | Public registries (GHCR / Docker Hub) |
| Readiness | TCP accept on 22 |
| Isolation | One Firecracker microVM per app instance |
| Multi-user | First-class (many SSH clients → one shared microVM) |
| Scaling | MicroVMs scale to zero when idle; GCE hosts stay warm (MIG) |
| Resources | Fixed tiers first; arbitrary CPU/RAM later |
| Port forwarding | Not in v1 |
| App-to-app net | None — inbound SSH + internet egress only |
| Egress | Allowlist |
| Volumes | Optional persistent volume |
| Snapshots | Orchestration only (bin-pack / drain); stored in GCS |
| Migrate UX | Prefer keeping connections; brief freeze OK; reconnect acceptable fallback |
| Control plane | Split: API / orchestrator / host agent |
| Infra | MIG + host agent; Terraform + ko for **platform** services only |
| Region | One region until bin-pack/migration is solid |
| Observability | Logs, metrics, connection traces |
| Billing | Quotas in v1; metering/billing later |

---

## 1. Pitch

Developers ship **SSH apps**: TUI tools (Bubble Tea), git servers, multiplayer
dungeons — anything that speaks SSH. Users never get a shell on the host. The
platform routes `ssh alice.fortune@foo.com` to alice’s fortune microVM, waking
it from zero if needed and showing a short loading UI while it boots.

### One-liner

> Deploy an SSH-speaking OCI image; we run it in a Firecracker microVM and
> expose `ssh owner.app@foo.com`.

---

## 2. Goals & non-goals

### Goals (v1)

1. **Join → fortune** vertical slice: register via `join`, then
   `ssh <user>.fortune@foo.com`.
2. Strong isolation: one microVM per app instance.
3. Scale microVMs to zero; keep GCE capacity warm for fast wake.
4. Gateway-held cold start with optional loading TUI before attach.
5. Snapshot microVMs to GCS to drain/bin-pack GCE hosts with minimal downtime.
6. Quotas (CPU/RAM/instances/connections); no billing yet.

### Non-goals (v1)

- HTTP/HTTPS ingress, custom domains for SSH hostnames
- SSH port forwarding / reverse tunnels
- Private app-to-app service mesh
- User-facing snapshot save/restore
- Multi-region
- Platform-provided sshd base image (apps bundle their own)
- Orgs/teams (individuals only)

---

## 3. Personas & naming

- **Owner** — registered user, e.g. `alice` (from `join`).
- **App** — named under an owner, e.g. `fortune` → SSH user `alice.fortune`.
- **Reserved platform users** (not allocatable): `join`, `help`, `status`,
  `whoami`, `root`, `admin`, … 

Parse rule for the SSH username field:

```text
join              → platform onboarding handler
<owner>.<app>     → route to that app instance
```

---

## 4. Onboarding: `ssh join@foo.com`

`join` is a **gateway built-in**, not a user app and not a Firecracker VM.

### Why gateway-native

- First contact happens **before** any key is registered.
- No cold start for the most important first impression.
- Platform-controlled TUI — no phishing via a user image.
- Cheap and always available.

### Flow

```text
ssh join@foo.com
  │
  ├─ Gateway accepts the offered public key (special auth mode)
  ├─ Read key type + fingerprint (SHA256:…)
  ├─ Bubble Tea TUI:
  │    • new user  → pick username (owner id)
  │    • existing  → manage keys (add/list/revoke)
  ├─ API: create user + store cloud-wide authorized key
  └─ Done: "You're alice. Try: ssh alice.fortune@foo.com"
```

### Key model

- Keys are owned by the **user**, not the app.
- After join, that key authenticates to **all** of alice’s apps.
- Adding a second machine: `ssh join@foo.com` again → add key.

### Fortune requires joining first

Unauthenticated / unknown keys **cannot** reach `*.fortune` (or any user app).
The gateway rejects app connections unless `key → registered user` succeeds.
The fortune demo path is explicitly:

1. `ssh join@foo.com` — pick `alice`, register key  
2. `ssh alice.fortune@foo.com` — only works with a registered key for `alice`

First-time copy in the `join` “done” screen always points at fortune.

---

## 5. App contract

| Concern | Rule |
|--------|------|
| Artifact | OCI image from GHCR/Docker Hub |
| Process | PID 1 listens on TCP `:22` (SSH) |
| Ready | TCP accept on 22 |
| SSH features | Whatever the image’s server offers (PTY, subsystems, many clients) |
| Platform shell | None |

Example fortune image: tiny distro + `sshd` (or an SSH library server) that runs
`fortune` (or a small Go SSH server) on session open.

### Access (v1)

- Connecting user must be **joined** (registered key).
- For `alice.fortune`, the key must map to owner `alice` (owner-only access).
- Public/shared apps and ACLs are later; the demo is personal fortune per owner.

### Auto-provision demo app

After join, the control plane may **ensure** a `fortune` app exists for that
owner (platform-standard image, `tiny` tier) so step 2 works without a separate
deploy CLI in the MVP slice. Real deploys (custom images) come via API/CLI next.

---

## 6. Data plane & cold start

```text
Client
  │  ssh alice.fortune@foo.com
  ▼
SSH Gateway
  │  1) auth key → user alice
  │  2) authorize alice.fortune
  │  3) if microVM scaled to zero:
  │       PTY loading UI ("Starting fortune…")
  │       ask orchestrator/agent to wake instance
  │  4) dial microVM :22 (platform SSH client)
  │  5) attach / proxy session (prefer keeping client connection)
  ▼
GCE host (MIG) ── host agent ── Firecracker microVM ── app :22
```

### Cold start UX

- Gateway **holds** the client SSH session until the microVM is ready.
- Shows a simple loading TUI when wake takes more than a trivial moment.
- Then forwards into the app session (gateway opens SSH to the microVM and
  pipes PTY/stdio/channels as appropriate).

This implies the **gateway terminates client SSH** and dials the app’s SSH as a
second hop. The image contract (“speaks SSH on 22”) still holds; users do not
SSH directly at GCE/Firecracker network addresses.

### Scale to zero

- Idle microVMs stop (no connections + idle timeout).
- GCE MIG hosts remain up (warm pool); hosts are bin-packed via snapshot migrate,
  not scaled to zero.

---

## 7. Control plane

Split Go services:

| Component | Role |
|-----------|------|
| **API** | Users, keys, apps, deploys, quotas, volumes |
| **Orchestrator** | Placement, wake/sleep, migrate/drain, bin-pack |
| **Host agent** | On each GCE VM: image→rootfs, Firecracker lifecycle, mounts, probes |
| **SSH gateway** | Client SSH, `join`, authz, loading UI, proxy to microVMs |

### Infra

- GCE **MIG** of host VMs running the host agent (+ Firecracker/jailer).
- Terraform provisions GCP resources; **terraform-provider-ko** builds/deploys
  platform Go services only (not customer app images).
- One region in v1.
- Snapshots in **GCS**; optional **persistent volumes** attachable per app.

### Migration

Orchestration-only snapshots:

1. Freeze microVM  
2. Snapshot to GCS  
3. Restore on target host  
4. Re-point gateway routing  
5. Thaw — prefer not dropping the client; brief freeze OK  

Used to drain hosts and shrink/grow the warm MIG efficiently.

---

## 8. Networking & security

- Ingress: SSH to gateway only (public).
- MicroVMs on private host network / tap; not directly reachable from Internet.
- Egress from microVMs: **allowlist**.
- No app-to-app network in v1.
- No port forwarding in v1.
- Gateway↔microVM trust: platform-managed credentials (e.g. short-lived cert or
  injected key) so the gateway can dial app `:22` without using the end-user key
  toward the VM if the app expects user keys — **open detail** (see §10).

---

## 9. MVP vertical slice

1. Terraform + ko: API, orchestrator, gateway, host agent on a small MIG.  
2. Platform fortune image (OCI, SSH on 22).  
3. `ssh join@foo.com` → register `alice` + key; ensure `alice.fortune`.  
4. `ssh alice.fortune@foo.com` → auth → wake if needed (loading UI) → fortune.  
5. Idle → microVM sleep; next connect wakes again.  
6. Drain a host via GCS snapshot migrate; confirm brief blip / held connection.

### Out of MVP (but designed for)

- Custom image deploy CLI  
- git-server and multiplayer dungeon sample apps  
- Arbitrary resource sizes  
- Per-app ACLs / public apps  

---

## 10. Open details

1. **Gateway↔app SSH auth** — inject user `authorized_keys` into the VM vs
   gateway-only auth with a platform force-command hop into the app.  
2. **Kernel strategy** — shared platform kernel vs per-image kernel.  
3. **OCI → rootfs pipeline** — extract + overlay; when to take a warm snapshot
   for faster subsequent wakes.  
4. **Volume backing** — persistent disk vs virtio-blk from PD vs other.  
5. **Allowlist UX** — global defaults vs per-app rules.  
6. **Username charset** — `[a-z][a-z0-9-]{2,31}` for owner and app; dot only as
   separator in the SSH username field.  

---

## 11. Example session

```bash
# Brand new user
ssh join@foo.com
# TUI: found SHA256:…, pick username "alice"
# → You're alice. Try: ssh alice.fortune@foo.com

# Unknown key still fails on apps
ssh alice.fortune@foo.com   # from a different key → reject, hint to join

# Registered key
ssh alice.fortune@foo.com
# (optional) Starting fortune…
# <fortune output / session>
```
