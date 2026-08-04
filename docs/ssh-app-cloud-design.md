# Design: SSH App Cloud

> **Status: design / pre-implementation.** Working name **SSH App Cloud** — a
> public PaaS where apps deploy an OCI image that speaks SSH on port 22, and
> users connect with `ssh <app>@foo.com` (owner inferred from the presenting
> key). No HTTP. Runtime is Firecracker microVMs on a warm GCE host MIG, with
> platform services in Go + Terraform (`terraform-provider-ko`).

### Locked decisions

| Topic | Decision |
|-------|----------|
| Product | Public PaaS (self-serve), individual developers in v1 |
| Connect URL | `ssh <app>@foo.com` — **short form only**; owner inferred from key |
| Naming | App names are per-user namespace (each user can have their own `fortune`) |
| Auth (client→gateway) | SSH public keys registered **cloud-wide** per user |
| Auth (gateway→app) | Gateway mints **short-lived SSH user certs** asserting the user; apps verify via platform CA |
| CA delivery | Platform **injects** user CA at boot (`/run/platform/ssh_user_ca.pub`); images need not bake it in |
| App SSH server | Any SSH server that can verify platform user certs — **not** OpenSSH-specific |
| Onboarding | `ssh join@foo.com` (gateway built-in) |
| Deploy | `ssh deploy@foo.com` (gateway built-in SSH UX) — no HTTP deploy API in v1 |
| Other platform users | Only `join` + `deploy` in MVP (`help` / `whoami` / `status` later) |
| First demo | `fortune` — **requires joining first**; **lazy-created on first connect** |
| “No shell” | No host/login shell; apps may offer PTY, exec/subsystem, long-lived multi-client sessions |
| Proxy fidelity | Session + PTY + exec/subsystem (not full arbitrary channel proxy) |
| Deploy unit | OCI image@**digest**; PID 1 speaks SSH on `:22` |
| Image source | Public registries (GHCR / Docker Hub); **digest required** |
| Kernel | Shared platform kernel for all apps |
| Readiness | TCP accept on 22 |
| Isolation | One Firecracker microVM per app instance |
| Multi-user | First-class (many SSH clients → one shared microVM) |
| Idle / scale-to-zero | **Snapshot-on-sleep to GCS**; wake = restore |
| Host capacity | GCE hosts stay warm (MIG); single **gateway VM** in v1 |
| Gateway host trust | Shared stable host key now; host CA later |
| Wake failures | Retry in-place (time-capped) now; queue-for-capacity later |
| Resources | `tiny` + `small` tiers in v1 |
| Port forwarding | Not in v1 |
| App-to-app net | None — inbound SSH + internet egress only |
| Egress | Single **global** platform allowlist |
| Volumes | Optional; **GCS-backed** block/virtio |
| Snapshots | Orchestration (bin-pack/drain) **and** idle sleep; stored in GCS |
| Migrate UX | Best-effort **freeze buffer** (time-capped); then force reconnect |
| Control plane | Split: API / orchestrator / host agent / SSH gateway |
| Datastore | **Firestore** for now |
| Infra | Host MIG + agent; Terraform + ko for **platform** services only |
| Region | One region until bin-pack/migration is solid |
| Observability | Logs, metrics, **metadata-only** connection traces (no session bytes) |
| Quotas | Enforced in v1 (starter defaults below); billing later |
| Account recovery | **None in v1** (lost all keys → new username / support-only) |

### Starter quotas

| Quota | Default |
|-------|---------|
| Apps / user | 5 |
| Concurrent SSH sessions / user | 10 |
| Concurrent sessions / app | 10 |
| Awake microVMs / user | 2 |
| Wakes / user / hour | 30 |
| Snapshot + volume storage / user | 5 GB |

---

## 1. Pitch

Developers ship **SSH apps**: TUI tools (Bubble Tea), git servers, multiplayer
dungeons — anything that speaks SSH and can verify platform-minted user certs.
Users never get a shell on the host. After `join`, they connect with
`ssh fortune@foo.com`; the gateway maps their key → user → that user’s app,
waking a snapshotted microVM if needed and showing a short loading UI.

### One-liner

> Deploy an SSH-speaking OCI image; we run it in a Firecracker microVM and
> expose `ssh app@foo.com`.

---

## 2. Goals & non-goals

### Goals (v1)

1. **Join → fortune** vertical slice (lazy fortune on first connect).
2. Strong isolation: one microVM per app instance.
3. Snapshot-on-sleep; warm GCE hosts; gateway-held wake with loading TUI.
4. Gateway-minted SSH user certs into apps (keys rotate without touching VMs).
5. SSH-based `deploy` for custom digest-pinned images.
6. Snapshot migrate with best-effort session hold for host drain/bin-pack.
7. Quotas; no billing yet.

### Non-goals (v1)

- HTTP/HTTPS ingress or deploy API
- `ssh owner.app@…` / custom SSH hostnames
- SSH port forwarding / reverse tunnels
- Private app-to-app networking
- Per-app egress rules
- User-facing snapshot save/restore
- Account recovery / email identity
- Multi-region / HA gateway
- Platform-provided OpenSSH wrapper (apps bring any cert-verifying SSH server)
- Orgs/teams; cross-user app access
- Full SSH channel proxy beyond session/PTY/exec/subsystem

---

## 3. Personas & naming

- **User / owner** — registered identity from `join`, e.g. `alice` (display /
  quota key; **not** part of the SSH username for apps).
- **App** — name in that user’s namespace, e.g. `fortune`, `mygame`.
- **Reserved platform users** (not allocatable as apps): `join`, `deploy`,
  and later `help`, `status`, `whoami`, plus `root`, `admin`, …

Parse rule for the SSH username field:

```text
join     → platform onboarding / key management
deploy   → platform deploy UX
<app>    → that app for the user identified by the presenting key
```

Username charset (apps + join-chosen owner id): `[a-z][a-z0-9-]{2,31}`.

---

## 4. Onboarding: `ssh join@foo.com`

`join` is a **gateway built-in**, not a microVM.

### Flow

```text
ssh join@foo.com
  │
  ├─ Gateway accepts the offered public key (special auth mode)
  ├─ Lookup key fingerprint
  │    • unknown → pick username once → create user + bind key
  │    • known   → already identified (no username prompt)
  │                → manage keys (add/list/revoke)
  └─ Done (first time): "You're alice. Try: ssh fortune@foo.com"
```

### Key model

- Keys are owned by the **user**, cloud-wide, reusable across all their apps.
- Re-join with the same key never asks for a username again.
- Adding a machine: `ssh join@foo.com` with a new key while… *(open: how to
  bind an additional key without recovery — likely require an already-authorized
  key in the same session, or a “add key” path while authenticated)*.  
  **Interim:** first key wins at signup; additional keys added from an
  already-authenticated `join` session.

### Fortune requires joining first

Unknown keys cannot reach apps. Gateway rejects with a hint to `ssh join@foo.com`.

Fortune is **not** created at join. First successful `ssh fortune@foo.com`
lazy-creates the user’s `fortune` app (platform image, `tiny`) and wakes it.

---

## 5. App contract

| Concern | Rule |
|--------|------|
| Artifact | Public OCI image, **digest-pinned** (`repo@sha256:…`) |
| Process | PID 1 listens on TCP `:22` (SSH) |
| Server | Any SSH implementation that verifies **platform user certs** |
| CA | Read platform user CA from `/run/platform/ssh_user_ca.pub` (injected) |
| Identity | Cert principal = platform username (e.g. `alice`) |
| Ready | TCP accept on 22 |
| Kernel | Platform-supplied (not from the image) |
| Platform shell | None |

Fortune sample: small Go SSH server (or similar) that verifies the injected CA,
opens a session, prints a fortune / runs a tiny PTY app.

### Gateway proxy fidelity

Client↔gateway↔app supports:

- Session channel + PTY (+ window-change)
- Exec and subsystem (e.g. git)

Not in v1: arbitrary multiplexing / port forwarding / agent forwarding as a
platform guarantee.

### Access (v1)

- Key must map to a registered user.
- `ssh fortune@foo.com` always means **that user’s** `fortune` (no cross-user).

---

## 6. Auth hops & certs

```text
Client key
  → Gateway: public-key auth against Firestore-registered keys
  → Gateway mints short-lived SSH user cert (principal=alice, TTL=minutes)
  → App SSH: verifies cert with injected platform CA
```

Users can rotate/add keys via `join` without redeploying or rewriting app
`authorized_keys`. Certs are **session-bound** (minutes-scale), minted per
attach.

---

## 7. Data plane, wake, sleep

```text
Client
  │  ssh fortune@foo.com
  ▼
SSH Gateway (single VM in v1; shared host key)
  │  1) auth key → user
  │  2) resolve user/fortune (lazy-create if platform demo app)
  │  3) if sleeping: loading TUI; restore snapshot from GCS (retry in-place)
  │  4) mint user cert; dial microVM :22
  │  5) proxy session/PTY/exec/subsystem
  ▼
GCE host MIG ── host agent ── Firecracker ── app :22
```

### Cold start UX

- Gateway **holds** the client SSH session until the microVM is ready.
- Loading TUI while waking (“Starting fortune…”).
- Wake failures: **retry in-place** with status, then fail (queue-for-capacity later).

### Sleep

- On idle (no connections + timeout): **freeze + snapshot to GCS**, stop VM.
- Wake = restore snapshot (memory + ephemeral disk).
- Optional **GCS-backed volumes** remount/reattach across sleep/migrate.

### Migration (host drain / bin-pack)

1. Freeze microVM (gateway **buffers** client I/O, time-capped)  
2. Snapshot to GCS  
3. Restore on target host  
4. Re-point gateway routing  
5. Thaw; if over cap → force reconnect  

---

## 8. Deploy: `ssh deploy@foo.com`

Gateway built-in (not a microVM). Authenticated by the same cloud-wide keys.

Responsibilities (v1 sketch):

- Create/update app name in the user’s namespace  
- Set image **digest** (reject unpinned tags)  
- Choose tier: `tiny` \| `small`  
- Optional: attach/size GCS-backed volume  
- Trigger pull/extract on a host + replace/wake instance  

No separate HTTP API or API tokens in v1.

---

## 9. Control plane

| Component | Role |
|-----------|------|
| **SSH gateway** | Client SSH; `join` / `deploy`; authz; loading UI; cert mint; proxy; migrate buffer |
| **API** | Internal control API for gateway/orchestrator/agent (not public deploy API) |
| **Orchestrator** | Placement, wake/sleep, migrate/drain, quotas, lazy fortune create |
| **Host agent** | Image→rootfs, inject CA, Firecracker lifecycle, volumes, probes, snapshots |
| **Firestore** | Users, keys, apps, placement pointers, quota counters, metadata |
| **GCS** | Idle/migrate snapshots + volume bytes |
| **Secret Manager** | Gateway host key; user CA signing key |

### Infra

- **Host MIG** + host agent + Firecracker/jailer.  
- **Single gateway VM** in v1.  
- Terraform + **terraform-provider-ko** for platform Go services only.  
- One region.  
- Shared platform kernel artifact for all microVMs.  
- Global egress allowlist enforced on the host data path.

---

## 10. Networking & security

- Public ingress: SSH to gateway only.  
- MicroVMs private (tap/CNI); not Internet-reachable.  
- Egress: global allowlist.  
- No app-to-app net; no port forwarding.  
- Connection traces: metadata only (user, app, timings, byte counts, errors) —
  never session payload.  
- No account recovery in v1.  
- Gateway host key: single stable key (published fingerprint in docs); host CA later.

---

## 11. MVP vertical slice

1. Terraform + ko: Firestore, GCS, Secrets, host MIG, single gateway, orchestrator, agent.  
2. Platform user CA + inject path; shared kernel.  
3. Platform fortune image (SSH server verifying CA).  
4. `ssh join@foo.com` → register alice + key.  
5. `ssh fortune@foo.com` → lazy create → wake (loading UI) → cert hop → fortune.  
6. Idle → snapshot-on-sleep; reconnect restores.  
7. `ssh deploy@foo.com` → deploy a second digest-pinned image as `myapp`.  
8. Drain a host with freeze-buffered migrate.

---

## 12. Still open / next forks

1. **Adding a second key** — exact `join` UX when already registered (must present
   an existing key to authorize a new one?).  
2. **OCI → rootfs pipeline** — unpack, size limits, caching, when to build the
   first “base” snapshot for an image digest.  
3. **Idle timeout numbers** — e.g. sleep after N minutes with zero sessions.  
4. **Freeze buffer cap** — max migrate hold before forced reconnect.  
5. **Tier numbers** — concrete vCPU/RAM/disk for `tiny` / `small`.  
6. **Global allowlist contents** — what destinations ship by default.  
7. **Internal API auth** — mTLS between gateway/orchestrator/agent.  
8. **Repo layout** in this monorepo when implementation starts.  
9. **Threat model** — tenant breakout, snapshot confidentiality in GCS, CA theft.

---

## 13. Example session

```bash
# Brand new user
ssh join@foo.com
# TUI: found SHA256:…, pick username "alice"
# → You're alice. Try: ssh fortune@foo.com

# Same key, re-join — no username prompt
ssh join@foo.com
# → manage keys

# Unknown key on an app
ssh fortune@foo.com   # reject → hint to join

# First fortune connect (lazy create + maybe cold restore/boot)
ssh fortune@foo.com
# Starting fortune…
# <session>

# Custom app
ssh deploy@foo.com
# → create myapp from ghcr.io/me/myapp@sha256:…
ssh myapp@foo.com
```
