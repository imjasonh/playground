# Design: SSH App Cloud

> **Status: design / pre-implementation.** Working name **SSH App Cloud** — a
> public PaaS where apps deploy an OCI image that speaks SSH on port 22.
> Default entry is `ssh foo.com` (hub: join or app menu); deep links use
> `ssh <app>@foo.com` (owner inferred from the presenting key). No HTTP.
> Runtime is Firecracker microVMs on a warm GCE host MIG, with platform
> services in Go + Terraform (`terraform-provider-ko`).

### Locked decisions

| Topic | Decision |
|-------|----------|
| Product | Public PaaS (self-serve), individual developers in v1 |
| Default entry | `ssh foo.com` → **join** if key unknown, else **app menu** (select → in-session handoff) |
| Deep link | `ssh <app>@foo.com` — straight to that app; owner inferred from key |
| Naming | App names are per-user namespace (each user can have their own `fortune`) |
| Auth (client→gateway) | SSH public keys registered **cloud-wide** per user |
| Auth (gateway→app) | Gateway mints **short-lived SSH user certs** asserting the user; apps verify via platform CA |
| CA delivery | Platform **injects** user CA at boot (`/run/platform/ssh_user_ca.pub`); images need not bake it in |
| App SSH server | Any SSH server that can verify platform user certs — **not** OpenSSH-specific |
| Onboarding | Join TUI via unknown key on any user, or `ssh join@foo.com` |
| Deploy | `ssh deploy@foo.com` or select **deploy** from the menu |
| Platform users (MVP) | `join`, `deploy`, `menu` (+ fallthrough-to-menu); `help` / `whoami` / `status` later |
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
Users never get a shell on the host. Primary UX:

```bash
ssh foo.com              # join (new key) or menu (known key)
ssh fortune@foo.com      # deep link straight to an app
```

The gateway maps key → user → app, waking a snapshotted microVM if needed and
showing a short loading UI before handoff.

### One-liner

> Deploy an SSH-speaking OCI image; we run it in a Firecracker microVM.
> `ssh foo.com` for the hub; `ssh app@foo.com` to go straight in.

---

## 2. Goals & non-goals

### Goals (v1)

1. **`ssh foo.com` → join → menu → fortune** vertical slice (lazy fortune).
2. Deep links: `ssh <app>@foo.com` skips the menu.
3. Strong isolation: one microVM per app instance.
4. Snapshot-on-sleep; warm GCE hosts; gateway-held wake with loading TUI.
5. Gateway-minted SSH user certs into apps (keys rotate without touching VMs).
6. SSH-based `deploy` (menu or `deploy@`) for custom digest-pinned images.
7. Snapshot migrate with best-effort session hold for host drain/bin-pack.
8. Quotas; no billing yet.

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
  `menu`, and later `help`, `status`, `whoami`, plus `root`, `admin`, …

### SSH username routing

```text
# Key unknown (any username, including bare `ssh foo.com`)
*        → join TUI

# Key known
join     → key management (no username re-prompt)
deploy   → deploy UX
menu     → app menu (explicit)
<app>    → if user has this app (or platform demo like fortune) → straight to app
<other>  → fall through to app menu
```

Bare `ssh foo.com` sends the **local account name** as the SSH user (OpenSSH
default). That usually does not match an app → **menu**. Deep link with
`ssh fortune@foo.com` when you want to skip the hub.

Username charset (apps + join-chosen owner id): `[a-z][a-z0-9-]{2,31}`.

### Footgun: local username vs app name

> **Potential confusion (document for later):** `ssh foo.com` uses the client’s
> local username as the SSH user. If the user has deployed an app with **that
> same name**, the gateway will **deep-link straight into the app** and skip
> the menu. Example: laptop account `dev`, app named `dev` → bare `ssh foo.com`
> never shows the hub.
>
> Mitigations to consider later: reserved/`menu` alias in docs and
> `~/.ssh/config`, warn at `deploy` time when the app name matches common
> local account names, or offer a “always show menu for bare connect” pref.
> For v1, accept the edge case; tell people `ssh menu@foo.com` when in doubt.

---

## 4. Hub: join + app menu

`join` and `menu` are **gateway built-ins**, not microVMs. Selecting an app
from the menu **hands off in the same SSH session** (PTY menu → optional
loading UI → proxy to the app), same path as a deep link after wake.

### Join flow

```text
ssh foo.com          # or ssh join@foo.com — unknown key
  │
  ├─ Gateway accepts the offered public key (special auth mode)
  ├─ Lookup key fingerprint → unknown
  ├─ Bubble Tea TUI: pick username once → create user + bind key
  └─ Continue into app menu (same session)
```

Known key on `join@`:

```text
ssh join@foo.com     # known key — no username prompt
  └─ manage keys (add/list/revoke)
```

### App menu flow

```text
ssh foo.com          # known key, local user ≠ an app name
ssh menu@foo.com     # explicit
  │
  ├─ List: user's apps + deploy + fortune (demo; lazy-create if needed)
  ├─ Select deploy → deploy TUI (same session)
  └─ Select app    → wake/loading if needed → cert hop → app session
```

### Key model

- Keys are owned by the **user**, cloud-wide, reusable across all their apps.
- Re-join with the same key never asks for a username again.
- Adding a machine: from an already-authenticated `join` session (interim).
  Exact UX for authorizing a *new* key still open (§12).

### Fortune requires joining first

Unknown keys always get the join TUI (never a raw reject on deep links).
Fortune is **not** created at join. First connect to fortune (menu select or
`ssh fortune@foo.com`) lazy-creates the app (platform image, `tiny`) and wakes it.

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
  │  ssh foo.com  /  ssh fortune@foo.com
  ▼
SSH Gateway (single VM in v1; shared host key)
  │  1) auth key → user (else join TUI)
  │  2) route: menu | deploy | deep-link app | fallthrough→menu
  │  3) on app select / deep link:
  │       resolve app (lazy-create fortune if needed)
  │       if sleeping: loading TUI; restore snapshot (retry in-place)
  │       mint user cert; dial microVM :22
  │       proxy session/PTY/exec/subsystem (in-session handoff from menu)
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

## 8. Deploy: `ssh deploy@foo.com` (or menu → deploy)

Gateway built-in (not a microVM). Authenticated by the same cloud-wide keys.
Reachable as a deep link or as a row in the app menu.

Responsibilities (v1 sketch):

- Create/update app name in the user’s namespace  
- Set image **digest** (reject unpinned tags)  
- Choose tier: `tiny` \| `small`  
- Optional: attach/size GCS-backed volume  
- Trigger pull/extract on a host + replace/wake instance  
- Later: warn when app name collides with common local usernames (hub footgun)

No separate HTTP API or API tokens in v1.

---

## 9. Control plane

| Component | Role |
|-----------|------|
| **SSH gateway** | Client SSH; join / menu / deploy; routing fallthrough; in-session handoff; authz; loading UI; cert mint; proxy; migrate buffer |
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
4. `ssh foo.com` (unknown key) → join → menu.  
5. Menu → fortune (lazy create) → wake (loading UI) → cert hop → session.  
6. `ssh fortune@foo.com` deep link works too.  
7. Idle → snapshot-on-sleep; reconnect restores.  
8. Menu → deploy (or `deploy@`) → second digest-pinned app `myapp`.  
9. Drain a host with freeze-buffered migrate.

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
10. **Hub footgun UX** — deploy-time warnings / `~/.ssh/config` docs when local
    username collides with an app name (see §3).

---

## 13. Example session

```bash
# Brand new user — bare connect
ssh foo.com
# join TUI: found SHA256:…, pick username "alice"
# → app menu: fortune, deploy, …

# Select fortune (lazy create + wake)
# Starting fortune…
# <session>

# Later — hub again
ssh foo.com
# → app menu (known key)

# Deep link skips menu
ssh fortune@foo.com

# Explicit menu if local username collides with an app
ssh menu@foo.com

# Key management
ssh join@foo.com

# Custom app
ssh deploy@foo.com
# → create myapp from ghcr.io/me/myapp@sha256:…
ssh myapp@foo.com
```
