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
| Deploy vs sessions (v1) | Default: **route new → new, drain old, kick after timeout**; opt-in **kick now** |
| Deploy vs sessions (later) | Maintenance mode; explicit blue/green promote + rollback |
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
| Abuse prevention | **Platform-enforced** at gateway/orchestrator; apps assume admission already happened |
| Sessions / user / app | **Max 1** — second connect is **rejected** (not replaced) |
| Join spam | **Rate limits in v1**; invite codes later if needed |
| Account recovery | **None in v1** (lost all keys → new username / support-only) |
| Repo layout | **`sshcloud/`** — one Go module; `cmd/{gateway,orchestrator,agent,api}` |

### Starter quotas & rate limits

| Limit | Default |
|-------|---------|
| Apps / user | 5 |
| Concurrent sessions / user / app | **1** (reject if busy) |
| Concurrent sessions / user (all apps) | 5 |
| Awake microVMs / user | 2 |
| Wakes / user / hour | 30 |
| Deploys / user / hour | 10 |
| In-flight deploy / app | 1 |
| Joins / source IP / 24h | 3 |
| Joins / source /24 / 24h | 20 |
| SSH handshakes / source IP / minute | modest gateway cap (tune in ops) |
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
6. SSH-based `deploy` (menu or `deploy@`) for custom digest-pinned images,
   with drain/kick controls for active sessions.
7. Snapshot migrate with best-effort session hold for host drain/bin-pack.
8. Quotas + platform abuse controls; no billing yet.

### Non-goals (v1)

- HTTP/HTTPS ingress or deploy API
- `ssh owner.app@…` / custom SSH hostnames
- SSH port forwarding / reverse tunnels
- Private app-to-app networking
- Per-app egress rules
- User-facing snapshot save/restore
- Account recovery / email identity
- Invite-only join (rate limits first; invites if abuse appears)
- Multi-region / HA gateway
- Platform-provided OpenSSH wrapper (apps bring any cert-verifying SSH server)
- Orgs/teams; cross-user app access
- Full SSH channel proxy beyond session/PTY/exec/subsystem
- App-implemented connection governors for the same platform user (platform’s job)

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

- Unknown key → join (never silent reject on deep links).
- Known key → that user’s apps only (no cross-user).
- `ssh fortune@foo.com` always means **the connecting user’s** `fortune`.
- At most **one** concurrent session per user per app; extras rejected at the gateway.

### What apps may assume (abuse)

Apps should **not** implement their own “is this user connecting too often?” logic for
platform identity. The gateway guarantees:

1. The cert principal is a registered user who passed join abuse checks.  
2. This session was admitted under concurrency and rate-limit policy.  
3. A second concurrent session for the same user×app will not be proxied
   (app will not see it).  

Apps may still enforce **app-domain** rules later (e.g. multi-tenant git authz)
when cross-user access exists; that is separate from platform anti-abuse.

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

**Implemented in `sshcloud/` (host-local path first):**
- Firecracker `Pause` → `CreateSnapshot` → kill VMM; wake via `snapshot/load` + `Resume`.
- Package: `vm.state` + `vm.mem` + `rootfs.ext4` + `meta.json` (network identity).
- Stores: `internal/snapshot.LocalStore` and `GCSStore`; agent `-snap-dir` /
  `-gcs-bucket`, idle via `-idle` (default 5m, `0` disables).
- TAP kept across sleep; `Ensure` / `POST /v1/instances/wake` restores.
- Gateway wake loading TUI: `DialWithLoading` prints `Starting <app>…` while
  Ensure/Adopt runs; dial via `-agent-url` or placement-aware
  `-orchestrator-url` (`POST /v1/ensure`).
- Still open: session-aware idle (today: agent `LastUsed` on Ensure, not live
  SSH connection count). Cross-host migrate: see below.

### Migration (host drain / bin-pack)

1. Freeze microVM (gateway **buffers** client I/O, time-capped)  
2. Snapshot to GCS  
3. Restore on target host  
4. Re-point gateway routing  
5. Thaw; if over cap → force reconnect  

**Implemented in `sshcloud/` (control-plane path; no live SSH buffer yet):**
- Agent: `Sleep` → `Evict` (drop local TAP/workdir, **keep** shared snapshot) →
  target `Adopt` (restore from store with new local TAP name, same guest IP/MAC).
- `internal/placement` maps `user/app` → host ID; `internal/migrate.Migrator`
  orchestrates the cutover with best-effort rollback Adopt on the source.
- `cmd/orchestrator` exposes `POST /v1/migrate` and placement-aware `POST /v1/ensure`.
- Gateway `-orchestrator-url` dials via orchestrator Ensure (vs single-host
  `-agent-url`).
- Migrate orchestration unit test: httptest agent stubs
  (`TestMigrateOrchestration`) — not a KVM stand-in.
- **Real KVM e2e in CI:** GitHub `ubuntu-latest` exposes `/dev/kvm` (nested
  virt on free Linux runners). Job `sshcloud-kvm` in `test.yml` runs
  `hack/run-kvm-e2e.sh` → `go test -tags=kvm` sleep/wake + migrate when
  `sshcloud/` changes; the script fails if any test is skipped.
- Placement: memory (default) or Firestore (`placement.Firestore`).
- Still open: gateway I/O freeze buffer during migrate, force-reconnect on
  timeout, session pin invalidation.

---

## 8. Deploy: `ssh deploy@foo.com` (or menu → deploy)

Gateway built-in (not a microVM). Authenticated by the same cloud-wide keys.
Reachable as a deep link or as a row in the app menu.

Responsibilities (v1 sketch):

- Create/update app name in the user’s namespace  
- Set image **digest** (reject unpinned tags)  
- Choose tier: `tiny` \| `small`  
- Optional: attach/size GCS-backed volume  
- Choose **session strategy** (below)  
- Trigger pull/extract on a host + cut over per strategy  
- Warn when app name collides with common local usernames (hub footgun)

**Implemented in `sshcloud/` (registration path):**
- `gateway.RunDeploy` TUI (menu row + `ActionDeploy` / `ssh deploy@…`)
- Digest-pinned image validation (`internal/image.ValidateDigestPinned`)
- `store.UpsertApp` / `GetApp` (tier + session strategy); rejects platform demos
- Hub-footgun warning for common local usernames
- OCI pull/extract → ext4: `sshcloud/internal/ocirootfs` (go-containerregistry;
  digest cache; whiteouts; 1 GiB unpack cap); agent Ensure `"image"` +
  `RootfsResolver`
- Dual-instance cutover: `internal/cutover` (drain + kick-on-timeout default,
  kick-now); gateway pins sessions to `ActiveGen`; agent instances are
  `app` or `app.gen`; draining gens set `no_idle`.
- Still open: volumes

No separate HTTP API or API tokens in v1.

### Active sessions during deploy

A **new image digest** is a new rootfs. Unlike host migration (same microVM
state), deploy cannot transparently keep process memory across cutover. The
gateway **pins** each proxied session to an **instance** (microVM). Deploy
controls where **new** sessions go and when **old** instances die.

Building blocks:

| Action | Meaning |
|--------|---------|
| **Cordon** | Stop sending new sessions to an instance |
| **Drain** | Wait for that instance’s active sessions → 0 |
| **Kick** | Close proxied sessions (short PTY notice when possible) |
| **Route** | New sessions go to the chosen instance |

#### v1 strategies (deployer options)

| Strategy | Behavior | When |
|----------|----------|------|
| **Drain + kick-on-timeout** *(default)* | Boot new instance alongside old; cordon old; **new sessions → new**; existing stay on old until disconnect or `drain-timeout`, then kick stragglers and destroy old | Normal deploys |
| **Kick now** | Notice + kick all on old; cut over immediately (or recreate) | Fortune/demos, broken apps, deployer impatience |

Deploy UX sketch:

```text
On deploy, active sessions:
  (•) route new to new, drain old; kick after timeout
  ( ) kick now
```

(CLI-shaped later: default drain; `--kick` for immediate.)

#### Later strategies (designed for, not v1)

| Strategy | Behavior |
|----------|----------|
| **Maintenance** | Cordon all (new sessions see “deploying…”); kick or drain old; boot new; uncordon — no two-version overlap |
| **Explicit promote / rollback** | Deploy boots **green** without shifting traffic; promote flips route; keep previous digest briefly for rollback |
| **Instant flip, lazy destroy** | New→new immediately; old dies on idle or TTL (split-brain revisions — avoid for singleton worlds) |

#### Constraints

- **Dual-instance burst:** drain strategies need a temporary extra awake microVM
  (quota exemption or awake+1 during deploy).
- **R/W volumes:** two instances cannot mount the same volume R/W → volume apps
  fall back to **kick** or **maintenance** (no side-by-side drain) until
  volume fork/clone exists.
- **No live session morph** onto a new image; clients reconnect after kick.
- **Don’t snapshot-sleep** a draining instance until drain/kick completes.
- Menu/status should show draining state (e.g. `myapp — draining, 3 sessions`).
- Traces (metadata): `deploy_id`, `instance_id`, cordon/drain/kick events.

#### Out of scope

Live-upgrading a PTY/git session onto a new digest without reconnect — not
supported; drain only delays the reconnect until the client leaves (or timeout).

---

## 9. Control plane

| Component | Role |
|-----------|------|
| **SSH gateway** | Client SSH; join / menu / deploy; routing; handoff; session admit/reject; rate limits; session→instance pin; cordon/drain/kick; cert mint; proxy |
| **API** | Internal control API for gateway/orchestrator/agent (not public deploy API) |
| **Orchestrator** | Placement, wake/sleep, host migrate/drain, deploy cutover, quotas / abuse counters, lazy fortune create |
| **Host agent** | Image→rootfs, inject CA, Firecracker lifecycle, volumes, probes, snapshots |
| **Firestore** | Users, keys, apps, placement pointers, quota counters, metadata |
| **GCS** | Idle/migrate snapshots + volume bytes |
| **Secret Manager** | Gateway host key; user CA signing key |

**Implemented in `sshcloud/`:**
- `store.Firestore` — `keys/{fp}`, `users/{id}`, `users/{id}/apps/{name}`;
  gateway `-firestore-project` (default remains in-memory).
- `placement.Firestore` — `placement/{user__app}` → host ID;
  orchestrator `-firestore-project`.
- Emulator tests: `hack/run-firestore-tests.sh` (skips in plain `go test`
  without `FIRESTORE_EMULATOR_HOST`).
- Terraform provisions the Native `(default)` database (`sshcloud/terraform`).
- Still open: quota counters.

### Infra

- **Host MIG** + host agent + Firecracker/jailer.  
- **Single gateway VM** in v1.  
- Terraform + **terraform-provider-ko** for platform Go services only.  
- One region.  
- Shared platform kernel artifact for all microVMs.  
- Global egress allowlist enforced on the host data path.

**Implemented in `sshcloud/terraform/` (first environment):**
- `ko_build` images: gateway, orchestrator, agent, api (api image only; no VM yet)
- Firestore Native `(default)`, snapshot + asset GCS buckets, Artifact Registry
- Secret Manager: gateway host key + user CA (`tls_private_key` → secret versions)
- Gateway GCE VM (public `:22`), orchestrator VM (VPC), nested-virt agent MIG
- Orchestrator `-hosts-file` refresh from MIG membership (`GET /v1/hosts`)
- Still open: egress allowlist on the data path, IAP-only hardening, key rotation
  out of Terraform state. OCI→rootfs on agents: `internal/ocirootfs` + Ensure
  `"image"` hook; deploy cutover pre-boots the new gen with that image.

---

## 10. Abuse prevention

Abuse controls live in the **gateway + orchestrator**. App images must assume
admission already happened and must not be the primary rate limiter (they often
won’t see real client IPs—only the gateway hop).

### Join / account creation

- Rate-limit successful joins and username-allocation attempts by **source IP**
  and **IP /24** (defaults in the table above).  
- Slow down repeated failures in the join TUI.  
- Reserved usernames cannot be claimed.  
- **Invites:** not required in v1; add invite codes if rate limits are bypassed
  in the wild.  
- Creating many keypairs is expected; limits must be on **join completion** and
  **allocation**, not on TCP alone.

### Sessions

- **Max one concurrent session per (user, app)** normally; during drain cutover,
  **one session per generation** (at most two: old + new).  
- If a session is already active on that generation, a new `ssh app@foo.com` (or menu handoff) is
  **rejected** with a clear message (e.g. already connected — disconnect the
  other session first). **No replace/kick of the existing session** on connect.  
- Deploy **kick** / drain-timeout kick remains a separate, explicit deploy path.  
- Cap total concurrent sessions per user across apps.  
- Gateway connection rate limits per IP to blunt handshake storms against menu/join.

Note: v1 apps are owner-only, so this is effectively one interactive session per
app. Multi-player / multi-user apps later will need a deliberate raise of this
cap (or per-guest principals)—not silent app-side accept of duplicates.

### Wake, deploy, storage

- Wakes/hour and deploys/hour quotas.  
- One in-flight deploy per app.  
- Snapshot/volume storage cap; retain policy for idle snapshots (ops detail).  
- Max image size at deploy (open number — §12).  
- Dual-instance drain burst is a controlled quota exception, not unlimited.

### Signals

Metadata traces/metrics: join accepts/rejects, session rejects (busy), rate-limit
hits, wake/deploy denials — still **no session bytes**.

---

## 11. Networking & security

- Public ingress: SSH to gateway only.  
- MicroVMs private (tap/CNI); not Internet-reachable.  
- Egress: global allowlist.  
- No app-to-app net; no port forwarding.  
- Connection traces: metadata only (user, app, timings, byte counts, errors) —
  never session payload.  
- No account recovery in v1.  
- Gateway host key: single stable key (published fingerprint in docs); host CA later.  
- Abuse controls: §10.

---

## 12. MVP vertical slice

1. ~~Terraform + ko: Firestore, GCS, Secrets, host MIG, single gateway, orchestrator, agent.~~
   (`sshcloud/terraform/`; upload Firecracker assets after apply).  
2. Platform user CA + inject path; shared kernel.  
3. Platform fortune image (SSH server verifying CA).  
4. `ssh foo.com` (unknown key) → join → menu (join rate-limited).  
5. Menu → fortune (lazy create) → wake (loading UI) → cert hop → session.  
6. Second concurrent `ssh fortune@foo.com` → **rejected** (session busy).  
7. Idle → snapshot-on-sleep; reconnect restores.  
8. Menu → deploy (or `deploy@`) → second digest-pinned app `myapp`.  
9. Deploy with active sessions: default drain + kick-on-timeout; `--kick` path.  
10. Drain a host with freeze-buffered migrate.

---

## 13. Still open / next forks

1. **Adding a second key** — exact `join` UX when already registered (must present
   an existing key to authorize a new one?).  
2. ~~**OCI → rootfs pipeline**~~ — `sshcloud/internal/ocirootfs.Materialize`
   pulls digest-pinned public images (linux/amd64), unpacks with OCI whiteouts,
   builds cached ext4 (`internal/rootfs.BuildFromDir`). Agent Ensure accepts
   `"image"` and resolves via `Config.RootfsResolver`. Still open: first warm
   snapshot per digest, guest `init=` from image config. 
3. ~~**Idle timeout numbers**~~ — agent default **5 minutes** (`-idle`); refine
   when to count “zero sessions” vs last Ensure touch.  
4. **Freeze buffer cap** — max migrate hold before forced reconnect.  
5. ~~**Deploy drain-timeout default**~~ — gateway `-drain-timeout` default **5m**;
   per-deploy TUI override not in v1 (strategy only).  
6. **Tier numbers** — concrete vCPU/RAM/disk for `tiny` / `small`.  
7. **Global allowlist contents** — what destinations ship by default.  
8. **Internal API auth** — mTLS between gateway/orchestrator/agent.  
9. ~~**Repo layout**~~ — **`sshcloud/`** single Go module (`cmd/{gateway,orchestrator,agent,api}`, `internal/…`, `images/fortune`, `terraform/`).  
10. **Threat model** — tenant breakout, snapshot confidentiality in GCS, CA theft.  
11. **Hub footgun UX** — deploy-time warnings / `~/.ssh/config` docs when local
    username collides with an app name (see §3).  
12. **Deploy promote/rollback UX** — when to add explicit blue/green beyond
    default drain cutover (see §8).  
13. **Invite codes** — trigger criteria / UX when join rate limits aren’t enough.  
14. **Stuck session UX** — user guidance when reject-because-busy and the other
    client is a dead laptop (idle timeout interaction).

---

## 14. Example session

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

# Second concurrent connect while first still up — rejected
ssh fortune@foo.com
# → busy: already connected; disconnect the other session first

# Explicit menu if local username collides with an app
ssh menu@foo.com

# Key management
ssh join@foo.com

# Custom app
ssh deploy@foo.com
# → create myapp from ghcr.io/me/myapp@sha256:…
ssh myapp@foo.com
```
