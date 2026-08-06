# Design: SSH App Cloud

> **Status: implementation prototype / private smoke tests only.** Working name
> **SSH App Cloud** — a
> public PaaS where apps deploy an OCI image that speaks SSH on port 22.
> Default entry is `ssh foo.com` (hub: join or app menu); deep links use
> `ssh <app>@foo.com` (owner inferred from the presenting key). No HTTP.
> Runtime is Firecracker microVMs on a warm GCE host MIG, with platform
> services in Go + Terraform (`terraform-provider-ko`).
>
> A review checkpoint found that the package-level vertical slice is ahead of
> its production safety boundary. Public ingress remains closed by default.
> The jailer/helper host boundary and workload-authenticated control plane are
> now implemented, but egress policy, distributed deploy-state CAS, and operator-owned GCP
> verification remain launch blockers—not optional polish. Manual rotation
> procedures and non-secret inspectors now exist, but Terraform still contains
> the SSH/control private keys and no production rotation drill has run.

Key/certificate/identity/KMS rotation and Terraform-state operations:
[`sshcloud/docs/key-rotation-runbook.md`](../sshcloud/docs/key-rotation-runbook.md).

### Review constraints

- Terraform `local-exec` SSH deployment is retained only as an opt-in fortune
  smoke test. Terraform cannot be the durable app reconciler: remote success
  can be lost, SSH is imperative, and app state can drift independently.
- Registry support is constrained to an operator allowlist. A syntactically
  valid digest is not sufficient; arbitrary registry hosts turn deploy into
  control-plane SSRF.
- One in-process gateway can serialize deploy/admission for this prototype.
  Multiple gateways require Firestore CAS/leases before they are safe.
- Snapshot migrate can preserve the outer client channel with bounded
  freeze/thaw and host-drain reconciliation. It intentionally reconnects a new
  backend SSH session; transparent app-session preservation is not promised
  without a migratable/routed dataplane.
- `tiny`/`small`, exec/subsystem, quotas, and “strong isolation” are product
  claims only when their corresponding enforcement paths are deployed and
  tested end to end.

### Locked decisions

| Topic | Decision |
|-------|----------|
| Product | Public PaaS (self-serve), individual developers in v1 |
| Default entry | `ssh foo.com` → **join** if key unknown, else **app menu** (select → in-session handoff) |
| Deep link | `ssh <app>@foo.com` — straight to that app; owner inferred from key |
| Naming | App names are per-user namespace (each user can have their own `fortune`) |
| Auth (client→gateway) | SSH public keys registered **cloud-wide** per user, gated by the operator access policy |
| Auth (gateway→app) | Gateway mints **short-lived SSH user certs** asserting the user; apps verify via platform CA |
| CA delivery | Platform **injects** user CA at boot (`/run/platform/ssh_user_ca.pub`); images need not bake it in |
| App SSH server | Any SSH server that can verify platform user certs — **not** OpenSSH-specific |
| Onboarding | Policy-admitted unknown key gets the join TUI on any user, or `ssh join@foo.com` |
| Deploy | Policy-authorized registered user uses `ssh deploy@foo.com` or **deploy** in the menu |
| Deploy vs sessions (v1) | Default: **route new → new, drain old, kick after timeout**; opt-in **kick now** |
| Deploy vs sessions (later) | Maintenance mode; explicit blue/green promote + rollback |
| Platform users (MVP) | `join`, `deploy`, `menu` (+ fallthrough-to-menu); `help` / `whoami` / `status` later |
| First sample app | `fortune` — **requires joining first**; **deployed** like any other digest-pinned app |
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
| Observability | Structured platform/app logs, aggregate metrics, **metadata-only** events; never SSH channel bytes/commands/env/signals/replays |
| Quotas | Enforced in v1 (starter defaults below); billing later |
| Abuse prevention | **Platform-enforced** at gateway/orchestrator; apps assume admission already happened |
| Sessions / user / app | **Max 1** — second connect is **rejected** (not replaced) |
| Join spam | **Rate limits in v1**; invite codes later if needed |
| Account recovery | **None in v1** (lost all keys → new username / support-only) |
| Repo layout | **`sshcloud/`** — one Go module; `cmd/{gateway,orchestrator,agent}` plus guest/app tools |

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

1. **`ssh foo.com` → join → deploy fortune → menu → fortune** vertical slice.
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
# First: reject the connection clearly unless its key passes join/use policy.

# Admitted key unknown (any username, including bare `ssh foo.com`)
*        → join TUI

# Key known
join     → key management (no username re-prompt)
deploy   → deploy UX
menu     → app menu (explicit)
<app>    → if user has this app (deployed) → straight to app
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
  ├─ Gateway checks the operator join/use policy for the offered public key
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
  ├─ List: user's deployed apps + deploy
  ├─ Select deploy → deploy TUI (same session)
  └─ Select app    → wake/loading if needed → cert hop → app session
```

### Key model

- Keys are owned by the **user**, cloud-wide, reusable across all their apps.
- Terraform takes full OpenSSH public key lines and the gateway derives SHA256
  fingerprints; operators do not configure fingerprint/digest strings.
- `join_mode=allowlist` admits member and deployer keys (deployer implies
  member); `join_mode=open` admits every key for join/use.
- `deploy_mode=allowlist` admits deployer keys only;
  `deploy_mode=all-users` admits every registered user.
- Policy versions refresh without an image rebuild. Revocation blocks new
  routes after refresh and closes open SSH connections on the next 30-second
  policy check, but does not erase registration or cancel a deploy after its
  final authorization check; remove a deployer from both lists to revoke its
  implied membership in allowlist mode.
- Re-join with the same key never asks for a username again.
- Adding a machine: from an already-authenticated `join` session (interim).
  Exact UX for authorizing a *new* key still open (§12).

### Fortune is a normal deployed app

Policy-admitted unknown keys get the join TUI; unadmitted keys receive a clear
forbidden exit before routing.
`fortune` is **not** a platform builtin and is **not** lazy-created. Deploy it
with `ssh deploy@…` (or the menu) using a digest-pinned OCI image — Terraform
builds one via `ko_build.fortune`. Until then, `ssh fortune@foo.com` falls
through to the hub (unknown app).

---

## 5. App contract

| Concern | Rule |
|--------|------|
| Artifact | Allowlisted, digest-pinned Linux/amd64 OCI image; root `User`, no OCI volumes |
| Process | PID 1 listens on TCP `:22` (SSH) |
| Server | Any SSH implementation that verifies **platform user certs** |
| CA | Read platform user CA from `/run/platform/ssh_user_ca.pub` (injected) |
| Host identity | Present `/run/platform/ssh_host_ed25519_key` (per instance/generation, injected) |
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

The gateway preserves shell/exec/subsystem start payloads, PTY modes and
dimensions, env ordering, resize/signal requests, stdout/stderr separation, and
exit-status/exit-signal payloads. Only interactive PTY shells use best-effort
freeze/reconnect; exec, subsystem, and non-PTY sessions are force-disconnected
rather than replayed.

The current image contract is intentionally narrower than a container runtime:
guestinit mounts basic pseudo-filesystems, but OCI UID/GID/xattrs, non-root
users, declared volumes, cgroups, DNS/egress, and StopSignal supervision remain
unsupported and are rejected or documented rather than silently promised.

### Access (v1)

- Production starts private (`allowlist` join + `allowlist` deploy). Operators
  can stage through open join + allowlisted deploy, then open join +
  all-registered-user deploy.
- Admitted unknown key → join; denied key → explicit forbidden exit.
- Admitted known key → that user’s apps only (no cross-user).
- The same policy is rechecked on direct routes, menu handoffs, and immediately
  before deploy mutation.
- `ssh fortune@foo.com` always means **the connecting user’s** `fortune`.
- At most **one** concurrent session per user per app; extras rejected at the gateway.

### What apps may assume (abuse)

Apps should **not** implement their own “is this user connecting too often?” logic for
platform identity. The gateway guarantees:

1. The cert principal is a registered user who passed join abuse checks.  
2. This session was admitted under concurrency and rate-limit policy.  
3. A second concurrent session for the same user×app will not be proxied
   (app will not see it).  

Items 1–2 describe the launch contract, not current prototype behavior:
concurrency is enforced today, but join/session/wake/deploy quotas are not.

Apps may still enforce **app-domain** rules later (e.g. multi-tenant git authz)
when cross-user access exists; that is separate from platform anti-abuse.

---

## 6. Auth hops & certs

```text
Client key
  → Gateway: operator policy + Firestore-registered key lookup
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
  │  1) policy-admit key → user (else join TUI if unregistered)
  │  2) route: menu | deploy | deep-link app | fallthrough→menu
  │  3) on app select / deep link:
  │       resolve app (must already be deployed)
  │       if sleeping: loading TUI; restore snapshot (retry in-place)
  │       mint user cert; dial microVM :22
  │       proxy session/PTY/exec/subsystem (in-session handoff from menu)
  ▼
GCE host MIG ── host agent ── Firecracker ── app :22
                    │
                    └─ TLS 1.3 mTLS + GCE identity ─ snapshotd ─ CMEK GCS/KMS
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
- Stores: local/KVM uses `internal/snapshot.LocalStore`; production agents
  require `RemoteStore` + `-snapshotd-url` and have no GCS/KMS snapshot IAM.
  Idle remains `-idle` (default 5m, `0` disables).
- Snapshot refs are structured `(user, app, generation)` values. snapshotd
  authenticates agent-role TLS 1.3 mTLS plus the snapshot audience GCE token,
  extracts the verified exact instance name/ID, and checks every method against
  the dedicated placement Firestore database and a non-expired
  ensure/stop/migrate/drain operation fence. Mutation authorization returns the
  exact record revision, operation ID/sequence, action, and caller incarnation;
  that fence is revalidated inside the envelope store immediately before the
  current-pointer publish/delete generation CAS. A source loses access as soon
  as placement commits to the target, even after a long staging/encryption run.
- Snapshot bytes are proxied. snapshotd validates the fixed four-entry archive,
  per-file/package limits, metadata identity/schema/layout, and then writes one
  immutable Tink v2 Streaming AEAD package using a fresh keyset. Cloud KMS wraps
  that keyset with tenant/app/generation/snapshot plus canonical metadata AAD.
  The immutable generation-pinned manifest metadata is authenticated before
  preflight use. A GCS generation CAS publishes `current.json` only after
  package + immutable manifest complete; the pointer retains exactly current
  and previous encrypted versions, and generation-qualified cleanup removes
  older object and pointer generations. The bucket also has a default CMEK.
- snapshotd rejects before reading package bytes when its disk-sized global
  weighted/concurrency guard or exact-agent-incarnation cap is full. Agent and
  snapshotd plaintext staging is removed immediately after publish/restore;
  static bounds, current use, rejections, and cleanup failures are exposed as
  aggregate diagnostics/metrics.
- TAP kept across sleep; `Ensure` / `POST /v1/instances/wake` restores.
- Gateway wake loading TUI: `DialWithLoading` prints `Starting <app>…` while
  Ensure/Adopt runs; dial via `-agent-url` or placement-aware
  `-orchestrator-url` (`POST /v1/ensure`).
- Active sessions and drains now hold an agent `no_idle` lease; release clears
  it. Still open: heartbeat/expiry so a crashed gateway cannot leave the hold
  set forever. Cross-host migrate: see below.

### Migration (host drain / bin-pack)

1. Freeze microVM (gateway **buffers** client I/O, time-capped)  
2. Snapshot to GCS  
3. Restore on target host  
4. Re-point gateway routing  
5. Thaw; if over cap → force reconnect  

**Implemented in `sshcloud/`:**
- Agent: `Sleep` → `Evict` (drop local TAP/workdir, **keep** shared snapshot) →
  target `Adopt` (restore deterministic paths/TAP, same guest IP/MAC).
- `internal/placement` maps `user/app` → host name + immutable GCE instance ID;
  `internal/migrate.Migrator`
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
- Firestore placement records carry revisioned, expiring operation leases.
  Wake/deploy/migrate cannot concurrently claim two hosts for one app.
- Drain/migrate phases, exact source/target instance IDs, and generations are
  journaled under the lease. An orchestrator restart reconciles expired ambiguous operations back
  to the authoritative source (or commits the prepared target if source died).
- Agents report allocatable/used/reserved CPU+memory and cordon state;
  unplaced apps and host drain use deterministic best-fit bin packing.
- Gateway freeze/thaw keeps the outer client channel open for a bounded window,
  disconnects the old backend hop, and reconnects after placement commits.
  Buffered input is bounded by SSH flow control; timeout kicks the client.
- `POST /v1/hosts/drain` cordons a host and moves all active/draining
  generations of each app under one placement lease.
- Production VMMs use Firecracker's portable `T2` CPU template; snapshot
  compatibility fencing covers VMM, kernel, and CPU baseline.
- Production agents do not launch Firecracker, open `/dev/kvm`, or hold
  `CAP_NET_ADMIN`. A mode-0600 Unix socket authenticated with `SO_PEERCRED`
  reaches a root helper that stages a fixed jail layout and invokes pinned
  Firecracker v1.10.1 only through its matching jailer. Each live VM gets a
  distinct derived UID/GID plus cgroup-v2 CPU/memory/pid limits. Jail
  snapshot/rootfs opens are anchored to a jail-root fd with openat2, `/run`
  becomes sandbox-non-writable after API socket creation, API connections must
  present the derived UID, and successful termination requires the complete
  derived cgroup to report unpopulated. A separate user/process with only
  `CAP_NET_ADMIN` owns fixed TAP/ruleset operations; IPv4 return acceptance is
  restricted to the exact derived guest-to-host address pair and IPv6 is
  drop-only.
- Snapshot schema 2 fences the runtime layout. Jailed state embeds
  `/rootfs.ext4` and `/snapshot/{vm.state,vm.mem}`, not an absolute host work
  path; old schema-1 packages are rejected.
- **Semantic limit:** the host-side TCP relay is not snapshot state. The outer
  client connection survives, but the app sees a fresh SSH session after thaw;
  transparent preservation would require a migratable/routed dataplane.

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
- Non-interactive deploy via SSH exec args:
  `ssh deploy@host fortune --image=repo@sha256:… [--tier=tiny] [--strategy=kick|drain] --yes`
  (exit status set for automation). Join: `ssh join@host demo`.
- Opt-in Terraform `demo.tf` smoke-test hack: `ko_build.fortune` digest →
  `local-exec` SSH join+deploy; input/script/infra changes replace the action
- Digest-pinned image validation plus registry allowlist (`internal/image`)
- `store.UpsertApp` / `GetApp` (tier + session strategy)
- Hub-footgun warning for common local usernames
- OCI pull/extract → ext4: `sshcloud/internal/ocirootfs` (go-containerregistry;
  digest cache; whiteouts; 1 GiB unpack cap; boot spec sidecar); agent Ensure
  `"image"` + `RootfsResolver`; PID 1 from image config via `cmd/guestinit`
- Serialized/idempotent dual-instance cutover: `internal/cutover` (drain + kick-on-timeout default,
  kick-now); gateway pins sessions to `ActiveGen`; agent instances are
  `app` or `app.gen`; draining gens set `no_idle`.
- Guest PID 1: always `guestinit` (`init=/platform-init` + `/platform-boot.json`).
  Spec from OCI image config — never a hardcoded platform default.
- Sample app `fortune` is a normal deploy target (`ko_build.fortune` +
  `TestDeployFortuneE2E`); no lazy platform demos.
- Still open: volumes

No separate public deploy HTTP API or user API tokens in v1.

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
| **API** | Internal control APIs for gateway/orchestrator/agent/snapshotd (not public deploy API) |
| **Orchestrator** | Placement, wake/sleep, host migrate/drain, deploy cutover, quotas / abuse counters |
| **Host agent** | Image→rootfs, inject CA, Firecracker lifecycle, volumes, probes, local snapshot creation/restore |
| **snapshotd** | Exact-instance snapshot authorization, package validation, envelope encryption, GCS proxy |
| **Firestore** | Users, keys, apps, placement pointers, quota counters, metadata |
| **GCS** | CMEK encrypted idle/migrate packages + volume bytes |
| **Cloud KMS** | Per-package keyset wrapping and snapshot-bucket CMEK |
| **Secret Manager** | Gateway host key; user CA signing key; versioned public-key access policy |

**Implemented in `sshcloud/`:**
- `store.Firestore` — `keys/{fp}`, `users/{id}`, `users/{id}/apps/{name}` in
  the dedicated user/app/quota database; gateway `-firestore-project` (default
  remains in-memory).
- `placement.Firestore` — `placement/{user__app}` → host name + immutable
  GCE instance ID, generation inventory, and operation fence in a separate
  dedicated placement/operation database;
  orchestrator `-firestore-project`.
- Emulator tests: `hack/run-firestore-tests.sh` (skips in plain `go test`
  without `FIRESTORE_EMULATOR_HOST`).
- Terraform provisions two named Native databases (`sshcloud-user` and
  `sshcloud-placement`), never `(default)`. Gateway IAM reaches only the user
  database; snapshotd has viewer-only access only to placement.
- Terraform publishes the staged SSH access policy to Secret Manager; the
  gateway host refreshes `latest` every minute and the process reloads the JSON
  file per decision. Missing/corrupt configured policy fails closed.
- Every production control request uses TLS 1.3 mutual authentication and a
  freshly fetched, audience-bound GCE metadata identity token. Servers verify
  the Google signature and standard claims, a 65-minute maximum token age plus
  clock skew (metadata may return a cached still-valid token), exact
  service-account email, and all full-format Compute Engine claims
  (including exact project ID/number). A static `Authorization: Bearer …`
  value has no authority.
- Control certificate URI identities are exact:
  `spiffe://sshcloud.internal/control/gateway`,
  `spiffe://sshcloud.internal/control/orchestrator`,
  `spiffe://sshcloud.internal/control/agent`, and
  `spiffe://sshcloud.internal/control/snapshot`. A role leaf proves the TLS role;
  it is not, by itself, workload identity—the GCE token is independently
  required.
- Authorization is deliberately narrow:

  | Listener/API | Exact caller | Token audience |
  |---|---|---|
  | Orchestrator `POST /v1/ensure`, `/v1/stop`, `/v1/no-idle` | gateway URI + exact gateway service account | `https://control.sshcloud.internal/orchestrator/gateway` |
  | Agent `/v1/*` | orchestrator URI + exact orchestrator service account | `https://control.sshcloud.internal/agent` |
  | Snapshotd `/v1/snapshots/*` | agent URI + exact agent service account and instance claims | `https://control.sshcloud.internal/snapshot` |
  | Gateway migration `/v1/sessions/{freeze,thaw,abort}` | orchestrator URI + exact orchestrator service account | `https://control.sshcloud.internal/gateway/migration` |
  | Orchestrator admin routes (hosts, drain, migrate, placement, diagnostics) | orchestrator URI + exact orchestrator service account, over the root-owned local Unix socket only | `https://control.sshcloud.internal/orchestrator/admin` |

  The gateway listener has no host/admin routes. The admin API has no TCP
  listener; operators reach the VM with IAP + OS Login and invoke the local
  root-only helper path. Separate unauthenticated HTTP listeners expose only
  `livez`/`readyz`/`healthz`, with no diagnostics.
- mTLS files reload on every new handshake. Two CA files are trusted
  concurrently so leaves can move between A/B signing slots before retiring
  the old CA. Fixed A/B trust positions plus explicit per-slot/per-role epochs
  make manual replacement deterministic without taint; superseded Secret
  Manager versions are retained for operator cleanup.
- Placement changes use Firestore transactions with revisioned leases,
  renewal heartbeats, expiry takeover, and a reconciler for abandoned leases.
- Rolling Firestore counters enforce join IP/prefix, deploy, and wake limits;
  gateway/orchestrator memory gates enforce handshakes, sessions, and awake VMs.
  Still open: storage-byte accounting.

### Infra

- **Host MIG** + host agent + Firecracker/jailer.  
- **Single gateway VM** in v1.  
- Terraform + **terraform-provider-ko** for platform Go services only.  
- One region.  
- Shared platform kernel artifact for all microVMs.  
- Guest egress is deny-all for the private trial; an audited global allowlist is later.

**Implemented in `sshcloud/terraform/` (first environment):**
- `ko_build` images: gateway, orchestrator, snapshotd, agent, guestinit, fortune (sample app)
- Separate named Firestore Native user and placement databases, CMEK snapshot + asset GCS buckets,
  Artifact Registry
- Secret Manager: gateway host key, user CA, two control CA slots, and
  role-specific control certificate/key bundles
- Versioned access policy from operator OpenSSH public-key lines; default
  allowlist/allowlist, with the opt-in demo key automatically admitted to both
  lists
- Gateway static IP (`:22` only when CIDRs are explicitly supplied),
  orchestrator VM (VPC), snapshotd VM/internal IP, nested-virt agent MIG
- Orchestrator `-hosts-file` refresh from MIG membership (`GET /v1/hosts`)
- Cloud NAT/Private Google Access for private hosts; content-addressed
  Firecracker/jailer/kernel GCS objects are in the Terraform DAG; agent-host SSH
  relays provide the separate-VM gateway→guest data path
- Gateway has a fixed internal migration-control address; orchestrator can
  freeze/thaw sessions while draining an agent. Agent templates remain
  opportunistic and operators call drain-before-replace; hard auto-healing
  remains an uncoordinated failure path.
- snapshotd is the only service account with snapshot object and envelope-KEK
  permissions. Agents reach only its TLS API through a tagged firewall edge;
  orchestrator reaches its separate health port. The snapshot bucket uses a
  Cloud KMS CMEK, while per-package streaming keysets are independently wrapped
  by the KEK.
- Still open: optional egress allowlist and key issuance outside Terraform
  state. The gateway host key, platform user CA, both control CAs, every role
  leaf, and optional demo key are Terraform-generated and remain in state;
  Secret Manager distribution plus a manual runbook is not external key
  management. OCI→rootfs on agents: `internal/ocirootfs` + Ensure
  `"image"` hook + `guestinit` PID 1 from image config; deploy cutover pre-boots
  the new gen with that image.
- GCP Ops Agent on every role, 30-day platform and seven-day app log buckets,
  `_Default` duplicate exclusion, Prometheus/OpenTelemetry-compatible host and
  lifecycle metrics, dashboard/core alerts, and optional email/budget. Real
  ingestion, routing, retention, and alert delivery still require a manual
  operator-owned GCP drill.
- CI unit/structural checks cover helper peer credentials, validation, fixed
  jailer argv, TAP rules, snapshot authorization fences, envelope
  tamper/swap/truncation/AAD, generation preconditions, and failure propagation.
  A disposable GCP project is
  still required to verify the Debian image's cgroup delegation, jailer
  mount/device syscalls, systemd lifecycle/capabilities, jailed snapshot
  migration, Cloud KMS/GCS/CMEK behavior, Firestore/IAM conditions, and direct
  agent-bucket denial. The systemd coupling and jailed Firecracker path remain
  unexercised on GCP nested KVM.

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

The implemented privacy boundary is documented in
[`sshcloud/docs/observability-runbook.md`](../sshcloud/docs/observability-runbook.md).
The bounded migration input queue is transport continuity, not recording, and
is explicitly excluded from every log/metric/event path. Production drains
guest serial-console output separately from Firecracker diagnostics through a
nonblocking bounded queue; guest JSON stays opaque. App telemetry has one
label-free counter/gauge line convention with hard rate, name, value, and
per-run cardinality limits. Aggregate platform metrics carry no
user/app/generation/run/session labels.

---

## 11. Networking & security

- Public ingress: SSH to gateway only.  
- MicroVMs private (tap/CNI); not Internet-reachable.  
- Egress: global allowlist.  
- No app-to-app net; no port forwarding.  
- Connection traces: metadata only (user, app, lifecycle phase, outcome, and
  timings) — never channel bytes, commands, environment, signals, or replay
  data.
- No account recovery in v1.  
- Gateway host key: single stable key (published fingerprint in docs); host CA later.  
- Abuse controls: §10.

---

## 12. MVP vertical slice

1. ~~Terraform + ko: Firestore, GCS, Secrets, host MIG, single gateway, orchestrator, agent.~~
   (`sshcloud/terraform/`; local pinned assets are uploaded before the MIG).
2. Platform user CA + inject path; shared kernel.  
3. Sample fortune OCI image (SSH server verifying CA) — `ko_build.fortune`.  
4. `ssh foo.com` (policy-admitted unknown key) → join → menu.
5. Deploy fortune → menu → fortune → wake (loading UI) → cert hop → session.  
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
   builds cached ext4 (`internal/rootfs.BuildFromDir`), and records Entrypoint /
   Cmd / Env / WorkingDir. Agent Ensure accepts `"image"` and resolves via
   `Config.RootfsResolver`, then boots `init=/platform-init` (`cmd/guestinit`)
   with `/platform-boot.json` from the image config (or an explicit base
   `.boot.json` / `-boot-spec`). No hardcoded fortune/platform default PID 1.
   Still open: first warm snapshot per digest. 
3. ~~**Idle timeout numbers**~~ — agent default **5 minutes** (`-idle`); refine
   when to count “zero sessions” vs last Ensure touch.  
4. **Freeze buffer cap** — max migrate hold before forced reconnect.  
5. ~~**Deploy drain-timeout default**~~ — gateway `-drain-timeout` default **5m**;
   per-deploy TUI override not in v1 (strategy only).  
6. ~~**Tier numbers**~~ — `tiny` = 1 vCPU / 128 MiB; `small` = 2 vCPU /
   512 MiB. Rootfs is currently 512 MiB for both; volume/disk tiers remain open.
7. **Global allowlist contents** — what destinations ship by default.  
8. ~~**Internal API auth**~~ — TLS 1.3 mTLS role URIs plus audience-bound,
   full-claim GCE service-account identity tokens are enforced on every
   production control route. Terraform initializes two CA slots and role
   leaves; deterministic manual epochs and a staged runbook now exist, but
   moving CA/leaf issuance and private keys out of Terraform remains open.
9. ~~**Repo layout**~~ — **`sshcloud/`** single Go module (`cmd/{gateway,orchestrator,agent}`, `internal/…`, `images/fortune`, `terraform/`).
10. **Threat model** — snapshot confidentiality/isolation now uses snapshotd,
    exact-instance operation fences revalidated at publish/delete CAS, Tink
    envelope encryption, KMS AAD, a bounded current+previous chain, and bucket
    CMEK. Tenant breakout, CA theft, storage-byte quota/accounting, and
    operational KMS rotation remain open. A future KEK/CMEK rotation affects
    new writes; old key versions must remain enabled until their packages and
    objects have expired. The operator runbook documents safe ordering, but no
    automatic schedule, envelope rewrap/object-rewrite path, or completed GCP
    drill is configured here.
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
# → app menu: deploy (empty until you deploy)

# Deploy the sample app (same path as any user app)
ssh deploy@foo.com
# → create fortune from <ko_build.fortune digest>

ssh foo.com
# Select fortune → wake
# Starting fortune…
# <session>

# Deep link skips menu
ssh fortune@foo.com

# Second concurrent connect while first still up — rejected
ssh fortune@foo.com
# → busy: already connected; disconnect the other session first

# Explicit menu if local username collides with an app
ssh menu@foo.com

# Key management
ssh join@foo.com

# Another custom app
ssh deploy@foo.com
# → create myapp from ghcr.io/me/myapp@sha256:…
ssh myapp@foo.com
```
