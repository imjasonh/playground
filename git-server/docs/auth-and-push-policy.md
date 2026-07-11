# Design: OAuth, IAM, and push-time policy

Status: **design only, not yet built.** This document proposes, in order:

1. **Authentication** — OAuth login, with the server minting short-lived
   **signed JWTs** (bearer tokens) under rotating keys, delivered to git via
   a credential helper.
2. **IAM** — permissions and roles; per-repo grants; tokens **scoped to
   branches or branch patterns**; a separate permission for managing the
   default branch.
3. **Push-time policy** — a declarative rule engine evaluated during
   receive-pack, able to reference IAM principals and permissions
   (including explicit policy override).
4. **Content checks** — budgeted blob scanning (secret patterns, lint
   rules) inside the policy engine.

Identity comes first: "who may bypass this rule" and "which branches may
this token touch" are meaningless without it.

Everything here is constrained by what the Worker actually is: wasm, CPU
metered (`cpu_ms = 300000` on the paid plan, see `wrangler.toml`), a hard
128 MiB isolate memory ceiling (enforced by `tests/memory.rs`), and **no
ability to run user-supplied code**. So policy is *data*, not hooks, and
auth is designed so the per-request cost is one signature verification —
no identity-store read on the hot path.

## Where the push pipeline offers facts

The receive-pack path (`src/protocol.rs::receive_pack` →
`src/repo.rs::apply_push`) already computes, in order:

| Stage | Facts available | Cost of a check here |
|---|---|---|
| Command parse | ref names, old/new oids, capabilities, push options | free; can reject **before any pack bytes are uploaded** |
| Pack scan (`PackScanner`) | per-entry type + inflated size (oid for non-delta entries); blob bytes are hashed and **discarded** | free; can abort the R2 upload mid-stream |
| `resolve_pack` | final oid / type / size for every object | free (already computed) |
| File-log build (`build_filelog_segment`) | per new commit: parsed headers (author, committer, message, parents) and **changed paths** with mode + blob oid, via `diff_trees` (cost ∝ changed paths) | free (already computed) |
| Explicit `Odb::read` | full blob content | **not** free — inflate ≈ 30 MiB/s on wasm, bytes count against the transient-heap budget |

The last row is why content checks (phase 4) get their own byte budgets;
everything above it is metadata the pipeline produces anyway. Note that
token **ref scoping** and IAM push checks need only the first row — they
reject before the pack uploads.

Rejections surface through the existing report-status path
(`src/protocol.rs::report_status`): `ng <ref> <reason>` per ref, with the
pipeline's existing invariant intact — refs, pack manifest, and file-log
flip atomically in the Durable Object or not at all. A rejection after
ingest leaves an orphan pack in R2, exactly like today's per-ref validation
failures; the maintenance sweep already collects those.

---

## Phase 1: OAuth + JWT bearer tokens

### Shape of the system

The Worker plays two OAuth roles:

* **Client / relying party** toward an upstream identity provider
  (GitHub first; the interface is provider-shaped, not GitHub-shaped, so
  another OIDC provider can slot in). We never store passwords and never
  build a login UI.
* **Authorization server** toward git: it exchanges a proven upstream
  identity for **our own JWTs**, which are what every subsequent request
  carries.

Splitting it this way keeps the hot path stateless: verifying a request is
one Ed25519 signature check in wasm (sub-millisecond, no I/O), not an
identity-store read.

### Login flow (device authorization grant)

Git is a CLI, so the natural flow is the device grant (RFC 8628),
server-mediated so the helper stays dumb and provider-agnostic:

```
helper                        worker                        provider
  |-- POST /auth/device -------->|                              |
  |                              |-- device code request ------>|
  |<- user_code, verify_uri, ----|<- device/user codes ---------|
  |   handle                     |                              |
  |   (user opens browser,       |                              |
  |    approves)                 |                              |
  |-- POST /auth/device/token -->|                              |
  |   {handle}   (poll)          |-- poll provider ------------>|
  |                              |<- provider access token -----|
  |                              |   verify identity, JIT-map   |
  |<- {access JWT, refresh tok} -|   to user record             |
```

On first successful login, the user record is **provisioned just-in-time**
in the auth store: login (from the provider handle, e.g. `github:alice` →
`alice`), verified emails (from the provider — used by the policy engine's
author-email checks), and default server role `user`.

### Tokens

Three kinds, all JWS compact JWTs signed EdDSA (Ed25519) except the
refresh token:

| Kind | Lifetime | Purpose |
|---|---|---|
| **access token** | short (default 1 h) | every git / API request; stateless verification |
| **refresh token** | rolling (default 30 d) | opaque random secret, stored **hashed** server-side → a revocable session; `POST /auth/token` exchanges it for a fresh access token (and rotates it) |
| **service token** | bounded (max 90 d) | minted via API for bots/CI; scoped tightly (below); revocable via jti denylist |

Access-token claims:

```jsonc
{
  "iss": "https://git.<account>.workers.dev",
  "aud": "git",
  "sub": "alice",
  "iat": 1760000000, "exp": 1760003600,
  "jti": "…",                       // for the denylist
  "roles": ["user"],                // server-wide roles only (see IAM)
  "scope": {                        // the token's CAP, not a grant
    "repos": ["*"],                 // repo-name globs
    "refs":  ["refs/heads/feature/*"],  // ref globs; ["*"] = unrestricted
    "permissions": ["repo.read", "repo.push", "refs.create"]
  }
}
```

`scope` is a **cap**: the effective authority of a request is
*live grants ∩ token scope* (see IAM below for where grants live). A token
can therefore only ever narrow what its owner may do — minting a scoped
token never escalates. Scoped minting (`POST /auth/token` with a requested
scope, or the `--scope` flags on the helper's login) is how "a token that
can only push to `refs/heads/deploy/*`" exists, per the requirement.

Why the cap/grant split matters for revocation: per-repo grants live on
`RepoState`, which **every request already loads** — so revoking someone's
access to a repo is effective immediately, no matter what tokens they
hold. Only server-wide roles ride inside the JWT and are as stale as the
token is old (bounded by the 1 h expiry).

### Keys and rotation

* Signing keys are Ed25519, generated inside the auth store DO, identified
  by `kid`. The store keeps **current** (signs new tokens) and **previous**
  (still verifies) keys.
* Rotation is scheduled on the existing cron trigger (`wrangler.toml`
  already runs nightly maintenance): promote a fresh key to current, demote
  current to previous, drop older. With a 1 h access-token lifetime, a
  two-key window is ample; refresh-token exchange re-signs under the
  current key naturally.
* Public keys are published at **`GET /.well-known/jwks.json`** — standard
  JWKS, so anything else (a future web UI, external services) can verify
  our tokens without a shared secret.
* Verification in the Worker caches the JWKS in-isolate; a `kid` miss
  refetches once. No secret material leaves the DO except public keys.

### Revocation, honestly

Stateless bearer tokens trade revocation latency for hot-path cost. The
design's stance:

* **Access tokens**: revoked by expiry (1 h). Per-repo de-permissioning is
  immediate anyway (grants are live, above).
* **Sessions** (refresh tokens): server-side hashed record → deleting it
  ends the session at next refresh, ≤1 h of residual access-token life.
* **Service tokens**: the emergency path is a **jti denylist** in the auth
  store, consulted **only on mutating requests** (push, `/api` writes) so
  reads stay lookup-free. Deny entries expire with the token's own `exp`,
  so the list stays small.

### The credential helper

A small client-side helper — `git-credential-git-server` — speaks git's
credential-helper protocol:

* On `get`: return a cached access token if fresh; else refresh via the
  session; else run the device flow (prints the code, opens the browser).
* With git ≥ 2.46, the helper returns `authtype=bearer` + `credential=<jwt>`
  and git sends a real `Authorization: Bearer` header. For older git, the
  server **also** accepts HTTP Basic with any username and the JWT as the
  password — same verification path, so the fallback costs nothing.
* Tokens cache in the OS credential store where available, else a
  `0600` file under `$XDG_STATE_HOME`.
* `login --scope repos=myrepo --scope refs=refs/heads/feature/*` mints a
  narrowed session for the paranoid or for per-project shells.

This intentionally relaxes the project's earlier "stock git only" stance
for *authenticated* use: anonymous reads of public repos still need
nothing, and Basic-with-JWT works helper-less (paste the token). The
helper is a client tool, not part of the Worker; it would live as its own
top-level app per repo conventions (likely Go, like `gitdb`/`ocidb`) —
exact home decided when built.

### Bootstrap

No secret to provision. A `SERVER_ADMINS` var in `wrangler.toml` lists
upstream identities (e.g. `"github:imjasonh"`); when one of them completes
the device flow, their JIT-provisioned record gets the server-wide `admin`
role. Everything else is granted from there via the API.

### New auth surface (added to `api.md` when built)

| Route | Auth | What |
|---|---|---|
| `POST /auth/device` | none | start device flow → user code + poll handle |
| `POST /auth/device/token` | none | poll → access JWT + refresh token |
| `POST /auth/token` | refresh or access token | refresh, or mint a **narrowed** access/service token (requested scope ∩ caller authority) |
| `DELETE /auth/sessions/<id>` | self or admin | end a session |
| `DELETE /auth/tokens/<jti>` | self or admin | denylist a service token |
| `GET /.well-known/jwks.json` | none | public verification keys |
| `GET /api/whoami` | token | resolved login, roles, effective scope |

Out of scope for phase 1: a web UI, SSH keys, non-device OAuth flows
(authorization-code + PKCE with a localhost redirect is a natural later
addition for browsers), and failed-auth rate limiting (open question).

---

## Phase 2: IAM — permissions, roles, grants

### Permissions

Atomic, dotted, resource-verb strings — the unit both grants and token
scopes speak:

| Permission | Allows |
|---|---|
| `repo.read` | fetch/clone; read `/api/<repo>/…` |
| `repo.push` | fast-forward updates to existing branches |
| `refs.create` | create branches/tags |
| `refs.delete` | delete branches/tags |
| `refs.forcePush` | non-fast-forward updates |
| `repo.setDefaultBranch` | change HEAD (see below) |
| `repo.maintenance` | `POST /api/<repo>/repack` |
| `repo.manageAccess` | edit visibility + grants |
| `repo.managePolicy` | edit the policy document |
| `policy.override` | eligible to bypass policy rules (phase 3) |
| `server.manageUsers` | create/disable users, grant server roles |

Splitting push into `repo.push` / `refs.create` / `refs.delete` /
`refs.forcePush` matches what receive-pack already distinguishes per
command (old=zero → create, new=zero → delete, non-ancestor → force), so
enforcement is a table lookup at command parse.

**`repo.setDefaultBranch` is deliberately its own permission.** Today HEAD
is implicit: `RepoState::empty()` defaults it to `refs/heads/main` and
`merge_push` silently re-points it when its branch disappears. Under IAM,
HEAD gets an explicit surface — **`PUT /api/<repo>/head`** — and only two
things may move it: that endpoint (requires `repo.setDefaultBranch`), and
the very first push to an empty repo (which establishes it). The
`merge_push` fallback survives purely as a safety net for
HEAD-branch-deleted, and deleting the HEAD branch itself requires
`repo.setDefaultBranch` *in addition to* `refs.delete` — so nobody
repoints the default branch by the back door.

### Roles

Named permission bundles. Built-in:

| Role | Permissions |
|---|---|
| `reader` | `repo.read` |
| `writer` | reader + `repo.push`, `refs.create` |
| `maintainer` | writer + `refs.delete`, `refs.forcePush`, `repo.setDefaultBranch`, `repo.maintenance`, `repo.manageAccess`, `repo.managePolicy`, `policy.override` |
| `admin` (server-wide only) | everything, every repo |

Grants can also name **individual permissions**, additive to a role — the
motivating cases both come from the requirements: a release bot holding
`writer` + `repo.setDefaultBranch` (can flip HEAD, can't edit policy), or
a `reader` + `policy.override` auditor. Custom named roles are an open
question; individual-permission grants cover the known cases without a
role-editor surface.

### Where grants live, and how a request is decided

* **Per-repo grants** live on `RepoState` (the per-repo DO document,
  already loaded by every request): `visibility: "public" | "private"`,
  plus `grants: { login → { role, permissions: [...] } }`. Well under the
  128 KiB DO value cap. Edited via `GET/PUT /api/<repo>/access`
  (`repo.manageAccess`).
* **Server-wide roles** live on the user record and are embedded in the
  JWT's `roles` claim (stale ≤ token lifetime).
* The **first authenticated push** to an empty repo grants the pusher
  `maintainer` on it (repo claiming).

Every request is decided by one pure function, in a transport-agnostic
module so it's natively testable:

```
effective(request) =
    permissions(server roles from JWT)
  ∪ permissions(repo grant for sub)
  ∩ token.scope.permissions
  ∩ (repo matches token.scope.repos)
allowed = required_permission ∈ effective
        ∧ (if the action targets a ref: ref matches token.scope.refs)
```

Anonymous requests get `repo.read` on public repos and nothing else.
**Push always requires auth** once this ships; an `ALLOW_ANONYMOUS_PUSH`
var exists only as a rollback lever and defaults off. Existing repos
default to `public` + no grants, so nothing currently readable goes dark
at the flag day.

### Branch-scoped tokens at enforcement time

`token.scope.refs` is checked at **command parse** in `receive_pack`: every
`RefUpdate.name` must match a scope glob, or that ref's command is
rejected (`ng <ref> token scope does not include this ref`) **before
`PackIngest::start`** — no R2 write, no scan. The same check guards
`PUT /api/<repo>/head` (the target ref must be in scope).

Ref scoping is a **write** control only. Branch-level *read* restriction
is deliberately not offered: a git object graph is shared across refs
(a fetch negotiates wants by oid, packs deltify across branches), so
per-ref read filtering leaks through object reachability and would be
false security. Read scoping stays repo-granular (`scope.repos`).

---

## Phase 3: the policy engine

### Rule shape

A per-repo **policy document**: an ordered list of named rules, each
`scope × check × action`. Stored as a `policy` field on `RepoState`
(versioned and CAS-swapped with the rest of the state doc), edited via
`PUT /api/<repo>/policy` (requires `repo.managePolicy`), retrieved via
`GET /api/<repo>/policy`. TOML on the wire for humans, canonical JSON in
the DO.

```toml
[[rule]]
name = "protect-main"                # names are API: they appear in ng lines
refs  = ["refs/heads/main"]          # glob scope; default: all refs
deny  = ["delete", "force"]          # tier-0 verbs: create | delete | force

[[rule]]
name  = "workflows-frozen"
paths = [".github/workflows/**"]     # glob on changed paths (tree diff)
deny  = ["add", "modify", "delete"]
bypass = ["user:alice"]              # narrows who may override (see below)

[[rule]]
name = "no-big-blobs"
max_blob_bytes = "5MB"
overridable = false                  # nobody bypasses this one

[[rule]]
name = "ticket-ref"
refs = ["refs/heads/main"]
commit_message_pattern = 'Resolves [A-Z]+-\d+'

[[rule]]
name = "you-are-you"
require_author_email_matches_pusher = true   # author email ∈ pusher's
                                             # provider-verified emails

[[rule]]
name = "no-secrets"
paths = ["**"]
action = "reject"                    # "reject" (default) | "warn"
[rule.content]
deny_patterns = ["aws-key", "pem-private-key", "github-token"]
max_blob_bytes = "1MB"               # skip larger blobs (see budget action)
on_budget_exceeded = "reject"        # fail closed for secrets
```

### Check catalog by tier

| Tier | Checks | Facts source |
|---|---|---|
| 0 — ref | protected refs (`deny = create/delete/force`), ref-name patterns, max refs per push | parsed commands; **rejects before the pack uploads** |
| 1 — pack shape | `max_blob_bytes` (fast-fail during scan for non-delta entries; authoritative after resolve), max objects per push | `PackScanner` / `resolve_pack` |
| 2 — path | frozen paths, deny path globs (`node_modules/**`, `*.env`), case-collision, path charset/length, mode rules (no symlinks / no gitlinks / executable-bit scoping), per-path-glob size caps | `diff_trees` output (already built for the file-log) |
| 3 — commit | author/committer email patterns, `require_author_email_matches_pusher`, message pattern, merge policy (parent count), signature *presence*, timestamp sanity | commits already parsed for the file-log |
| 4 — content | secret patterns, lint checks | `Odb::read`, budgeted — phase 4 below |

Note the overlap by design between tier-0 policy and IAM: `refs.forcePush`
is *authority* ("may this principal ever force-push here"), while
`deny = ["force"]` is *policy* ("nobody force-pushes main without an
explicit override"). IAM is evaluated first; policy applies to the
already-authorized.

"Force" means: `old` is a non-ancestor of `new`. The pipeline's CAS
already rejects *stale* olds; the force check additionally needs an
ancestry walk between two commits in the (old ∪ new) odb, bounded like the
existing connectivity check. IAM's `refs.forcePush` gate uses the same
walk — one implementation.

### Override: permissioned and explicit

Bypass eligibility is the **`policy.override` permission** (within the
token's scope cap, like everything else). A rule can narrow eligibility
further with `bypass = ["user:…", "role:…"]`, or forbid override entirely
with `overridable = false`.

Eligibility alone never bypasses anything — the pusher must say so:

```
git push -o policy.override=workflows-frozen
```

The server advertises the `push-options` capability; options arrive in the
command section, before any pack bytes. An override without eligibility is
rejected (`ng <ref> policy "workflows-frozen": override not permitted`);
eligibility without the option still enforces the rule. Maintainers stay
subject to policy by default, every exception is a deliberate act, and
each override emits a structured audit log line (sub, jti, rule, refs).

### Semantics

* Rules evaluate **per ref command**, against the facts of the commits that
  command introduces. All rules run; all violations are reported (no
  first-failure short-circuit), each as part of the ref's `ng` reason.
* `action = "warn"` reports the violation on the side-band PROGRESS channel
  (the push path already emits those) and lets the push land — the rollout
  mode for new rules.
* Error text is API:
  `ng <ref> policy "<rule-name>": <detail>` — e.g.
  `ng refs/heads/main policy "workflows-frozen": .github/workflows/ci.yml`.
* One glob implementation (gitignore-style `**`) shared by policy `refs` /
  `paths`, token `scope.refs` / `scope.repos` — a single home per
  `AGENTS.md`.
* Custom regexes (`commit_message_pattern`, custom content patterns) are
  compiled with the linear-time `regex` engine — no backtracking, so no
  ReDoS — with caps on pattern count and compiled size, validated at
  `PUT /api/<repo>/policy` time so a bad policy fails at write, not at
  someone else's push.

### Enforcement points

Right after command parse in `receive_pack`, in order: token ref-scope
check, IAM per-command check, tier-0 policy — all **before
`PackIngest::start`**, so none of them costs an R2 write. Tier 1's
fast-fail lives in the scan feed loop and aborts the multipart upload.
Tiers 2–4 evaluate inside `apply_push`, after `resolve_pack` and the
file-log build produced their facts, **before** `StateStore::apply_push` —
the same slot as today's connectivity check, with the same orphan-pack
consequence on rejection (already handled by the maintenance sweep).

All of it lives in transport-agnostic modules (new `src/auth.rs`,
`src/iam.rs`, `src/policy.rs`), so `cargo test` exercises the same code
the Worker runs, and every rejection branch gets an integration test per
the crate's error-path rule.

---

## Phase 4: content checks (tier 4)

The only tier that must *read blob bytes*, so the only tier with a real
CPU/memory budget question.

### What gets scanned

After `resolve_pack` and the file-log build, the push knows every
`(path, Add|Modify, blob oid)` the new commits introduce, and the pack
index knows each blob's size. The scanner:

1. Collects records matching any content rule's `paths` globs; dedupes by
   blob oid (the same blob at two paths scans once).
2. Skips blobs larger than the rule's `max_blob_bytes` (default 1 MiB) —
   applying the rule's `on_budget_exceeded` action to the skip.
3. Reads survivors **one at a time** via `Odb::read` into a reused buffer,
   until the per-push scan budget (default 32 MiB) is spent; past it,
   remaining blobs get the `on_budget_exceeded` action too.

Only blobs introduced by *this push* are scanned — unchanged files are
never rescanned, so steady-state cost tracks the size of the change, not
the repo.

Budget arithmetic: `Odb::read` inflates at ~30 MiB/s on wasm, so the
default 32 MiB budget is ≈1 s of CPU plus a single linear regex pass —
noise under `cpu_ms = 300000`. Memory: one buffer, capped at the largest
`max_blob_bytes` in the policy, counted against the transient-heap budget;
`tests/memory.rs` grows a content-scanning variant so the 64 MiB
`TRANSIENT_BUDGET` keeps enforcing this.

### Check types

**Secret patterns** — the headline rule. Curated, named pattern packs
maintained in the crate (`aws-key`, `pem-private-key`, `github-token`,
`slack-token`, …), so most policies never write a regex; custom
`regex = '…'` entries are allowed under the same linear-time-engine caps as
phase 3. Findings are reported as rule + path + line number — **never** the
matched text; the report-status channel must not echo secrets back. Our own
JWTs are a pattern-pack entry too.

**Lint checks** — declarative built-ins, each a flag or small param:

| Check | Meaning |
|---|---|
| `deny_conflict_markers` | `<<<<<<<` / `=======` / `>>>>>>>` at line start |
| `max_line_length = n` | any line longer than *n* bytes |
| `deny_trailing_whitespace` | space/tab before newline |
| `require_final_newline` | last byte is `\n` |
| `require_lf` | no CRLF line endings |
| `require_utf8` | blob is valid UTF-8 |
| `deny_binary` | NUL byte in the first 8 KiB |
| `required_prefix = "…"` | file starts with the given text (license headers) |
| `require_json` | blob parses as JSON (scoped via `paths = ["**/*.json"]`) |

Several of these (`deny_binary`, `required_prefix`) need only a bounded
prefix read, and the scanner exploits that.

**Deliberately out of scope: real linters.** eslint, clippy, gofmt — these
are arbitrary code execution, which the wasm/CPU model (and the declarative
premise) rules out. If a repo ever needs them at push time, the answer is
an *asynchronous external check* (server calls a webhook, a later API
reports status) — a different feature with different consistency semantics,
intentionally not designed here.

### Fail open or fail closed

Per rule, `on_budget_exceeded = "warn" | "reject"` decides what happens to
blobs the scanner *couldn't* check (too large, or budget exhausted).
Defaults: `warn` for lint rules (style checks shouldn't brick a big
refactor), `reject` for secret rules (an unscanned blob is an unvetted
blob). Both defaults are overridable, and the warn path names the skipped
blobs so the gap is visible.

---

## Phasing and test plan

| Phase | Lands | Proves |
|---|---|---|
| 1 | auth store DO (users, sessions, keys), device flow, JWT mint/verify, JWKS + rotation, Bearer + Basic-fallback parsing, credential helper | full login → push round-trip in integration tests (native JWT mint against a test key; `TestServer` with `Authorization` headers); expiry; refresh rotation; session revocation; kid rollover |
| 2 | permission/role model, grants on `RepoState`, `/api/<repo>/access`, `PUT /api/<repo>/head`, token scope caps + ref-scope enforcement, claim-on-first-push, 401/403 flow | every permission's allow and deny; scoped-token narrowing (never widening); ref-scope rejection before ingest; default-branch permission split |
| 3 | `src/policy.rs`, policy storage + API, tiers 0–3, permissioned override, warn channel | every rule type's reject *and* warn branch; override eligibility × option matrix; policy-validation-at-write |
| 4 | content scanner, pattern packs, lint checks, budgets | secret hit / lint hit / budget-exceeded paths; memory-test variant under `TRANSIENT_BUDGET` |

Each phase updates `docs/api.md` in the same change (hard rule), and each
new rejection path ships with the test that triggers it. The credential
helper is client-side and gets its own home and test suite per repo
conventions.

## Open questions

* **Second identity provider.** GitHub device flow first; the exchange
  endpoint is shaped for any OIDC provider, but generic-OIDC config
  (issuer discovery, client registration) is unspecified until a second
  provider is real.
* **Custom roles.** Individual-permission grants cover the known cases;
  a role editor is deferred until repeated grants make one earn its keep.
* **Service-token ceiling.** 90 d max proposed; too long for taste, but
  shorter forces bot-credential rotation machinery that doesn't exist yet.
  The jti denylist is the compensating control.
* **Failed-auth rate limiting.** Signature verification is cheap enough
  that probing costs us little; device-flow and refresh endpoints are the
  ones to watch. A KV counter keyed by IP with a short TTL if logs show
  abuse.
* **Retro-scanning.** A policy added after a secret already landed doesn't
  scan history. A `POST /api/<repo>/scan` walking existing blobs under the
  same budget machinery (repeated calls to converge, like `/repack`) is
  the likely shape — not in scope for phase 4.
* **Web flow.** Authorization-code + PKCE (localhost redirect) as a
  second grant type once anything browser-shaped exists; the token
  machinery is unchanged by it.
