# Design: OAuth, IAM, and push-time policy

Status: **design only, not yet built.** This document proposes, in order:

1. **Authentication** — OAuth login for **users** and OIDC federation for
   **service accounts**, with the server minting short-lived **signed
   JWTs** (bearer tokens) under rotating keys, delivered to git via a
   credential helper.
2. **IAM** — permissions and roles; per-repo grants; tokens **scoped to
   branches or branch patterns**; a separate permission for managing the
   default branch.
3. **Push-time policy** — a declarative rule engine evaluated during
   receive-pack, able to reference IAM permissions. One **approval
   mechanism** serves two rule interactions: overriding a rule requires
   **two-party approval**, and rules can require **review approval for
   merges into protected branches**. Both write **signed audit records
   into the repo itself**, in a form that stays cheap to store and O(1)
   to query. Service accounts can never approve. For monorepos, policy
   layers: an API-managed **root policy** applies to the whole repo and
   delegates path-confined, monotonically-tightening **subtree policies**
   to directory owners.
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

### Two principal kinds: users and service accounts

* A **user** is a human, tied to an upstream OAuth account, who logs in
  interactively (device flow above) and holds a refresh-token session.
* A **service account** is a registered non-human principal
  (`sa:deploy-bot`) that is never logged into — it is **assumed** via OIDC
  federation: a workload (CI job, cron, another service) presents an ID
  token from a **trusted OIDC issuer**, and the server exchanges it for a
  short-lived access JWT for the service account.

A service account record (created by an admin) names what may assume it:

```jsonc
{ "name": "sa:deploy-bot",
  "assume": [ { "issuer": "https://token.actions.githubusercontent.com",
                "subject": "repo:imjasonh/playground:ref:refs/heads/main",
                "audience": "https://git.<account>.workers.dev" } ] }
```

The exchange (`POST /auth/token`, `grant_type=…:token-exchange`) verifies
the presented ID token against the issuer's published JWKS, matches
issuer/subject/audience to a service account's `assume` rules, and mints
an ordinary access JWT — same 1 h lifetime, same scope-cap machinery, but
`"kind": "service"`. There are **no long-lived bot credentials to store,
leak, or rotate**: the workload's ambient OIDC identity is the credential,
and every assumed token dies within the hour. Service accounts get no
refresh tokens and no sessions.

The `kind` claim is load-bearing downstream: **service accounts can never
act as approvers** — not for policy overrides, not for merge review
(phase 3). The approver endpoints reject `kind: "service"` tokens
outright. Bots push, deploy, and mirror; humans vouch.

### Tokens

All JWS compact JWTs signed EdDSA (Ed25519) except the refresh token:

| Kind | Lifetime | Purpose |
|---|---|---|
| **access token** | short (default 1 h) | every git / API request; stateless verification; `kind` claim says user vs service |
| **refresh token** | rolling (default 30 d) | users only; opaque random secret, stored **hashed** server-side → a revocable session; `POST /auth/token` exchanges it for a fresh access token (and rotates it) |

Access-token claims:

```jsonc
{
  "iss": "https://git.<account>.workers.dev",
  "aud": "git",
  "sub": "alice",                   // or "sa:deploy-bot"
  "kind": "user",                   // "user" | "service"
  "iat": 1760000000, "exp": 1760003600,
  "jti": "…",                       // for the denylist
  "roles": ["user"],                // server-wide roles only (see IAM)
  "scope": {                        // the token's CAP, not a grant
    "repos": ["*"],                 // repo-name globs
    "refs":  ["refs/heads/feature/*"],  // ref globs; ["*"] = unrestricted
    "paths": ["services/payments/**"],  // write-path globs (monorepos)
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
  current to previous. With a 1 h access-token lifetime, a two-key window
  is ample for *accepting* tokens; refresh-token exchange re-signs under
  the current key naturally.
* Public keys are published at **`GET /.well-known/jwks.json`** — standard
  JWKS, so anything else (a future web UI, external services) can verify
  our tokens without a shared secret.
* Rotated-out keys are **retained for verification indefinitely** (public
  keys are tiny) and stay in the JWKS marked verify-only. This matters for
  the audit trail (phase 3): override records embedded in repo history
  carry JWS signatures that must remain checkable years after the signing
  key stopped signing.
* Verification in the Worker caches the JWKS in-isolate; a `kid` miss
  refetches once. No secret material leaves the DO except public keys.

### Revocation, honestly

Stateless bearer tokens trade revocation latency for hot-path cost. The
design's stance:

* **Access tokens**: revoked by expiry (1 h). Per-repo de-permissioning is
  immediate anyway (grants are live, above).
* **Sessions** (refresh tokens): server-side hashed record → deleting it
  ends the session at next refresh, ≤1 h of residual access-token life.
* **Service accounts**: disabling the account or editing its `assume`
  rules stops the *next* exchange; outstanding assumed tokens die within
  the hour. No stored bot credential exists to leak, so there is nothing
  long-lived to revoke.
* **Emergency**: a **jti denylist** in the auth store, consulted **only on
  mutating requests** (push, `/api` writes) so reads stay lookup-free.
  Deny entries expire with the token's own `exp`, so the list stays small.

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
| `POST /auth/token` | refresh token, access token, or upstream OIDC ID token | refresh; mint a **narrowed** access token (requested scope ∩ caller authority); or the token-exchange grant that assumes a service account |
| `PUT /api/service-accounts/<name>` | admin | create/update a service account and its `assume` rules |
| `DELETE /auth/sessions/<id>` | self or admin | end a session |
| `DELETE /auth/tokens/<jti>` | self or admin | denylist a token (emergency) |
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
| `policy.approve` | may create review approvals (phase 3) |
| `policy.override` | may satisfy the permission half of a two-party policy override (phase 3) |
| `server.manageUsers` | create/disable users and service accounts, grant server roles |

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
| `writer` | reader + `repo.push`, `refs.create`, `policy.approve` |
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
  plus `grants: { principal → { role, permissions: [...], paths: [...] } }`,
  where a principal is a user login or a service account (`sa:deploy-bot`)
  — grants are kind-blind; only approval acts (phase 3) discriminate. The
  optional `paths` globs confine a grant's *write* authority (and its
  `policy.approve` coverage) to a subtree — the monorepo ownership story,
  detailed in phase 3's monorepo section. Well under the 128 KiB DO value
  cap. Edited via `GET/PUT /api/<repo>/access` (`repo.manageAccess`).
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
        ∧ (if the action writes tree content and the grant or token scope
           is path-confined: every changed path matches — evaluated at the
           apply stage from the same tree diff tier-2 policy uses)
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

One namespace is reserved: **`refs/audit/**` is never client-writable** —
no token scope may include it and no grant permits pushing to it. The
server itself appends there (phase 3's audit trail); clients can only
fetch it.

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
name = "main-requires-review"
refs  = ["refs/heads/main"]
require_review = { approvals = 1 }   # merges into main need a prior
                                     # review approval (see Approvals)

[[rule]]
name  = "workflows-frozen"
paths = [".github/workflows/**"]     # glob on changed paths (tree diff)
deny  = ["add", "modify", "delete"]  # overridable (the default) — but only
                                     # via two-party approval (see below)

[[rule]]
name = "policy-files-guarded"
paths = ["**/.policy.toml"]          # subtree policies (see Monorepos) change
deny  = ["add", "modify", "delete"]  # only via two-party override

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
| 3 — commit | author/committer email patterns, `require_author_email_matches_pusher`, message pattern, merge policy (parent count), signature *presence*, timestamp sanity, `require_review` (needs the parsed tip commit's parents + an ancestry check) | commits already parsed for the file-log |
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

### Approvals: one mechanism, two uses

An **approval** is a signed statement by a *user* — "I, bob, approve X
against ref Y, valid until T" — minted by the server, held pending on the
repo, consumed by a push, and archived in the repo's audit space. Two rule
interactions use it:

* **Override approvals** — waiving a rule a push would otherwise violate
  (exceptional, two-party, permissioned).
* **Review approvals** — satisfying a `require_review` rule on a protected
  branch (routine: "merges into main must be approved").

**Service accounts can never approve.** The approval endpoint rejects
`kind: "service"` tokens outright, for both uses. A CI bot can push,
deploy, and mirror; it cannot vouch. This is what makes "two parties"
mean two *humans* — a person plus their own bot is not a quorum — and
it's a hard rule, not policy: no rule setting re-enables bot approvers.

#### Creating an approval

```
POST /api/<repo>/approvals
{ "use": "review",                // "review" | "override"
  "ref": "refs/heads/main",
  "new": "<oid>",                 // review: required. override: optional
  "rule": "workflows-frozen",     // override only: the rule being waived
  "reason": "LGTM — reviewed the diff",
  "ttl_s": 86400 }                // review default 7 d; override default 1 h
```

Requirements at mint time: an authenticated **user** (never a service
account); for `review`, the `policy.approve` permission on the repo (the
`writer` role has it — peers review peers); for `override`, any
authenticated user with `repo.read` — the permission gate for overrides
is on *using* the approval (the two-party check below), not on stating
one. The server records whether the approver holds `policy.override`, so
the push-time check needs no second identity lookup.

The server mints an **approval JWS** — a compact JWT under the rotating
keys whose claims are the approval itself:

```jsonc
{ "iss": "…", "aud": "git-approval",
  "sub": "bob", "kind": "user",    // the approver; never a service account
  "iat": 1760000000, "exp": 1760086400, "jti": "ap-…",
  "repo": "myrepo", "use": "review",
  "ref": "refs/heads/main", "new": "<oid>",
  "rule": null,                    // set for overrides
  "reason": "LGTM — reviewed the diff",
  "approver_has_override": false }
```

The JWS is returned to the approver *and* a pending-approval stub (jti,
use, rule, ref, oid, expiry, the JWS itself) is stored on `RepoState`.
Storing the stub buys three things a pure hand-the-JWT-to-the-pusher
design can't:

* **Single use.** The approval is consumed in the same DO CAS that
  applies the push — it cannot authorize two pushes, and a concurrent
  race gets exactly one winner.
* **Pusher UX.** No token pasting. Review approvals are matched
  automatically when the rule evaluates; overrides need only the explicit
  `-o policy.override=<rule>` push option.
* **Revocability.** `DELETE /api/<repo>/approvals/<jti>` (the approver or
  anyone with `repo.managePolicy`) withdraws an approval before use.

The pending set is **bounded**: expired stubs are pruned on every write,
and a cap (`MAX_PENDING_APPROVALS`, order of 64) rejects new approvals
when full — approvals are ephemeral work-in-flight, not storage, so the
128 KiB DO document never becomes the bottleneck. The durable record
lives in the audit space, below.

#### Override: two parties, one permission

Overriding a rule is deliberately heavier than satisfying it:

1. **Two parties.** The pusher and a prior approver, with
   `approver.sub ≠ pusher.sub` — and both necessarily human, per above.
2. **One permission between them.** At least one of the two must hold
   `policy.override` on the repo. (Both parties are approving the
   override — the pusher approves by pushing.) A junior engineer can push
   an approved exception their lead signed off on, and equally a lead can
   push with a junior's ack; two unprivileged users cannot waive policy
   between themselves.
3. **The override must be explicit** — `git push -o policy.override=<rule>`;
   eligibility without the option still enforces the rule.

At push time the server checks: matching unconsumed approval (rule + ref
+ oid-if-bound + unexpired), distinct parties, and
`pusher_has_override ∨ approver_has_override`. Any miss is a normal
rejection with the established vocabulary:
`ng <ref> policy "workflows-frozen": override requires approval`,
`… approval expired`, `… approver and pusher must differ`,
`… override not permitted`.

**Who may override is *not* configured per rule.** An earlier draft had
per-rule `bypass = ["user:…"]` lists; they're gone deliberately. User
lists inside policy documents rot (people join, leave, change teams) and
create a second authorization system competing with IAM. Authorization
membership lives in exactly one place — IAM grants of `policy.override` —
and the policy document only says whether a rule is overridable *at all*
(`overridable = false` for the never-bypass rules like secret scanning).
If different rules ever genuinely need different approver *sets*, the
right mechanism is IAM groups as grantees, not names inside rules — an
open question below, deferred until a real case shows up.

#### Required review for protected branches

```toml
[[rule]]
name = "main-requires-review"
refs  = ["refs/heads/main"]
require_review = { approvals = 1 }
```

This server has no pull-request object — a "PR" here is a branch plus a
review approval bound to a commit. The workflow:

1. Alice pushes `refs/heads/feature/x` (no rule applies there).
2. Bob fetches, reviews, and approves the tip:
   `POST /api/<repo>/approvals {use: "review", ref: "refs/heads/main",
   new: "<feature tip oid>"}`.
3. Alice pushes to `main`. No push option needed — the rule finds the
   matching approval automatically.

A push `old → new` on the protected ref satisfies a review approval bound
to commit `A` when:

* `new == A` (a fast-forward to exactly the approved commit), **or**
* `new` is a merge commit whose parents include both `old` (first parent
  — history stays first-parent linear on the protected branch) and `A`
  (the approved work).

The second arm is what lets approval precede the merge commit: the merge
oid doesn't exist when the reviewer approves, so the approval binds to
the branch tip being merged, and the ancestry check (same bounded walk as
the force check) ties them together. Known and accepted gap, same as
GitHub's: conflict-resolution content *inside* the merge commit itself
isn't separately re-reviewed. Approving the merge commit's own oid
(re-approval after creating it locally) closes the gap when it matters.

`approvals = N` requires N matching approvals from N **distinct**
approvers, each distinct from the pusher. The pusher's own approval never
counts (`approver ≠ pusher` applies per approval). Like any rule,
`require_review` is overridable through the two-party override above —
the incident escape hatch, itself audited — unless the rule sets
`overridable = false`, in which case unreviewed code cannot reach the
branch at all.

Review approvals evaluate at the apply stage (the tip commit's parents
are already parsed for the file-log; the ancestry walk is the shared
force-check implementation).

#### The audit space: one ref, records keyed by commit

Every consumed approval — override or review — lands in the repo itself,
under the reserved **`refs/audit`** ref. The design goal is threefold, per
the requirements: **verifiable** (signed claims), **bounded** (growth
can't degrade the repo), and **queryable** ("why/when was this merge
approved" in one lookup, no history walk).

The tip of `refs/audit` is a tree keyed by *what was admitted*, fanned out
like a pack index:

```
reviews/refs/heads/main/ab/abcdef…40hex.json
overrides/refs/heads/main/12/123456…40hex.json
```

— one JSON blob per admitted push event, at a path derived from the
target ref and the **new tip oid** it admitted. Each blob is a
**server-signed JWS** (`aud: "git-audit"`) over the full record:

```jsonc
{ "kind": "review", "v": 1,
  "rule": "main-requires-review",
  "ref": "refs/heads/main", "old": "<oid>", "new": "<oid>",
  "pusher": { "sub": "alice", "kind": "user", "jti": "…", "iat": 1760001000 },
  "approvals": [ "<approval JWS, verbatim>", … ],
  "pushed_at": "2026-07-11T18:04:05.123Z" }
```

Two signature layers, verifiable offline against
`/.well-known/jwks.json` years later (phase 1 retains rotated-out public
keys verify-only for exactly this): the embedded approval JWSes are the
approvers' claims — who approved what, when, holding which permission —
and the outer JWS is the server's attestation of what was actually pushed
under them.

**Answering the queries.** "Why/when was this merge approved?" is a
single tree lookup at the audit tip — `GET
/api/<repo>/file/refs/audit/reviews/refs/heads/main/ab/<oid>.json` — no
history walk, cost independent of how many approvals the repo has ever
recorded. Directory listings (`/api/<repo>/tree/…`) browse recent records
per ref, and the push-time file-log gives each record's own
`last_commit_time` attribution for free. `git log refs/audit` works too,
for humans who prefer git. No new read API is needed; if ergonomics
demand it later, a convenience route can wrap the same lookup.

**Bounding growth.** Records are ~1–2 KiB (two compact JWSes plus
metadata); ten thousand approvals is ~15 MiB of R2 — real but unalarming,
and it lives in ordinary packs that repack consolidates like everything
else. The structures that must *not* grow are protected by construction:

* **The DO state doc** gains exactly one refs entry (`refs/audit`) and
  the bounded pending-approval stubs — audit volume never touches it.
* **The audit commit chain** is redundant with its own tip tree (every
  record is self-describing and individually signed; ordering and
  timestamps live inside the records). Nightly maintenance therefore
  **flattens** `refs/audit` history — when the chain exceeds a threshold,
  it's rewritten to a single commit carrying the same tree — so the chain
  never becomes an unbounded walk for anything.
* **Normal git traffic never pays.** `refs/audit` is outside
  `refs/heads/*` and `refs/tags/*`, so default clones and fetches don't
  download it; only `--mirror` or an explicit refspec does.
* **Appending stays O(changed path)**: the per-push audit update is one
  blob + the trees along its fanout path, built by the existing
  `PackWriter`, riding in the same `PushDelta` as the user's refs —
  atomic via the existing DO CAS, no new consistency story.

The flattening trade-off, stated plainly: rewriting audit history means
the git chain itself is not tamper-evidence — but it never really was,
since the server writes it and the server is the enforcement point. The
integrity guarantees live in the signatures on each record. If
independent tamper-evidence is ever wanted, each record can chain a hash
of its predecessor inside the signed payload (open question below).

Rejected pushes and rejected approval attempts don't touch the repo —
they get the `ng` line and a structured log entry, same as any other
rejection.

What this is **not**: a client-side signature by the pusher or approver.
Git does have one (`git push --signed`, the `push-cert` capability), and
supporting it would strengthen records from "the server attests alice's
token did this" to "alice's own key signed this" — but it drags in client
key management for marginal gain over authenticated bearer requests.
Noted as a possible later hardening, not designed here.

### Monorepos: root policy plus delegated subtree policies

The engine is monorepo-friendly on *cost* by construction — every
evaluation scales with the change, not the repo: path rules ride
`diff_trees` (∝ changed paths), content rules scan only blobs the push
introduces, audit lookups are O(1) by commit. What a monorepo adds is
*organizational*: directories owned by different teams, each wanting its
own rules and reviewers, without every change funneling through whoever
holds `repo.managePolicy`. Three additions cover it.

#### Path-scoped IAM (ownership)

Grants and token scopes optionally carry `paths` globs (shapes shown in
phases 1–2):

```jsonc
"grants": {
  "sa:payments-ci": { "role": "writer", "paths": ["services/payments/**"] },
  "carol":          { "role": "writer", "paths": ["services/payments/**"] }
}
```

A path-confined writer's push may only touch matching paths — checked at
the apply stage against the same `diff_trees` output tier-2 rules use;
anything else is `ng <ref> grant does not cover path <path>`. Token
`scope.paths` is the same check as a cap (mint the payments-CI token so
it *couldn't* touch `services/billing/**` even if the account could).
Like ref scoping, path scoping is **write-only** — read stays
repo-granular, by the same shared-object-graph argument. Path-confined
`policy.approve` is what makes review path-aware, below.

#### Delegated subtree policies

Two policy layers:

* The **root policy** — the API-managed document on `RepoState`, exactly
  as designed above. It applies to the whole repo unconditionally, and it
  is the only layer that can declare **delegations**:

```toml
[[delegate]]
path  = "services/payments"
allow = ["paths", "commit", "content", "review"]  # rule kinds the subtree may add
```

* A **subtree policy** — an ordinary committed file,
  `services/payments/.policy.toml`, owned and evolved by the team that
  owns the directory, subject to two invariants enforced when the server
  loads it:

  * **Confinement.** Every subtree rule's path scope is intersected with
    the delegated subtree. A subtree policy cannot observe, much less
    constrain, anything outside its directory, and may only use the rule
    kinds its delegation allows.
  * **Monotonicity.** Subtree rules only *add* checks. They cannot mark a
    root rule overridable, relax a budget, waive a review requirement, or
    grant anything. Where both layers speak, the stricter wins. (This is
    what makes in-repo policy safe at all — the root layer's guarantees
    are unconditional, so the worst a subtree file can do is over-tighten
    its own directory.)

Evaluation stays cheap because delegations are **explicitly enumerated**
in the root policy: after `diff_trees`, the server knows which delegated
roots the push touched, reads exactly those `.policy.toml` blobs
(size-capped, through the same budgeted read path as content rules — a
push touching no delegated subtree reads none), and evaluates their rules
alongside the root's. No repo-wide policy discovery walk, ever.

**Which version of a policy file governs?** The one in the **old tree of
the ref being pushed** — the policy in force when the push arrives. A
push that edits `.policy.toml` is judged under the *previous* rules (a
push can never weaken the rules that judge it) and its changes take
effect from the next push. Branch creations (old = zero) are judged under
the root policy alone. And `.policy.toml` files are themselves just
files: the root policy sample above freezes `**/.policy.toml` behind the
two-party override, so subtree-policy evolution is itself audited; a
`require_review` + path-aware setup works too.

#### Path-aware review (owners)

```toml
[[rule]]
name  = "owners-review"
refs  = ["refs/heads/main"]
require_review = { approvals = 1, per_path = true }
```

With `per_path = true`, every path the push changes must be covered by at
least one matching approval whose approver's `policy.approve` grant
covers that path (a path-unconfined approve grant covers everything).
This is the CODEOWNERS idea with the membership kept in IAM grants
instead of a usernames file in the repo — the same no-user-lists-in-policy
principle as overrides, and the same place grants already live. A subtree
policy may require review for its own directory even when the root
doesn't (a monotonic add); the root's `per_path` rule automatically
*becomes* owner-review wherever owners are path-confined.

Audit records for `per_path` reviews embed each approval's covered paths,
so "who approved the change to `services/payments/api.rs` in that merge"
is still the same single record lookup by commit oid.

#### Scale honesty

The grants document shares `RepoState`'s 128 KiB DO value cap. Hundreds
of principals with path lists fit comfortably; a monorepo with thousands
of individually-granted engineers hits the same wall the design already
acknowledges for refs-heavy repos (state-doc sharding,
`design.md` → Size limits) — and groups (open question) are the real
compression: grant `group:payments` once, membership lives in the auth
store. Subtree policy count is a non-issue: files live in the repo,
and only the touched ones are ever read.

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
| 1 | auth store DO (users, service accounts, sessions, keys), device flow, OIDC token exchange for service accounts, JWT mint/verify, JWKS + rotation, Bearer + Basic-fallback parsing, credential helper | full login → push round-trip in integration tests (native JWT mint against a test key; `TestServer` with `Authorization` headers); OIDC exchange against a test issuer (issuer/subject/audience matrix); expiry; refresh rotation; session revocation; kid rollover |
| 2 | permission/role model, grants on `RepoState` (users + service accounts), `/api/<repo>/access`, `PUT /api/<repo>/head`, token scope caps + ref-scope enforcement, claim-on-first-push, 401/403 flow | every permission's allow and deny; scoped-token narrowing (never widening); ref-scope rejection before ingest; default-branch permission split |
| 3 | `src/policy.rs`, policy storage + API, tiers 0–3, approvals (`/api/<repo>/approvals`, both uses), `require_review`, audit records on `refs/audit`, audit flattening in maintenance, warn channel | every rule type's reject *and* warn branch; the two-party matrix (self-approval, neither-permissioned, expired/consumed/revoked approval, oid-bound mismatch); **service-account approval rejected** (both uses); review satisfaction arms (fast-forward to approved oid; merge of old + approved; N-distinct-approvers); single-use under concurrent pushes; pending-approval cap; audit-record signature round-trip against the JWKS; audit lookup by commit oid via the file API; flattening preserves the tree; `refs/audit/**` unwritable by clients; policy-validation-at-write |
| 4 | content scanner, pattern packs, lint checks, budgets | secret hit / lint hit / budget-exceeded paths; memory-test variant under `TRANSIENT_BUDGET` |
| 5 | monorepo layer: path-confined grants + token `scope.paths`, delegation loader, subtree `.policy.toml` evaluation, `per_path` review | path-grant coverage allow/deny (push touching in/out-of-grant paths); scope-cap narrowing; confinement and monotonicity rejected at subtree-policy load; old-tree governance (a push editing `.policy.toml` is judged by the previous version); per-path coverage matrix incl. mixed-ownership pushes; delegated-read budget |

Each phase updates `docs/api.md` in the same change (hard rule), and each
new rejection path ships with the test that triggers it. The credential
helper is client-side and gets its own home and test suite per repo
conventions.

## Open questions

* **Second identity provider.** GitHub device flow first; the exchange
  endpoint is shaped for any OIDC provider, but generic-OIDC config
  (issuer discovery, client registration) is unspecified until a second
  provider is real.
* **Custom roles / groups.** Individual-permission grants cover the known
  cases; a role editor is deferred until repeated grants make one earn its
  keep. Groups are the same question wearing two hats: per-rule approver
  sets ("only the release team may approve overrides of
  `workflows-frozen`") and monorepo ownership at scale (grant
  `group:payments` → `paths: ["services/payments/**"]` once, instead of
  per-engineer grants pressing on the DO value cap). Both point at IAM
  groups as grantees — membership in the auth store, never user lists
  inside policy documents. Deferred until a real case, but the monorepo
  layer is where it will first pinch.
* **Sock-puppet approvals, residual.** Service accounts can't approve
  (hard rule), which closes the human-plus-their-bot quorum. The residual
  is one human with two *user* accounts — only upstream-provider identity
  hygiene catches that, and audit records at least expose the pairing for
  review. Requiring the *approver* (not just one of the two parties) to
  hold `policy.override` would narrow it further but breaks the
  junior-pushes-lead-approves flow; not proposed.
* **Bot-driven approvals.** Dependabot-style auto-merge wants a bot to
  approve its own upgrades. Deliberately impossible here (service
  accounts never approve). If it's ever wanted, the shape is a human
  pre-approving a *pattern* (e.g. standing approval for lockfile-only
  diffs) rather than weakening the approver rule — a policy feature, not
  an IAM one. Deferred.
* **Audit tamper-evidence.** Flattening means the audit ref's git history
  is not a hash chain; each record is individually signed but the server
  could theoretically drop one silently. If independent tamper-evidence
  is wanted, chain a predecessor-record hash inside each signed payload
  (making omission detectable), or periodically anchor the audit tip
  externally. Deferred — the server is already the trusted enforcement
  point.
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
