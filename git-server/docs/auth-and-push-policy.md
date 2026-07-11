# Design: users, auth, and push-time policy

Status: **design only, not yet built.** This document proposes (1) users and
authentication, (2) a declarative push-time policy engine that can reference
those users, and (3) blob-content checks (secret scanning and lint rules)
that run inside the policy engine. The three land as separate phases, in
that order — identity must exist before "who can bypass this rule" means
anything.

Everything here is constrained by what the Worker actually is: wasm, CPU
metered (`cpu_ms = 300000` on the paid plan, see `wrangler.toml`), a hard
128 MiB isolate memory ceiling (enforced by `tests/memory.rs`), and **no
ability to run user-supplied code**. So policy is *data*, not hooks: a
declarative rule set evaluated by the server, at points in the push
pipeline where the needed facts are already cheap.

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

The last row is why content checks (phase 3) get their own byte budgets;
everything above it is metadata the pipeline produces anyway.

Rejections surface through the existing report-status path
(`src/protocol.rs::report_status`): `ng <ref> <reason>` per ref, with the
pipeline's existing invariant intact — refs, pack manifest, and file-log
flip atomically in the Durable Object or not at all. A rejection after
ingest leaves an orphan pack in R2, exactly like today's per-ref validation
failures; the maintenance sweep already collects those.

---

## Phase 1: users and authentication

### Requirements

* Stock git clients only — so **HTTP Basic auth** (username + token), which
  every git credential helper speaks natively. SSH is out (Workers is
  HTTP-only).
* Identity must be available to the push path cheaply, so policy rules can
  scope to users and honor bypass lists.
* No expensive password hashing per request. The Worker is CPU-metered;
  an argon2/bcrypt verification on every `git fetch` is real money and
  latency. Tokens, not passwords, make this a non-issue (below).
* Fits the existing storage shape: Durable Objects for small consistent
  state, R2 for bulk, KV for the registry.

### Model

**Users are server-wide** (not per-repo). A user document:

```jsonc
{
  "login": "alice",              // <repo>-style charset: [A-Za-z0-9._-], ≤100
  "emails": ["alice@example.com"],  // for author/committer policy checks
  "server_role": "user",         // "user" | "admin"
  "tokens": [
    { "id": "t1", "sha256": "<hex>", "label": "laptop",
      "created_ms": 0, "expires_ms": null }
  ]
}
```

**Per-repo access lives on `RepoState`** (the per-repo DO document), next to
refs and the pack manifest, so it is read in the same state load every
request already performs:

```jsonc
{
  "visibility": "public",        // "public" (anonymous read) | "private"
  "maintainers": ["alice"],      // push + edit access/policy
  "writers": ["bot-deploy"]      // push only
}
```

Semantics:

| Principal | Public repo | Private repo |
|---|---|---|
| anonymous | read | nothing |
| authenticated, no grant | read | nothing |
| writer | read + push | read + push |
| maintainer | + edit access & policy | same |
| server admin | everything, on every repo | same |

The first **authenticated** push to an empty repo makes the pusher its
maintainer (repo claiming). Server admins bootstrap users; maintainers
manage their repos.

### Tokens, not passwords

Tokens are server-generated, high-entropy (128-bit) secrets with a
recognizable prefix for secret-scanner friendliness, e.g.
`gsv1_<32 hex chars>`. The server stores only `SHA-256(token)`.
Verification is: hash the presented token, look up the hash. Because the
token is uniform random, SHA-256 preimage resistance is sufficient — no
KDF, no per-request CPU cost, and the lookup is constant-time by
construction (an index probe on the digest, not a string compare against
each candidate).

The Basic-auth username must match the token's user; a mismatch is
`bad credentials` (same error as an unknown token — don't oracle which part
was wrong).

### Where identities live

A new **single-instance `AuthDo`** (SQLite-backed Durable Object, same
migration mechanism as `RepoStateDo`): user documents plus a
token-hash → login index. One DO read per authenticated request, from one
global instance.

Two mitigations for that being a global serialization point:

* Reads of public repos stay anonymous — no auth lookup at all on today's
  dominant traffic.
* A small in-isolate cache (token hash → login, TTL ~60 s, bounded entries)
  absorbs bursts like a clone's advertisement + fetch pair. Revocation
  latency is the TTL, which is acceptable at seconds.

KV was considered and rejected for the authoritative store: KV is
eventually consistent (minutes), which turns token revocation into a
window, and tokens are exactly the thing you revoke in a hurry.

### Bootstrap

The deploy workflow get-or-generates a `GIT_ROOT_TOKEN` Worker secret,
exactly like it already does for `web-push`'s `VAPID_PRIVATE_KEY` (see
`deploy-workers.yml`): generated once, stable across deploys. That token
authenticates the virtual user `root` (server admin) without touching
`AuthDo`, and is used to create the first real users via the API.

### HTTP integration

* Protected routes answer `401` with `WWW-Authenticate: Basic realm="git"`;
  stock git prompts or consults its credential helper and retries. This is
  the entire client-side story — nothing to install.
* **Push always requires auth** once this phase ships. The prototype's
  anonymous push dies at that flag day; an `ALLOW_ANONYMOUS_PUSH` var
  exists only as a rollback lever and defaults off.
* Fetch and the read `/api/…` routes require auth only for
  `visibility = "private"` repos. Existing repos default to `public`, so
  nothing currently readable becomes unreadable.

### New API surface (added to `api.md` when built)

| Route | Who | What |
|---|---|---|
| `GET /api/whoami` | any token | the authenticated login + role |
| `PUT /api/users/<login>` | admin | create/update a user |
| `GET /api/users/<login>` | admin or self | user doc (token hashes elided) |
| `POST /api/users/<login>/tokens` | admin or self | mint a token; plaintext returned **once** |
| `DELETE /api/users/<login>/tokens/<id>` | admin or self | revoke |
| `GET /api/<repo>/access` | maintainer | visibility + grants |
| `PUT /api/<repo>/access` | maintainer | update them |

Out of scope for this phase: OAuth/OIDC, SSH keys, sessions/cookies, and
failed-auth rate limiting (noted as an open question; a KV counter with a
short TTL is the likely cheap answer if probing shows up in logs).

---

## Phase 2: the policy engine

### Rule shape

A per-repo **policy document**: an ordered list of named rules, each
`scope × check × action`. Stored as a `policy` field on `RepoState`
(versioned and CAS-swapped with the rest of the state doc; the 128 KiB DO
value cap is ample for rules), edited via `PUT /api/<repo>/policy`
(maintainer), retrieved via `GET /api/<repo>/policy`. TOML on the wire for
humans, canonical JSON in the DO.

```toml
[[rule]]
name = "protect-main"                # names are API: they appear in ng lines
refs  = ["refs/heads/main"]          # glob scope; default: all refs
deny  = ["delete", "force"]          # tier-0 verbs: create | delete | force

[[rule]]
name  = "workflows-frozen"
paths = [".github/workflows/**"]     # glob on changed paths (tree diff)
deny  = ["add", "modify", "delete"]
bypass = ["user:alice", "role:maintainer"]

[[rule]]
name = "no-big-blobs"
max_blob_bytes = "5MB"

[[rule]]
name = "ticket-ref"
refs = ["refs/heads/main"]
commit_message_pattern = 'Resolves [A-Z]+-\d+'

[[rule]]
name = "you-are-you"
require_author_email_matches_pusher = true   # author email ∈ pusher's emails

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
| 4 — content | secret patterns, lint checks | `Odb::read`, budgeted — phase 3 below |

"Force" at tier 0 means: `old` is a non-ancestor of `new`. The pipeline's
CAS already rejects *stale* olds; the force check additionally needs an
ancestry walk between two commits in the (old ∪ new) odb, bounded like the
existing connectivity check.

### Users in policy: bypass is explicit

`bypass` lists principals (`user:<login>`, `role:maintainer`,
`role:admin`) who **may** override the rule — but override is never
silent. A bypass-eligible pusher must say so:

```
git push -o policy.override=workflows-frozen
```

The server advertises the `push-options` capability; options arrive in the
command section, before any pack bytes. An override without eligibility is
rejected (`ng <ref> policy "workflows-frozen": override not permitted`);
eligibility without the option still enforces the rule. This keeps
maintainers subject to policy by default, makes every exception a
deliberate act, and gives structured logs an audit line (pusher, rule,
refs) for free.

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
* One glob implementation (gitignore-style `**`) shared by `refs` and
  `paths` — a new "single home" per `AGENTS.md`.
* Custom regexes (`commit_message_pattern`, custom content patterns) are
  compiled with the linear-time `regex` engine — no backtracking, so no
  ReDoS — with caps on pattern count and compiled size, validated at
  `PUT /api/<repo>/policy` time so a bad policy fails at write, not at
  someone else's push.

### Enforcement points

Tier 0 evaluates right after command parse in `receive_pack` — before
`PackIngest::start`, so a protected-ref rejection never writes to R2.
Tier 1's fast-fail lives in the scan feed loop and aborts the multipart
upload. Tiers 2–4 evaluate inside `apply_push`, after `resolve_pack` and
the file-log build produced their facts, **before** `StateStore::apply_push`
— the same slot as today's connectivity check, with the same orphan-pack
consequence on rejection (already handled by the maintenance sweep).

All of it lives in transport-agnostic modules (a new `src/policy.rs`), so
`cargo test` exercises the same code the Worker runs, and every rejection
branch gets an integration test per the crate's error-path rule.

---

## Phase 3: content checks (tier 4)

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
phase 2. Findings are reported as rule + path + line number — **never** the
matched text; the report-status channel must not echo secrets back.

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
| 1 | `AuthDo`, token auth, repo access, `/api/users` + `/api/<repo>/access`, 401 flow | git credential round-trip in integration tests (`TestServer` with `Authorization` headers); revocation; claim-on-first-push |
| 2 | `src/policy.rs`, policy storage + API, tiers 0–3, bypass/override, warn channel | every rule type's reject *and* warn branch; override audit line; policy-validation-at-write |
| 3 | content scanner, pattern packs, lint checks, budgets | secret hit / lint hit / budget-exceeded paths; memory-test variant under `TRANSIENT_BUDGET` |

Each phase updates `docs/api.md` in the same change (hard rule), and each
new rejection path ships with the test that triggers it.

## Open questions

* **Retro-scanning.** A policy added after a secret already landed doesn't
  scan history. A `POST /api/<repo>/scan` walking existing blobs under the
  same budget machinery (repeated calls to converge, like `/repack`) is the
  likely shape — not in scope for phase 3.
* **Failed-auth rate limiting.** Token probing is cheap for an attacker
  and each probe costs us an `AuthDo` read (cache misses only). A KV
  counter keyed by IP with a short TTL if logs show probing.
* **Default visibility at flag day.** Proposed: existing repos stay
  `public` (read) but push locks to authenticated users everywhere,
  with `ALLOW_ANONYMOUS_PUSH` as the rollback lever only.
* **Token expiry defaults.** Proposed: no default expiry (prototype), but
  the field exists so policy can later require expiring tokens.
