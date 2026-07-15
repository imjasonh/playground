# Design: NetTriage — offline Mac network & config triage

> **Status: design only — awaiting review.** No app directory yet.
> Working title / proposed top-level dir: **`nettriage/`**.
> Rename is cheap before the first ship; say so in review if you prefer
> something else (`housecall`, `triage`, …).

This is the product we deferred while standing up macOS CD. Foundations now
exist and are proven end-to-end:

- [`hello-macos/`](../hello-macos/) — SwiftUI sample with Sparkle **Check for Updates…**
- [`docs/macos-sparkle-design.md`](macos-sparkle-design.md) — shared macOS app conventions
- [`docs/macos-sparkle-setup.md`](macos-sparkle-setup.md) — Developer ID / notarization / EdDSA secrets
- Live ship: notarized ZIP + appcast with `sparkle:edSignature` (e.g. hello-macos 1.0.7)

**This doc proposes the diagnostic app itself**, how it uses on-device Foundation
Models + tool calling, and how it **reuses the existing CD path without new
workflows or secrets** (modulo optional per-app Sparkle key — see §7).

---

## 1. Problem & pitch

When someone’s Mac “can’t get online,” the useful answers are usually about
**path, DNS, proxy/VPN, captive portals, and local config** — not the Wi‑Fi
RSSI bars. Geek Squad (and good IT) ask: Can you resolve names? Which interface
is default? Is there a VPN hijacking the route? Are you behind a proxy? Is DNS
pointing at something dead? Did `/etc/hosts` or a profile break you?

**NetTriage** is a small, notarized macOS app that acts like an offline tech:
the user describes the symptom in plain language (or picks a canned scenario),
an **on-device** language model plans a short investigation, **typed tools**
gather facts from the Mac, and the app returns a grounded explanation plus
suggested next steps — without sending packet captures or config off-device.

### One-liner

> Offline Mac network & config triage: on-device model + local diagnostic tools,
> shipped via the same Developer ID + Sparkle CD as `hello-macos`.

### Why this, not a Wi‑Fi heat-map

Earlier exploration covered CoreWLAN RSSI/channel surveys. That is useful but
**not v1**. Signal strength does not explain most “I can’t reach the internet”
cases on a laptop that already shows full bars. V1 optimizes for **routing and
configuration**, with optional Wi‑Fi *association identity* (SSID/BSSID if
Location allows) as context — not neighbour scanning or channel planning.

---

## 2. Goals & non-goals

### Goals (v1)

1. **Chat / guided triage UI** — user states a problem; app runs a bounded
   tool-using session; shows findings in plain language.
2. **On-device only for model inference** — Apple Foundation Models
   (`LanguageModelSession` + `Tool`). No cloud LLM API key; no prompt/data
   egress for the model loop.
3. **Read-mostly diagnostic tools** — DNS, routing table / default route, path
   status, reachability, HTTP(S) probe, proxy/VPN/DNS config summaries, hosts
   file highlights, interface list. Tools return compact structured text the
   model can reason over.
4. **Works offline for diagnosis** — once installed and stapled, triage that
   only needs local state works with no network. (Probes that *are* the test —
   e.g. “can we reach 1.1.1.1?” — obviously need a path.)
5. **Same CD as hello-macos** — discover → test on PR → notarize + Sparkle on
   `main`. Continuous updates via in-app Check for Updates.
6. **Degrade gracefully** when Apple Intelligence / Foundation Models are
   unavailable (unsupported Mac, region, AI off) — still expose a **manual
   toolbox** of the same diagnostics without the LLM.

### Non-goals (v1)

- Mac App Store / TestFlight / App Sandbox (blocks the useful tools).
- Cloud LLM fallback (keep the trust model simple; revisit later).
- Wi‑Fi neighbour survey, channel planner, spectrum analysis.
- Auto-remediation that changes system state without explicit confirmation
  (v1: explain + copyable commands / deep links; optional “Apply” later).
- Enterprise MDM fleet management, remote agent, or always-on daemon.
- Replacing `wifi-diagnostics` / Wireless Diagnostics .wdig bundles as a
  primary artifact (may *link* to them later).
- iOS / iPad companion.

---

## 3. User experience

### Primary flow

1. Launch → availability banner if Foundation Models unavailable.
2. Home: short prompt field + chips for common scenarios  
   (“Can’t load websites”, “VPN connected but nothing works”, “DNS weird”,
   “Only some sites fail”, “Captive portal / hotel Wi‑Fi”).
3. Session view: streaming model text + **tool call cards** (name, args,
   compact result). User can expand raw tool output.
4. Closing card: **Likely cause**, **Evidence** (which tools), **What to try**
   (ordered, copyable). Optional “Run again with more detail”.
5. Menu: **Check for Updates…** (Sparkle), standard About.

### Tone

Practical tech, not chatty. Prefer “Default route is `utun` (VPN); DNS is still
your ISP resolver — split-tunnel mismatch” over generic “check your cables.”

### Permissions UX

Request only what a tool needs, at first use:

| Capability | Why | When prompted |
|------------|-----|----------------|
| Local network / client sockets | Reachability & HTTP probes | First probe tool |
| Location (optional) | Current Wi‑Fi SSID/BSSID via CoreWLAN | First “current Wi‑Fi” tool — skippable |
| Full Disk / admin | **Not required for v1** | Avoid |

No TCC prompt up front on launch.

---

## 4. Architecture

```
┌──────────────────────────────────────────────────────────┐
│  SwiftUI (NetTriageApp)                                  │
│  SessionView · ToolCallCard · ManualToolboxView          │
└───────────────┬───────────────────────────┬──────────────┘
                │                           │
                ▼                           ▼
┌───────────────────────────┐   ┌───────────────────────────┐
│  TriageSession            │   │  ManualToolbox            │
│  LanguageModelSession +   │   │  Same DiagnosticServices  │
│  tools[] + instructions   │   │  without the model        │
└───────────────┬───────────┘   └─────────────┬─────────────┘
                │                               │
                ▼                               │
┌───────────────────────────┐                   │
│  Tools (FoundationModels) │◄──────────────────┘
│  DnsLookupTool            │
│  DefaultRouteTool         │
│  PathStatusTool           │
│  ReachabilityTool         │
│  HttpProbeTool            │
│  ProxyConfigTool          │
│  VpnInterfacesTool        │
│  DnsConfigTool            │
│  HostsFileTool            │
│  InterfacesTool           │
│  CurrentWifiTool (opt.)   │
└───────────────┬───────────┘
                ▼
┌───────────────────────────┐
│  DiagnosticServices       │
│  NWPathMonitor, Network,  │
│  scutil/networksetup/dig  │
│  wrappers, CoreWLAN       │
└───────────────────────────┘
```

### Model layer (Foundation Models)

- Deployment target: **macOS 26+** (Foundation Models / Apple Intelligence).
- Check `SystemLanguageModel.default.availability` before creating a session.
- One `LanguageModelSession` per triage run (not one forever); pass tools +
  system instructions specialized for Mac network triage.
- Use `@Generable` for a final **TriageReport** (headline, likelyCause,
  evidence[], steps[]) so the UI is not stuck parsing freeform markdown.
- Tool outputs stay **small** (summaries, top N routes, truncated hosts). The
  on-device context window is not GPT-4-class; dump-the-world tools will thrash.

### Tool layer

- Each tool = Swift `Tool`: `name`, `description`, `@Generable Arguments`,
  `call(arguments:) -> String` (or small `PromptRepresentable` output).
- Implementation calls into **DiagnosticServices** (testable without the model).
- Prefer Apple frameworks (`Network`, `SystemConfiguration`, `CoreWLAN`) over
  shelling out; use `/usr/bin/dig`, `scutil`, `networksetup`, `route` only when
  the framework surface is insufficient — and always with timeouts + output caps.
- **No `codesign --deep`-style footguns** in CD; product code must not spawn
  unbounded shell pipelines.

### Safety / trust

- System instructions: only use tools for facts; never invent IP/DNS results;
  if a tool errors, say so; prefer reversible advice.
- Tools are read-only in v1. Any future mutation tool requires an explicit
  UI confirm outside the model’s autonomous loop.
- No telemetry of prompts/tool results in v1 (keep offline promise honest).

---

## 5. V1 tool catalog (concrete)

| Tool | What it returns (compact) | Primary APIs / commands |
|------|---------------------------|-------------------------|
| `interfaces` | Name, type, IPv4/IPv6, status | `NWPath` / SCNetworkInterface / `ifconfig`-class via SC |
| `default_route` | Gateway, interface, whether utun/VPN | `route get default` / SCDynamicStore |
| `path_status` | Satisfied/unsatisfied, expensive, interfaces | `NWPathMonitor` snapshot |
| `dns_config` | Resolvers, search domains, scoped DNS | `scutil --dns` (parsed) |
| `dns_lookup` | A/AAAA/CNAME for a name via system + optional Do53 | `DNS` / `dig` with timeout |
| `reachability` | ICMP or TCP connect to host:port | `Network.framework` NWConnection |
| `http_probe` | Status, redirect, timing, TLS error class | `URLSession` to URL |
| `proxy_config` | System HTTP/HTTPS/SOCKS/PAC summary | `SCDynamicStore` / `networksetup -getwebproxy` |
| `vpn_interfaces` | utun/ipsec list + whether default path uses them | interface enum + path |
| `hosts_file` | Non-comment lines matching query / surprising overrides | read `/etc/hosts` (world-readable) |
| `current_wifi` | SSID/BSSID/security if authorized; else “denied” | CoreWLAN + Location |

**Explicitly deferred:** `wifi_scan` / channel congestion / RSSI ranking.

---

## 6. Repo layout (new macOS app)

Follow [`AGENTS.md`](../AGENTS.md) / hello-macos: **top-level directory**, not under
`ios/`, no `index.html`.

```
nettriage/
├── project.yml                 # platform: macOS (discovery marker)
├── NetTriage.entitlements      # Hardened Runtime + Sparkle helpers (+ any needed)
├── Sources/
│   ├── NetTriageApp.swift
│   ├── SparkleUpdater.swift    # copy/adapt from hello-macos
│   ├── UI/…
│   ├── Triage/                 # session, prompts, TriageReport @Generable
│   ├── Tools/                  # FoundationModels Tool types
│   └── Diagnostics/            # DiagnosticServices (unit-tested)
├── Tests/NetTriageTests/
├── fastlane/                   # test + beta (fork of hello-macos)
├── Gemfile
├── README.md
└── .gitignore
```

| Item | Value |
|------|--------|
| Bundle ID | `io.github.imjasonh.nettriage` |
| Product name | NetTriage |
| Sparkle feed | `https://imjasonh.github.io/playground/macos/nettriage/appcast.xml` |
| Release tag shape | `nettriage-v<marketing>` (from `sparkle-metadata.json` `app` field) |
| Min OS | **macOS 26.0** (Foundation Models) |

`hello-macos` stays the tiny CD canary (low risk, low deps). NetTriage is the
real product; do **not** fold it into `hello-macos`.

---

## 7. Continuous delivery — reuse existing infra

### What already works (no new workflows)

| Piece | Behavior for a new app |
|-------|------------------------|
| `discover-macos-apps.sh` | Picks up any top-level dir with `project.yml` + `platform: macOS` |
| `macos.yml` | Tests changed macOS apps on PRs; ships on `main` when secrets exist |
| `macos-ci.sh` | Per app: `xcodegen` → `fastlane test` → (deploy) `fastlane beta` → `publish-macos-sparkle.sh` |
| `publish-macos-sparkle.sh` | Already generic: reads `app`, `feed_path`, `ed_signature`, enclosure from `sparkle-metadata.json` |

**Expected CI delta for NetTriage: zero workflow YAML edits** if we copy the
hello-macos `fastlane beta` contract (write `sparkle-metadata.json` + enclosure
ZIP under `fastlane/release/`).

### Secrets

Reuse the secrets already configured for hello-macos:

| Secret | Reuse? |
|--------|--------|
| `MACOS_DEVELOPER_ID_P12` / `PASSWORD` | Yes — same Developer ID Application cert |
| `ASC_*` / `APPLE_TEAM_ID` | Yes — notarization |
| `SPARKLE_EDDSA_PRIVATE_KEY` | **Yes for v1** — bake the **same** `SUPublicEDKey` already in hello-macos into NetTriage Info.plist |

Sharing one EdDSA keypair across playground macOS apps is operationally simple
(one secret, already proven). Tradeoff: a private-key leak affects every app
using it. Acceptable for this playground; document that a future “serious”
app can generate its own pair and either add `SPARKLE_EDDSA_PRIVATE_KEY_NETTRIAGE`
or switch to a naming scheme later. **Not blocking v1.**

### Fastlane / Sparkle embedding

Copy from `hello-macos/` and rename constants:

- Sparkle SPM dependency + `SUFeedURL` / `SUPublicEDKey` / auto-check keys
- Entitlement `com.apple.security.cs.disable-library-validation`
- Nested Sparkle re-sign before notarize (`resign_sparkle_embedded!`)
- `notarytool` submit with log dump on Invalid
- `sign_update` → `ed_signature` in metadata
- Metadata `app: "nettriage"`, `feed_path: "macos/nettriage/appcast.xml"`

Optional small cleanup (not required to ship): extract shared Fastfile helpers
into `.github/fastlane/` or a Ruby module so hello-macos and nettriage do not
drift. Prefer **copy-paste first**, extract after the second app ships green.

### What CD does *not* need

- New GitHub Actions workflow
- Mac TestFlight / ASC app record for this bundle (Developer ID only)
- Pages browser-app registration (`index.html`)
- Changes to `deploy.yml` / `preview.yml` (macOS apps are not Pages apps)

### Offline vs updates

Same contract as hello-macos: stapled build launches offline; Sparkle update
check needs network once. Diagnosis that only reads local config works offline;
connectivity probes are part of the investigation when relevant.

---

## 8. Testing strategy

| Layer | Where | Notes |
|-------|-------|-------|
| DiagnosticServices unit tests | `NetTriageTests` | Parse fixtures for `scutil --dns`, hosts file, fake path snapshots; **no** live network required in CI |
| Tool argument / report `@Generable` shapes | Unit tests | Compile-time + decode fixtures if useful |
| UI smoke | Optional XCUITest later | Not required for first PR |
| Foundation Models | **Not** asserted in CI | Runners may lack Apple Intelligence; gate model tests behind a local scheme or manual checklist |
| CD | `macos.yml` | Same as hello-macos: test on PR; notarize+appcast on `main` |

CI must stay green on stock `macos-latest` without relying on the on-device model
being present. Ship the Manual Toolbox path as the always-testable core.

---

## 9. Privacy & entitlements

- Hardened Runtime on; notarized Developer ID distribution.
- Sparkle: `com.apple.security.cs.disable-library-validation` (same as hello-macos).
- **No App Sandbox** — required for useful routing/DNS/config inspection.
- Location only for optional current-Wi‑Fi identity.
- Do not embed analytics SDKs in v1.
- README documents what tools read (and that model inference stays on-device).

---

## 10. Phased delivery

### Phase 0 — design review (this doc)

Stop here for product/CD agreement. Open questions in §11.

### Phase 1 — scaffold + CD canary

1. Create `nettriage/` from hello-macos skeleton (Sparkle, fastlane, empty UI).
2. Bundle ID / feed URL / metadata `app: nettriage`.
3. Ship **0.1.0** via `main` to prove a second appcast path
   (`macos/nettriage/appcast.xml`) without depending on Foundation Models yet.
4. Manual install + Check for Updates smoke (0.1.0 → 0.1.1 bump).

### Phase 2 — DiagnosticServices + Manual Toolbox

1. Implement services + unit tests with fixtures.
2. SwiftUI toolbox UI (buttons → result panes) — usable without Apple Intelligence.
3. Still no model required for a useful app.

### Phase 3 — Foundation Models triage

1. Tools wrapping the services; `TriageSession`; `@Generable TriageReport`.
2. Availability gating + chips/scenarios.
3. Hardening: timeouts, output caps, instruction tuning on a real Mac.

### Phase 4 — polish (optional)

- Copyable “fix commands” block
- Export a markdown report
- Confirmed-apply actions (flush DNS cache, etc.) behind UI confirms
- Extract shared Fastlane helpers

---

## 11. Open questions for review

Please decide / correct before implementation:

1. **Name** — stick with `nettriage` / NetTriage, or rename?
2. **Sparkle key** — reuse hello-macos EdDSA keypair (recommended for v1), or
   generate a dedicated pair + new secret now?
3. **OS floor** — macOS 26-only is correct for Foundation Models; confirm we
   will not support older macOS even for Manual Toolbox-only (supporting both
   means dual deployment targets or `#available` splits — doable but messier).
4. **Shell vs frameworks** — OK to call `scutil` / `dig` / `networksetup` when
   parsed output is clearer than SC APIs, with timeouts?
5. **Scope creep** — any v1 tool from §5 you want cut or added before Phase 2?
6. **Remediation** — confirm v1 is explain-only (no automatic `networksetup`
   changes).
7. **Phase 1 CD canary** — ship an empty-ish 0.1.0 before Diagnostics land, or
   wait until Manual Toolbox exists so the first public ZIP is useful?

---

## 12. Success criteria

- [ ] Design approved (this doc).
- [ ] `nettriage/` discovered by `macos.yml` with **no** workflow file changes.
- [ ] Notarized release + appcast with `sparkle:edSignature` on `main`.
- [ ] In-app update works (N → N+1) like hello-macos 1.0.6 → 1.0.7.
- [ ] Manual Toolbox diagnoses a forced bad DNS / proxy case without the model.
- [ ] On an Apple Intelligence Mac, a canned “VPN but broken DNS” scenario
      produces a `TriageReport` that cites real tool evidence.

---

## 13. References

- [`docs/macos-sparkle-design.md`](macos-sparkle-design.md) — macOS app + Sparkle CD
- [`docs/macos-sparkle-setup.md`](macos-sparkle-setup.md) — secrets / keys
- [`hello-macos/`](../hello-macos/) — reference implementation for CD
- [Foundation Models](https://developer.apple.com/documentation/foundationmodels) —
  on-device LLM, `Tool`, `@Generable`
- WWDC25: *Meet the Foundation Models framework*, *Deep dive…*, *Code-along…*
