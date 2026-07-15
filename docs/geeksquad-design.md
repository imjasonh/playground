# Design: Geek Squad — offline Mac network & config triage

> **Status: Phase 1 implementation includes Chat + Toolbox.** Directory
> **`geeksquad/`**, Bundle ID `io.github.imjasonh.geeksquad`, product name
> **Geek Squad**. **0.1.0** ships Foundation Models chat (primary) that calls
> local diagnostic tools, plus a Manual Toolbox fallback. Deployment target is
> **macOS 14+** so CI can build; chat requires **macOS 26+ / Apple Intelligence**
> at runtime (`#if canImport` + availability checks, weak-linked framework).

This is the product we deferred while standing up macOS CD. Foundations now
exist and are proven end-to-end:

- [`hello-macos/`](../hello-macos/) — SwiftUI sample with Sparkle **Check for Updates…**
- [`docs/macos-sparkle-design.md`](macos-sparkle-design.md) — shared macOS app conventions
- [`docs/macos-sparkle-setup.md`](macos-sparkle-setup.md) — Developer ID / notarization / EdDSA secrets
- Live ship: notarized ZIP + appcast with `sparkle:edSignature` (e.g. hello-macos 1.0.7)

**This doc is the diagnostic app plan**: on-device Foundation Models + tool
calling, and how it **reuses the existing CD path** (same workflows, same
secrets, second appcast).

### Review decisions (locked)

| Topic | Decision |
|-------|----------|
| Name | **Geek Squad** (`geeksquad/`) |
| Sparkle | Reuse as much as possible — **same EdDSA keypair + Fastlane patterns**; two apps are fine (see §7) |
| OS floor | **macOS 14+** for Manual Toolbox (0.1.0); Phase 2 chat needs **macOS 26+** / Apple Intelligence |
| Diagnostics APIs | Prefer **frameworks**; fall back to CLIs when needed |
| Remediation | **Propose fixes**; do **not** apply them automatically in v1 |
| First ship | **0.1.0 includes Chat + Manual Toolbox** (chat needs Apple Intelligence at runtime) |

---

## 1. Problem & pitch

When someone’s Mac “can’t get online,” the useful answers are usually about
**path, DNS, proxy/VPN, captive portals, and local config** — not the Wi‑Fi
RSSI bars. A good tech asks: Can you resolve names? Which interface is default?
Is a VPN hijacking the route? Are you behind a proxy? Is DNS pointing at
something dead? Did `/etc/hosts` or a profile break you?

**Geek Squad** is a small, notarized macOS app that acts like an offline tech:
the user describes the symptom in plain language (or picks a canned scenario),
an **on-device** language model plans a short investigation, **typed tools**
gather facts from the Mac, and the app returns a grounded explanation plus
**proposed** next steps — without sending packet captures or config off-device,
and without changing system state on its own.

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

### Goals (v1 / 0.1.0+)

1. **Usable from first public build (0.1.0)** — Manual Toolbox with real
   diagnostics even before (or without) Foundation Models. Chat triage lands
   in the same release train as soon as it is ready, but **0.1.0 is not a
   hollow CD canary**.
2. **Chat / guided triage UI** (when Apple Intelligence is available) — user
   states a problem; app runs a bounded tool-using session; shows findings.
3. **On-device only for model inference** — Apple Foundation Models
   (`LanguageModelSession` + `Tool`). No cloud LLM API key.
4. **Read-mostly diagnostic tools** — DNS, routing / default route, path
   status, reachability, HTTP(S) probe, proxy/VPN/DNS config, hosts highlights,
   interfaces. Prefer frameworks; CLI fallbacks with timeouts + output caps.
5. **Propose fixes, don’t apply them** — copyable steps / commands / Settings
   deep links; no autonomous `networksetup` mutations.
6. **Works offline for local-config diagnosis** — stapled build; probes that
   *are* the test still need a path when relevant.
7. **Same CD as hello-macos** — discover → test on PR → notarize + Sparkle on
   `main`. Continuous updates via Check for Updates.
8. **Degrade gracefully** when Foundation Models are unavailable — Manual
   Toolbox remains fully usable.

### Non-goals (v1)

- Mac App Store / TestFlight / App Sandbox.
- Cloud LLM fallback.
- Wi‑Fi neighbour survey / channel planner / RSSI ranking.
- Auto-remediation (flush DNS, toggle VPN, rewrite proxies, etc.).
- Enterprise MDM / remote agent / always-on daemon.
- Supporting pre–macOS 26.
- Folding into `hello-macos` (keep hello as the tiny CD canary).

---

## 3. User experience

### Primary flows

**A. Manual Toolbox (always available — required for 0.1.0)**  
Buttons / sections for interfaces, default route, DNS config, DNS lookup,
path status, reachability, HTTP probe, proxy, VPN, hosts. Each shows a clear
result pane. “Copy report” exports markdown.

**B. Guided triage (when Foundation Models available)**  
1. Prompt + scenario chips (“Can’t load websites”, “VPN connected but broken”,
   “DNS weird”, “Only some sites fail”, “Captive portal”).
2. Session: streaming text + tool-call cards.
3. Closing **TriageReport**: likely cause, evidence, **proposed** steps
   (copyable — not executed).

**C. Updates**  
Menu: **Check for Updates…** (Sparkle), About.

### Tone

Practical tech. Prefer “Default route is `utun` (VPN); DNS is still your ISP
resolver — likely split-tunnel mismatch. Try: disconnect VPN and retest” over
generic “check your cables.”

### Permissions UX

Request only what a tool needs, at first use:

| Capability | Why | When prompted |
|------------|-----|----------------|
| Local network / client sockets | Reachability & HTTP probes | First probe |
| Location (optional) | Current Wi‑Fi SSID/BSSID | First current-Wi‑Fi tool — skippable |

No TCC prompt on launch. No Full Disk Access required for v1.

---

## 4. Architecture

```
┌──────────────────────────────────────────────────────────┐
│  SwiftUI (GeekSquadApp)                                  │
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
│  (see §5)                 │
└───────────────┬───────────┘
                ▼
┌───────────────────────────┐
│  DiagnosticServices       │
│  Prefer: Network,         │
│  SystemConfiguration,     │
│  CoreWLAN                 │
│  Fallback: dig, scutil,   │
│  networksetup, route      │
│  (timeouts + output caps) │
└───────────────────────────┘
```

### Model layer

- **macOS 26+** only.
- Check `SystemLanguageModel.default.availability` before sessions.
- One `LanguageModelSession` per triage run; tools + triage-focused instructions.
- `@Generable TriageReport` for the closing card (headline, likelyCause,
  evidence[], proposedSteps[]).
- Keep tool outputs small — on-device context is limited.

### Tool / service layer

- Tools wrap **DiagnosticServices** (unit-tested without the model).
- **Prefer frameworks** (`Network`, `SystemConfiguration`, `CoreWLAN`).
- **CLI fallback** only when frameworks are insufficient or opaque — always
  with timeouts, argv arrays (no shell string concat), and truncated stdout.

### Safety

- Instructions: ground claims in tool results; never invent DNS/IP facts.
- v1 tools are read-only. Proposed fixes are text for the human.
  **Hard rule for coding agents:** see [`geeksquad/AGENTS.md`](../geeksquad/AGENTS.md) —
  tools available to the Geek Squad agent must never take action, only read
  and diagnose. Capability is enforced by the tool surface.
- No telemetry of prompts/tool results in v1.

---

## 5. V1 tool catalog

| Tool | Returns (compact) | Prefer | Fallback CLI |
|------|-------------------|--------|--------------|
| `interfaces` | Name, type, IPv4/IPv6, status | SCNetwork / Network | — |
| `default_route` | Gateway, interface, VPN/utun? | SCDynamicStore | `route get default` |
| `path_status` | Satisfied?, expensive?, ifaces | `NWPathMonitor` | — |
| `dns_config` | Resolvers, search, scoped DNS | SCDynamicStore | `scutil --dns` |
| `dns_lookup` | A/AAAA/CNAME | Network / DNSSD | `dig` |
| `reachability` | TCP connect host:port | `NWConnection` | — |
| `http_probe` | Status, redirect, timing, TLS class | `URLSession` | — |
| `proxy_config` | HTTP/HTTPS/SOCKS/PAC | SCDynamicStore | `networksetup -get*proxy` |
| `vpn_interfaces` | utun/ipsec + default-path use | interface enum + path | — |
| `hosts_file` | Surprising `/etc/hosts` lines | file read | — |
| `current_wifi` | SSID/BSSID if allowed | CoreWLAN | — |

**Deferred:** `wifi_scan` / channel congestion / RSSI ranking.

**Remediation (propose only):** the model/UI may suggest steps such as
“forget Wi‑Fi network”, “disconnect VPN”, “disable HTTP proxy”, “flush DNS
(`dscacheutil -flushcache`)” as **copyable instructions** — never run them.

---

## 6. Repo layout

```
geeksquad/
├── project.yml                 # platform: macOS (discovery marker)
├── GeekSquad.entitlements      # Hardened Runtime + Sparkle helpers
├── Sources/
│   ├── GeekSquadApp.swift
│   ├── SparkleUpdater.swift    # copy/adapt from hello-macos
│   ├── UI/…                    # ManualToolbox + Session
│   ├── Triage/                 # session, prompts, TriageReport
│   ├── Tools/                  # FoundationModels Tool types
│   └── Diagnostics/            # DiagnosticServices (unit-tested)
├── Tests/GeekSquadTests/
├── fastlane/                   # test + beta (fork of hello-macos)
├── Gemfile
├── README.md
└── .gitignore
```

| Item | Value |
|------|--------|
| Bundle ID | `io.github.imjasonh.geeksquad` |
| Product / app name | Geek Squad |
| Sparkle feed | `https://imjasonh.github.io/playground/macos/geeksquad/appcast.xml` |
| Release tag | `geeksquad-v<marketing>` |
| Min OS | **macOS 14.0** for Manual Toolbox (0.1.0); **macOS 26+** when Phase 2 chat ships |

`hello-macos` remains the low-deps CD canary. Geek Squad is the product app.

---

## 7. Continuous delivery — reuse Sparkle / CD (two apps are fine)

### Short answer

**Sharing Sparkle machinery does not mean only one app.**  
`hello-macos` and `geeksquad` are two top-level macOS apps. Each gets:

- its own Bundle ID, ZIP, GitHub Release tag, and appcast path
- the **same** CI workflow (`macos.yml`), Fastlane pattern, Developer ID cert,
  notarization secrets, and (for v1) **same EdDSA keypair**

Sparkle ties an install to **one feed URL** baked into that app’s Info.plist.
Two apps ⇒ two feeds (`macos/hello-macos/appcast.xml` and
`macos/geeksquad/appcast.xml`). They can verify enclosures with the **same
public key** without conflicting.

```
                    ┌─ hello-macos  → gh-pages/macos/hello-macos/appcast.xml
macos.yml / secrets ┤
                    └─ geeksquad    → gh-pages/macos/geeksquad/appcast.xml
                         (same SPARKLE_EDDSA_PRIVATE_KEY / SUPublicEDKey)
```

### What already works (no new workflows)

| Piece | Behavior |
|-------|----------|
| `discover-macos-apps.sh` | Any top-level `project.yml` with `platform: macOS` |
| `macos.yml` | Test changed apps on PRs; ship on `main` when secrets exist |
| `macos-ci.sh` | Per app: xcodegen → test → beta → `publish-macos-sparkle.sh` |
| `publish-macos-sparkle.sh` | Generic via `sparkle-metadata.json` (`app`, `feed_path`, …) |

**Expected CI delta: zero workflow YAML edits** if `geeksquad/fastlane` writes
the same metadata contract as hello-macos.

### Secrets (reuse)

| Secret | Reuse? |
|--------|--------|
| `MACOS_DEVELOPER_ID_*` | Yes |
| `ASC_*` / `APPLE_TEAM_ID` | Yes |
| `SPARKLE_EDDSA_PRIVATE_KEY` | **Yes** — same seed; bake the existing `SUPublicEDKey` into Geek Squad |

Tradeoff of one shared key: a leak affects every app using it. Fine for this
playground. A later app can mint its own pair if needed.

### Fastlane / Sparkle embedding

Copy from `hello-macos/`: SPM Sparkle, feed/public-key Info keys, entitlement,
nested Sparkle re-sign, `notarytool` + log dump, `sign_update`, metadata with
`app: "geeksquad"` and `feed_path: "macos/geeksquad/appcast.xml"`.

Optional later: extract shared Fastlane helpers so the two apps do not drift.
**Copy-paste first**; extract after Geek Squad ships green.

---

## 8. Testing strategy

| Layer | Where | Notes |
|-------|-------|-------|
| DiagnosticServices | `GeekSquadTests` | Fixtures for DNS/hosts/path; no live net required in CI |
| Manual Toolbox | Unit + light UI later | Core of 0.1.0 |
| Foundation Models | Manual / local | CI must not require Apple Intelligence |
| CD | `macos.yml` | Same as hello-macos |

---

## 9. Privacy & entitlements

- Hardened Runtime; Developer ID notarization; **no App Sandbox**.
- Sparkle: `com.apple.security.cs.disable-library-validation`.
- Location only for optional current Wi‑Fi.
- No analytics SDKs in v1.
- README documents reads + on-device inference.

---

## 10. Phased delivery

### Phase 0 — design (this doc)

Review complete once this revision matches intent.

### Phase 1 — usable 0.1.0 (this PR)

1. Scaffold `geeksquad/` from hello-macos (Sparkle + Fastlane).
2. **DiagnosticServices** + unit tests (frameworks first, CLI fallback).
3. **Chat (primary):** Foundation Models + diagnostic tools; propose-only fixes.
4. **Manual Toolbox** fallback when Apple Intelligence is unavailable.
5. Sparkle Check for Updates; shared EdDSA key.
6. Merge to `main` → notarized **0.1.0**.

### Phase 2 — polish (optional)

- Richer streaming / transcript UI, Settings deep links, shared Fastlane extract.
- Confirmed-apply actions only if we explicitly revisit “don’t action yet.”

---

## 11. Open questions (remaining)

Most review items are locked above. Left only if you care before coding:

1. **Trademark / naming tone** — “Geek Squad” is a Best Buy mark; fine for a
   personal playground experiment, but say if you want a disclaimer in About /
   README (“unofficial; not affiliated with Best Buy”).
2. **0.1.0 chat** — include a *stub* triage UI that says “requires Apple
   Intelligence” vs hide chat entirely until Phase 2?

Default if unspecified: disclaimer yes; hide chat until Phase 2 so 0.1.0 UI
stays honest and focused on the toolbox.

---

## 12. Success criteria

- [ ] Design matches review decisions (this revision).
- [ ] `geeksquad/` discovered by `macos.yml` with **no** workflow edits.
- [ ] **0.1.0** notarized + appcast `edSignature`; Manual Toolbox usable offline
      for local-config cases.
- [ ] In-app update works (0.1.0 → 0.1.1) on Geek Squad itself.
- [ ] `hello-macos` continues to ship independently on its own feed.
- [ ] Later: on an Apple Intelligence Mac, guided triage cites real tool evidence
      and only **proposes** fixes.

---

## 13. References

- [`docs/macos-sparkle-design.md`](macos-sparkle-design.md)
- [`docs/macos-sparkle-setup.md`](macos-sparkle-setup.md)
- [`hello-macos/`](../hello-macos/)
- [Foundation Models](https://developer.apple.com/documentation/foundationmodels)
