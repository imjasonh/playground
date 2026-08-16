# Design: Onramp — offline Mac network triage

> **Status: 0.2.0 — renamed from Geek Squad; Playbooks-first.** Directory
> **`onramp/`**, Bundle ID `io.github.imjasonh.onramp`, product name
> **Onramp**. Differentiation is **can’t get online**: chained playbooks rank
> path/DNS/proxy/VPN/hosts/captive causes **without** Apple Intelligence.
> Chat remains optional (macOS 26+ / Apple Intelligence). Deployment target is
> **macOS 14+** so CI can build; chat weak-links FoundationModels.

This is the product we deferred while standing up macOS CD. Foundations now
exist and are proven end-to-end:

- [`hello-macos/`](../hello-macos/) — SwiftUI sample with Sparkle **Check for Updates…**
- [`docs/macos-sparkle-design.md`](macos-sparkle-design.md) — shared macOS app conventions
- [`docs/macos-sparkle-setup.md`](macos-sparkle-setup.md) — Developer ID / notarization / EdDSA secrets
- Live ship: notarized ZIP + appcast with `sparkle:edSignature` (e.g. hello-macos 1.0.7)

**This doc is the diagnostic app plan**: offline playbooks + on-device Foundation
Models tool calling, reusing the existing CD path (same workflows, same secrets,
second appcast).

### Review decisions (locked)

| Topic | Decision |
|-------|----------|
| Name | **Onramp** (`onramp/`) — not “Geek Squad” (Best Buy mark) |
| Sparkle | Reuse as much as possible — **same EdDSA keypair + Fastlane patterns**; two apps are fine (see §7) |
| OS floor | **macOS 14+** for Playbooks + Toolbox; chat needs **macOS 26+** / Apple Intelligence |
| Diagnostics APIs | Prefer **frameworks**; fall back to CLIs when needed |
| Remediation | **Propose fixes**; do **not** apply them automatically |
| Product focus | **Can’t get online** — playbooks primary; once-online help is demoted (search engines win) |
| First useful ship | Playbooks + network Toolbox; chat optional |

---

## 1. Problem & pitch

When someone’s Mac “can’t get online,” the useful answers are usually about
**path, DNS, proxy/VPN, captive portals, and local config** — not the Wi‑Fi
RSSI bars. A good tech asks: Can you resolve names? Which interface is default?
Is a VPN hijacking the route? Are you behind a proxy? Is DNS pointing at
something dead? Did `/etc/hosts` or a profile break you?

**Onramp** is a small, notarized macOS app for that moment: **Playbooks** run a
bounded investigation and return a ranked likely cause plus proposed steps —
fully usable offline for local config, without sending packet captures off-device,
and without changing system state. Optional chat uses an on-device model with the
same read-only tools when Apple Intelligence is available.

### One-liner

> Offline Mac network triage: Can’t-get-online playbooks (+ optional on-device chat),
> shipped via the same Developer ID + Sparkle CD as `hello-macos`.

### Why this, not a Wi‑Fi heat-map

Earlier exploration covered CoreWLAN RSSI/channel surveys. That is useful but
**not v1**. Signal strength does not explain most “I can’t reach the internet”
cases on a laptop that already shows full bars. V1 optimizes for **routing and
configuration**, with optional Wi‑Fi *association identity* (SSID/BSSID if
Location allows) as context — not neighbour scanning or channel planning.

### Why not general Mac helpdesk

Once the user can browse, Activity Monitor + search engines beat a local app for
CPU, disk, crashes, and login items. Onramp keeps those checks under **Advanced**
for chat/toolbox escape hatches, but does not compete there.

---

## 2. Goals & non-goals

### Goals (0.2.0+)

1. **Playbooks first** — Can’t get online (and VPN / DNS / captive / some-sites)
   chain diagnostics and rank causes with **no model required**.
2. **Network Toolbox** — single checks for drilling in after a playbook.
3. **Optional chat** when Apple Intelligence is available — same tools, propose-only.
4. **On-device only for model inference** — no cloud LLM API key.
5. **Propose fixes, don’t apply them** — Settings/UI steps; no autonomous mutations.
6. **Works offline for local-config diagnosis** — stapled build; probes that
   *are* the test still need a path when relevant.
7. **Same CD as hello-macos** — discover → test on PR → notarize + Sparkle on
   `main`.
8. **Degrade gracefully** when Foundation Models are unavailable — Playbooks remain primary.

### Non-goals

- Mac App Store / TestFlight / App Sandbox.
- Cloud LLM fallback.
- Wi‑Fi neighbour survey / channel planner / RSSI ranking.
- Auto-remediation (flush DNS, toggle VPN, rewrite proxies, etc.).
- Enterprise MDM / remote agent / always-on daemon.
- General-purpose “slow Mac” product positioning (demoted).
- Folding into `hello-macos` (keep hello as the tiny CD canary).
- Keeping the “Geek Squad” name.

---

## 3. User experience

### Primary flows

**A. Playbooks (always available — primary)**  
“Can’t get online” runs path → route → DNS → proxy → VPN → hosts → Wi‑Fi →
DNS lookup / TCP / HTTP / captive probes, then ranks causes into the same
structured card as chat (`headline` / `likelyCause` / `evidence` / `proposedSteps`).
Variants: VPN broken, DNS wrong, captive portal, only some sites fail.

**B. Manual Toolbox**  
Network checks first; advanced once-online checks demoted. Each shows a result
pane. “Copy report” exports markdown.

**C. Guided triage (when Foundation Models available)**  
1. Prompt + network scenario chips.
2. Session: streaming text + tool-call cards.
3. Closing **TriageReport**: likely cause, evidence, **proposed** steps.

**D. Menu bar**  
One-click Can’t get online + open main window.

**E. Updates**  
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

### Foundation Models gate (first launch)

| State | UX |
|-------|-----|
| macOS &lt; 26 / framework missing | **Hard block** — full window, no tabs, no workaround |
| `deviceNotEligible` | **Hard block** — hardware/region will never get the model |
| `appleIntelligenceNotEnabled` | Fullscreen setup — primary CTA opens Settings; polls until ready |
| `modelNotReady` | Fullscreen setup — “download in progress”, auto-poll every few seconds |
| Available | Normal Playbooks / Toolbox / Chat |

A small **Playbooks only** escape exists for the offline chicken-and-egg (can’t download while offline); Chat remains blocked until the model is ready.

---

## 4. Architecture

```
┌──────────────────────────────────────────────────────────┐
│  SwiftUI (OnrampApp)                                     │
│  PlaybooksView · ManualToolboxView · ChatView            │
└───────────────┬───────────────────────────┬──────────────┘
                │                           │
                ▼                           ▼
┌───────────────────────────┐   ┌───────────────────────────┐
│  ConnectivityPlaybook     │   │  TriageSession (optional) │
│  Runner + Analyzer        │   │  LanguageModelSession +   │
│  → TriageReport card      │   │  tools[]                  │
└───────────────┬───────────┘   └─────────────┬─────────────┘
                │                               │
                └───────────────┬───────────────┘
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
  **Hard rule for coding agents:** see [`onramp/AGENTS.md`](../onramp/AGENTS.md) —
  tools available to the Onramp agent must never take action, only read
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
| `dns_lookup` | A/AAAA | dig | `dig +short` |
| `dns_trace` | Delegation path from root | dig | `dig +trace` |
| `reachability` | TCP connect host:port | `NWConnection` | — |
| `ping` | ICMP loss / latency (4 packets) | — | `/sbin/ping -c 4` |
| `traceroute` | Path hops | — | `/usr/sbin/traceroute` |
| `http_probe` | Status, redirect, timing, TLS class | `URLSession` | — |
| `proxy_config` | HTTP/HTTPS/SOCKS/PAC | SCDynamicStore | `networksetup -get*proxy` |
| `vpn_interfaces` | utun/ipsec + default-path use | interface enum + path | — |
| `hosts_file` | Surprising `/etc/hosts` lines | file read | — |
| `current_wifi` | SSID/BSSID if allowed | CoreWLAN | — |
| `arp_neighbors` | Local ARP table | — | `arp -an` |

**Deferred:** `wifi_scan` / channel congestion / RSSI ranking; `networkQuality` (slow Apple CDN test).

**Remediation (propose only):** the model/UI may suggest steps such as
“forget Wi‑Fi network”, “disconnect VPN”, “disable HTTP proxy”, “flush DNS
(`dscacheutil -flushcache`)” as **copyable instructions** — never run them.

---

## 6. Repo layout

```
onramp/
├── project.yml                 # platform: macOS (discovery marker)
├── Onramp.entitlements      # Hardened Runtime + Sparkle helpers
├── Sources/
│   ├── OnrampApp.swift
│   ├── SparkleUpdater.swift    # copy/adapt from hello-macos
│   ├── UI/…                    # ManualToolbox + Session
│   ├── Triage/                 # session, prompts, TriageReport
│   ├── Tools/                  # FoundationModels Tool types
│   └── Diagnostics/            # DiagnosticServices (unit-tested)
├── Tests/OnrampTests/
├── fastlane/                   # test + beta (fork of hello-macos)
├── Gemfile
├── README.md
└── .gitignore
```

| Item | Value |
|------|--------|
| Bundle ID | `io.github.imjasonh.onramp` |
| Product / app name | Onramp |
| Sparkle feed | `https://imjasonh.github.io/playground/macos/onramp/appcast.xml` |
| Release tag | `onramp-v<marketing>` |
| Min OS | **macOS 14.0** for Playbooks + Toolbox; **macOS 26+** for chat |

`hello-macos` remains the low-deps CD canary. Onramp is the product app.

---

## 7. Continuous delivery — reuse Sparkle / CD (two apps are fine)

### Short answer

**Sharing Sparkle machinery does not mean only one app.**  
`hello-macos` and `onramp` are two top-level macOS apps. Each gets:

- its own Bundle ID, ZIP, GitHub Release tag, and appcast path
- the **same** CI workflow (`macos.yml`), Fastlane pattern, Developer ID cert,
  notarization secrets, and (for v1) **same EdDSA keypair**

Sparkle ties an install to **one feed URL** baked into that app’s Info.plist.
Two apps ⇒ two feeds (`macos/hello-macos/appcast.xml` and
`macos/onramp/appcast.xml`). They can verify enclosures with the **same
public key** without conflicting.

```
                    ┌─ hello-macos  → gh-pages/macos/hello-macos/appcast.xml
macos.yml / secrets ┤
                    └─ onramp    → gh-pages/macos/onramp/appcast.xml
                         (same SPARKLE_EDDSA_PRIVATE_KEY / SUPublicEDKey)
```

### What already works (no new workflows)

| Piece | Behavior |
|-------|----------|
| `discover-macos-apps.sh` | Any top-level `project.yml` with `platform: macOS` |
| `macos.yml` | Test changed apps on PRs; ship on `main` when secrets exist |
| `macos-ci.sh` | Per app: xcodegen → test → beta → `publish-macos-sparkle.sh` |
| `publish-macos-sparkle.sh` | Generic via `sparkle-metadata.json` (`app`, `feed_path`, …) |

**Expected CI delta: zero workflow YAML edits** if `onramp/fastlane` writes
the same metadata contract as hello-macos.

### Secrets (reuse)

| Secret | Reuse? |
|--------|--------|
| `MACOS_DEVELOPER_ID_*` | Yes |
| `ASC_*` / `APPLE_TEAM_ID` | Yes |
| `SPARKLE_EDDSA_PRIVATE_KEY` | **Yes** — same seed; bake the existing `SUPublicEDKey` into Onramp |

Tradeoff of one shared key: a leak affects every app using it. Fine for this
playground. A later app can mint its own pair if needed.

### Fastlane / Sparkle embedding

Copy from `hello-macos/`: SPM Sparkle, feed/public-key Info keys, entitlement,
nested Sparkle re-sign, `notarytool` + log dump, `sign_update`, metadata with
`app: "onramp"` and `feed_path: "macos/onramp/appcast.xml"`.

Optional later: extract shared Fastlane helpers so the two apps do not drift.
**Copy-paste first**; extract after Onramp ships green.

---

## 8. Testing strategy

| Layer | Where | Notes |
|-------|-------|-------|
| DiagnosticServices + ConnectivityAnalyzer | `OnrampTests` | Fixtures; no live net required in CI |
| Playbooks | Unit tests on snapshot → ranked card | Core of 0.2.0 |
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

### Phase 1 — usable 0.1.x (done)

Scaffold + DiagnosticServices + Chat + Toolbox + Sparkle.

### Phase 2 — Onramp 0.2.0 (this change)

1. Rename Geek Squad → **Onramp** (new bundle ID / Sparkle feed).
2. **Playbooks** primary: Can’t get online + variants; ranked triage card.
3. Toolbox: network-first; demote once-online checks.
4. Chat: network scenario chips; prompts scoped to getting online.
5. Menu bar: Can’t get online playbook.

### Phase 3 — polish (optional)

- Richer streaming / transcript UI, shared Fastlane extract.
- Confirmed-apply actions only if we explicitly revisit “don’t action yet.”

---

## 11. Open questions (remaining)

Most review items are locked above.

1. **Rename migration** — Bundle ID changed (`…geeksquad` → `…onramp`); Sparkle
   will not update old installs. Acceptable for playground; document if anyone
   still runs the old app.
2. **Confirmed-apply remediations** — still deferred; propose-only remains.

---

## 12. Success criteria

- [x] Design matches review decisions (this revision).
- [x] `onramp/` discovered by `macos.yml` with **no** workflow edits.
- [ ] **0.2.0** notarized + appcast `edSignature`; Playbooks usable offline
      for local-config cases.
- [ ] In-app update works on Onramp itself.
- [ ] `hello-macos` continues to ship independently on its own feed.
- [ ] On an Apple Intelligence Mac, guided triage cites real tool evidence
      and only **proposes** fixes.

---

## 13. References

- [`docs/macos-sparkle-design.md`](macos-sparkle-design.md)
- [`docs/macos-sparkle-setup.md`](macos-sparkle-setup.md)
- [`hello-macos/`](../hello-macos/)
- [Foundation Models](https://developer.apple.com/documentation/foundationmodels)
