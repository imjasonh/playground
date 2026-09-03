# Design: Army List Builder (Warhammer 40,000, 11th Edition)

> **Status: Phases 0–5 landed for Votann.** Playground experiment under
> `ios/Sources/Experiments/ArmyList/`. Bundled catalog + validator + authoring UI
> + export + on-device Foundation Models chat (tool calls re-validate). More
> factions and richer wargear options are follow-ups.

This document is the implementation plan for a Warhammer 40,000 army list
builder experiment: build lists, validate them against 11th Edition army
construction rules, export/share them, and (later) discuss or edit them with
Apple Intelligence on device.

### Review decisions (proposed)

| Topic | Decision |
|-------|----------|
| Ship shape | Playground **experiment** under `ios/Sources/Experiments/ArmyList/` |
| Bundle ID / signing | Host Bundle ID only. No extension. No re-bootstrap. |
| Rules priority | **Authoring + validation first.** LLM features are blocked until the validator is trustworthy for the shipped catalog. |
| Rules data source | **Bundled construction catalog** generated from [BSData `wh40k-11e-mfm`](https://github.com/BSData/wh40k-11e-mfm) (Munitorum Field Manual scrape) plus keywords/join edges from [BSData `wh40k-11e`](https://github.com/BSData/wh40k-11e). Refresh with `python3 ios/scripts/refresh-army-list-catalog.py`. Wahapedia is fine as a human reference; the machine source of truth is BSData/MFM. |
| Edition | **11th Edition** army construction (Detachment Points, multi-detachment, Leader/Support at list build, enhancement/upgrade limits, Force Disposition). |
| First catalog slice | **Leagues of Votann** only, Incursion (1000 pts) + Strike Force (2000 pts). Expand factions after the validator and UI are solid. |
| LLM | Apple **Foundation Models** (same weak-link pattern as Device Agent / Ride Monitor). Tools edit the list; the validator accepts or rejects every change. |
| Export | Versioned JSON (canonical) + plain-text roster + `ShareLink` / share sheet. |

---

## 1. Problem & pitch

List building in 11th Edition is more combinatorial than 10th: you spend a
**Detachment Points (DP)** budget, can combine detachments with unique-tag
constraints, attach Leaders and Support characters at list construction, and
respect new enhancement / Upgrade limits. A bad list builder that "looks right"
but fails table validation is worse than no builder.

The experiment needs a **deterministic rules engine** with fixtures, then a
SwiftUI authoring UI that never lets an illegal list look legal, then optional
on-device chat that proposes edits through that same engine.

### One-liner

> Build and validate 11th Edition army lists on iPhone; later, chat with them
> using on-device Apple Intelligence that must pass the same validator.

### Why an experiment, not a new app

`ios/AGENTS.md` forbids a second iOS host. This is list authoring + local
validation + Foundation Models, all host-app capabilities. No keyboard, widget,
or Watch companion is required for v1.

---

## 2. Goals & non-goals

### Goals (v1 — authoring & validation)

1. **Domain model** for an army list: faction, battle size, detachments,
   units, options, Leader/Support attachments, enhancements/upgrades, warlord.
2. **Catalog schema** for datasheets, detachments, keywords, points, join
   restrictions, and detachment metadata (DP cost, unique tags, Force
   Disposition).
3. **Validator** that returns structured issues (error vs warning) with stable
   codes and human-readable messages.
4. **Authoring UI** that shows live points, DP spend, and validation state while
   editing.
5. **Persistence** of lists on device (Codable store, like Ride Monitor / Snore
   Log).
6. **Export / share** of a simple, versioned format.
7. **Unit tests** that encode the rules, not just the happy path.

### Goals (v2 — on-device intelligence)

8. Chat over the current list: weaknesses, names, color schemes, freeform talk.
9. Tool-calling that can create or edit a list from a prompt ("1000 pt Votann
   list"), always re-validating after each mutation.
10. Suggested fixes that apply as concrete list edits the user can accept.

### Non-goals

- Scraping or redistributing wahapedia.ru, BattleScribe data, New Recruit
  catalogs, or Games Workshop copyrighted datasheet text.
- Full 40K rules engine for playing games (wound rolls, missions, scoring).
- Offline OCR of physical codexes.
- Cloud LLM backends or API keys.
- Competitive balance advice as authority (chat is opinion; validation is law).
- Every faction at once.

### Legal / data policy

Games Workshop owns the rules, names, and points. This playground experiment
bundles **construction facts only** (points, Detachment Points, unique tags,
join edges, keywords) derived from the public Munitorum Field Manual via the
community [BSData `wh40k-11e-mfm`](https://github.com/BSData/wh40k-11e-mfm)
dataset, with datasheet keywords from [BSData `wh40k-11e`](https://github.com/BSData/wh40k-11e).

1. Refresh the bundled catalog with `python3 ios/scripts/refresh-army-list-catalog.py`.
2. Do **not** paste long copyrighted datasheet or ability text into the catalog.
3. Show an in-app disclaimer: unofficial fan experiment; use official sources
   for tournament play.

Wahapedia is a useful human reference while building features. Prefer BSData/MFM
for machine-readable construction data so refreshes stay reproducible.

---

## 3. 11th Edition army construction (what the validator must know)

These are the construction constraints the engine must encode. Exact numbers
live in the catalog and fixtures; this section is the rule shape.

| Concern | 11th Edition shape |
|---------|--------------------|
| Battle size | Sets points limit, DP budget, enhancement pick limit, duplicate limits. |
| Detachment Points | Spend a DP budget (e.g. 2 at 1000 pts, 3 at 2000 pts). Detachments cost 1–3 DP. |
| Multi-detachment | Multiple detachments allowed if DP budget allows and **unique tags** do not collide. |
| Datasheet duplicates | Default cap (e.g. 3); **Battleline** (and typically Dedicated Transports) get a higher cap. |
| Characters | **Leader** and **Support** attach during list building (not at the table). One Leader + one Support per unit where rules allow. Support characters cannot stand alone. |
| Join graph | Which Leaders/Support may join which units comes from catalog edges (MFM-style). |
| Enhancements | Per battle-size pick limit; one enhancement per unit; **Upgrade** enhancements may apply to non-Character units with special stacking rules. |
| Warlord | Must share the army faction keyword (and other catalog constraints). |
| Force Disposition | Derived from selected detachments; stored on the list for display/export (mission play is out of scope). |
| Epic Heroes / unique characters | Catalog flags enforce uniqueness. |

The validator does **not** need combat rules, stratagems text, or weapon
profiles beyond what construction requires (points, option exclusivity, unit
composition min/max).

---

## 4. Architecture

```
ios/Sources/Experiments/ArmyList/
├── ArmyListExperiment.swift          # launcher registration
├── Models/
│   ├── ArmyList.swift                # saved list document
│   ├── BattleSize.swift
│   ├── DetachmentSelection.swift
│   ├── ListUnit.swift                # instance: datasheet + options + attachments
│   └── ValidationIssue.swift
├── Catalog/
│   ├── CatalogModels.swift           # datasheet, detachment, option definitions
│   ├── CatalogLoader.swift           # load bundled JSON
│   └── Resources/                    # faction packs as JSON (hand-authored)
│       ├── VERSION.json
│       ├── core-battle-sizes.json
│       └── factions/leagues-of-votann.json
├── Validation/
│   ├── ArmyListValidator.swift       # pure: (list, catalog) -> [ValidationIssue]
│   └── Rules/                        # one file per rule family when it grows
├── Store/
│   └── ArmyListStore.swift           # disk persistence
├── Export/
│   ├── ArmyListJSONExporter.swift    # canonical .army.json
│   └── ArmyListTextExporter.swift    # human-readable roster
├── UI/
│   ├── ArmyListHomeView.swift        # library of lists
│   ├── ArmyListEditorView.swift      # authoring surface
│   ├── UnitPickerView.swift
│   ├── DetachmentPickerView.swift
│   ├── ValidationBannerView.swift
│   └── ShareArmyListView.swift
└── Chat/                             # v2 only
    ├── ArmyListChatRuntime.swift     # Foundation Models session + tools
    ├── ArmyListChatTools.swift       # add/remove/set options via validator
    └── ArmyListChatView.swift
```

Tests live under `ios/Tests/PlaygroundTests/` (and optional UI smoke under
`PlaygroundUITests/`), matching other experiments.

### Dependency direction

```
UI ──► Store ──► Models
 UI ──► Validator ◄── Catalog
Chat tools ──► Store mutations ──► Validator
```

The LLM never writes catalog data and never marks a list valid on its own.
After every tool call: apply draft mutation → validate → return issues to the
model and UI.

---

## 5. Domain model (sketch)

### List document

```swift
struct ArmyListDocument: Identifiable, Codable, Equatable {
    var id: UUID
    var name: String
    var catalogVersion: String
    var factionID: String
    var battleSizeID: String          // e.g. "incursion", "strikeForce"
    var detachmentIDs: [String]
    var units: [ListUnitInstance]
    var warlordUnitID: UUID?
    var notes: String
    var updatedAt: Date
}

struct ListUnitInstance: Identifiable, Codable, Equatable {
    var id: UUID
    var datasheetID: String
    var models: Int                   // when variable unit size
    var optionIDs: [String]           // selected wargear / loadout choices
    var enhancementIDs: [String]
    var attachedToUnitID: UUID?       // Leader/Support → bodyguard unit
    var role: CharacterRole?          // leader | support | nil
}
```

### Catalog (JSON-backed)

Enough fields to validate construction:

- Faction: id, name, keywords
- Battle size: points limit, DP budget, enhancement picks, duplicate caps
- Detachment: id, faction, DP cost, unique tags, Force Disposition, which
  enhancements it unlocks
- Datasheet: id, faction, keywords (Battleline, Character, Vehicle, …),
  points (base + per-model or option deltas), min/max models, duplicate group,
  Epic Hero flag
- Join edge: leaderOrSupportID → allowedBodyguardIDs
- Option groups: exclusive / optional / required counts

Keep ability *prose* out of the catalog. Chat can talk in general terms; the
engine only needs construction facts.

### Validation issues

```swift
struct ValidationIssue: Identifiable, Equatable {
    var id: String                    // stable code, e.g. "dp.overBudget"
    var severity: Severity            // error | warning
    var message: String
    var unitID: UUID?                 // optional anchor for UI highlight
}
```

A list is **legal** when it has zero `.error` issues. Warnings (e.g. unused DP)
do not block export, but the UI must show them.

### Core rule checks (v1 checklist)

1. Faction of every unit matches army faction (or explicit ally rules if ever
   added; v1: no allies).
2. Total points ≤ battle size limit.
3. Sum of detachment DP costs ≤ battle size DP budget; each detachment exists
   and belongs to the faction.
4. Detachment unique tags are pairwise disjoint.
5. Datasheet duplicate caps (Battleline / transport exceptions).
6. Unit size within min/max; selected options legal and exclusive groups ok.
7. Character attachment: Support must be attached; Leader/Support join edges
   respected; at most one Leader and one Support per bodyguard unit.
8. Enhancement pick count ≤ battle size limit; one per unit; Upgrade stacking
   rules; detachment eligibility.
9. Warlord present, legal datasheet, faction keyword match.
10. Catalog version on the document matches loaded catalog (or migrates).

Every check gets fixtures: at least one pass and one fail case.

---

## 6. Authoring UI

Follow Apple HIG and existing Playground patterns (`NavigationStack`, system
lists, `ContentUnavailableView`, Dynamic Type, 44 pt targets,
accessibility identifiers = experiment ids + control names).

### Screens

1. **Library** — saved lists, New List, empty state.
2. **New List sheet** — faction (Votann only at first), battle size, name.
3. **Editor** — sticky header with points / DP / legal badge; sections for
   Detachments, Units, Validation.
4. **Add Unit** — searchable datasheet picker with points and keywords.
5. **Unit detail** — model count, options, enhancements, attach Leader/Support.
6. **Share** — export JSON / text, system share sheet.

### UX rules that protect validation

- Illegal actions are disabled **or** allowed as drafts that immediately show
  errors (prefer allow-and-explain so users can fix mid-edit).
- Never hide the validation panel when errors exist.
- Points and DP update on every edit.
- Selecting a second detachment that collides on a unique tag shows the
  collision before save.

### Visual tone

Native SwiftUI. No custom "grimdark dashboard." Faction flavor can appear in
list names and chat themes later; the editor itself stays clear and utilitarian.

---

## 7. Export & share

### Canonical JSON (`.army.json`)

Versioned, pretty-printed, stable key order where practical:

```json
{
  "format": "playground.armyList",
  "formatVersion": 1,
  "catalogVersion": "11e-votann-2026-09-01",
  "name": "Forge-tight 1k",
  "factionID": "leagues-of-votann",
  "battleSizeID": "incursion",
  "detachmentIDs": ["…"],
  "units": [ … ],
  "warlordUnitID": "…",
  "validation": { "errorCount": 0, "warningCount": 1 }
}
```

Import accepts the same schema. On catalog mismatch, import still loads but
revalidates and surfaces migration warnings.

### Plain text

A compact roster for paste into chat apps or printer:

```
Forge-tight 1k — Leagues of Votann — Incursion 1000
Detachments: … (DP 2/2)
Warlord: …
- Unit (points)
…
Total: 990/1000
Status: LEGAL (1 warning)
```

Use `ShareLink` / `UIActivityViewController` for both file and text. No
account, no network upload.

---

## 8. LLM layer (v2, after validation is solid)

Reuse the Device Agent / Ride Monitor approach:

- `#if canImport(FoundationModels)` + `-weak_framework FoundationModels`
- Gate on `SystemLanguageModel.default.availability`
- `LanguageModelSession` with app-defined **tools**

### Tools (mutate through the store + validator)

| Tool | Effect |
|------|--------|
| `getListSummary` | Compact roster + validation issues (token-cheap). |
| `searchCatalog` | Find datasheets/detachments by name/keyword/points. |
| `setBattleSize` / `setDetachments` | Structural edits. |
| `addUnit` / `removeUnit` / `setUnitOptions` | Unit edits. |
| `attachCharacter` / `setWarlord` | Attachment edits. |
| `applySuggestion` | Optional: apply a previously proposed patch object. |

Every mutating tool returns `{ accepted, issues, summary }`. If the draft is
illegal, the model must fix it or ask the user; the UI still shows the draft
with errors.

### Prompt modes (UI chips, not separate models)

- Build from scratch
- Find weaknesses
- Propose fixes (as tool calls)
- Theme (name, color scheme)
- Freeform

System instructions must say: construction facts come only from tool results;
do not invent points or datasheets; thematic advice is clearly opinion.

### What not to do

- Do not paste the entire catalog into the prompt.
- Do not let the model emit a full JSON list that bypasses tools.
- Do not claim tournament legality from chat text alone.

---

## 9. Implementation phases

Ship in small PRs. Each phase must leave `ios.yml` green.

### Phase 0 — Skeleton (no rules claims yet)

- Register `ArmyListExperiment` in `ExperimentCatalog`.
- Empty library UI + disclaimer about unofficial / hand-maintained data.
- Catalog `VERSION.json` + empty Votann file stub.
- Tests: experiment is listed; store round-trips an empty document.

### Phase 1 — Catalog + validator (MOST IMPORTANT)

- Hand-author Votann construction data for a **small but real** subset:
  battle sizes, 2–3 detachments, ~8–15 datasheets including Battleline,
  Leader, Support, one vehicle, enhancements.
- Implement `ArmyListValidator` with the checklist in §5.
- Fixture tests named after rules (`DPOverBudget`, `UniqueTagCollision`,
  `SupportMustAttach`, `BattlelineDuplicateCap`, …).
- No LLM. Minimal UI: debug-only list editor is acceptable if it exercises
  validation.

**Exit criteria:** illegal lists always produce the expected error codes;
legal sample lists (including a 1000 pt sample) validate clean.

### Phase 2 — Authoring UI

- Library, editor, pickers, unit detail, live validation banner.
- Persistence.
- Accessibility identifiers + a UI smoke test if useful.

**Exit criteria:** a human can build the sample 1000 pt Votann list from scratch
on Simulator without looking at JSON.

### Phase 3 — Export / import / share

- JSON + text exporters, share sheet, import from file.
- Tests for encode/decode and validation stamp on export.

### Phase 4 — Expand catalog

- Finish Votann detachments/units needed for normal play.
- Optional second faction only after Votann feels complete.
- Document how a human updates `VERSION.json` when points change.

### Phase 5 — Foundation Models chat

- Chat UI gated like Device Agent.
- Tools from §8.
- Tests for tool executors with a mock list (no model required in CI).
- Manual TestFlight check on an Apple Intelligence device.

### Phase 6 — Polish (optional)

- Suggested-fix buttons from validation codes (deterministic, no LLM).
- Duplicate list, compare two lists' points breakdowns.
- Force Disposition summary on the roster.

---

## 10. Testing strategy

| Layer | What |
|-------|------|
| Catalog loader | Rejects malformed JSON; loads Votann pack. |
| Validator | One fixture file per rule family; golden legal lists. |
| Store | Save / load / delete. |
| Export | JSON round-trip; text contains name, totals, status. |
| Chat tools | Mutating tools call validator; illegal add returns issues. |
| UI | Library empty state; open editor (smoke). |

CI already builds and tests the host app on PRs that touch `ios/`. Keep logic
in plain types so Simulator-less reasoning stays in unit tests.

---

## 11. Risks

| Risk | Mitigation |
|------|------------|
| Rules change often (MFM drops) | Version the catalog; show version in UI and exports; easy JSON edits. |
| Copyright / ToS if scraping | No scrapers. Hand-authored minimal construction data only. |
| Catalog too large for on-device prompts | Tools + search; never dump full faction JSON into the session. |
| LLM invents illegal units | Tools constrained to catalog ids; validator is source of truth. |
| Scope explosion across factions | Hard gate: Votann complete before faction two. |
| 11th Edition nuance wrong | Prefer under-claiming; add warnings when a rule is modeled loosely; fix from fixtures. |

---

## 12. Success metrics (honest)

The experiment is successful when:

1. You can build a 1000 pt Votann list in the UI and trust the legal/illegal
   badge.
2. Export pastes cleanly into Messages / Notes.
3. Chat (when available) can draft a list that ends **legal**, or clearly shows
   what is still wrong.
4. A points update is a catalog JSON edit + test tweak, not an engine rewrite.

If (1) is weak, do not ship (3).

---

## 13. Open questions for the human owner

Resolve these before Phase 1 data authoring gets large:

1. **Faction order after Votann?** (e.g. personal armies only.)
2. **How strict on Upgrade / enhancement edge cases** until an official
   clarification is in hand: error vs warning?
3. **Import compatibility** with any external format (New Recruit, official
   app), or Playground JSON only for v1?
4. **Name** of the experiment in the launcher (working title: **Army List**).

Default if unanswered: Votann-only, strict errors when sure / warnings when
modeling is incomplete, Playground JSON only, launcher title **Army List**.
