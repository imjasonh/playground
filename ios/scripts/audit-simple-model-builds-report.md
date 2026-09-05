# Simple-model Army List build audit

Three harnesses check whether a weak model, using only our real prompt + tools,
builds good legal lists — and where the tools/prompts fall short.

- `generate-starter-prompts.py` — emits the exact `ArmyListStarterPrompt` text
  the app sends, one per faction, to `/tmp/starter-prompts.json`.
- `execute-and-assess-plans.py` — runs a simple LLM's roster plans through a
  faithful `applyRosterPlan` (with the shipped clamp) + `ArmyListValidator`
  replica, then grades legality, fill %, theme %, and hallucinated ids.
- `stress-simple-model-builds.py` — 840 code-driven builds across strategies, to
  isolate specific failure behaviors.

## LLM-in-the-loop run (the app's real path)

A simple LLM (Gemini 3.6 Flash Minimal, a stand-in for the on-device model —
Claude Haiku isn't available as a subagent model) read each faction's prompt and
chose a roster with its own judgement. We executed those choices through the app
tools and graded them.

| Metric | Before under-fill nudge | After nudge |
|--------|------------------------:|------------:|
| Legal (of 28 buildable) | 28 | 28 |
| Under-filled <90% | 8 | 1 |
| Factions saved by the clamp | 11 | 24 |
| Hallucinated ids | 1 | 0 |

The nudge ("keep adding units until no listed unit fits the points that remain")
made the model fill harder — most factions moved to 95–100% — and the clamp made
that safe: aggressive filling overshoots more often, and every overshoot is
trimmed back to legal. Titan factions correctly never reach the model
(feasibility gate).

## Stress run: legality by weak-model strategy (code-driven)

| Strategy | accept-all (old) | clamp (shipped) |
|----------|-----------------:|----------------:|
| `char_first` (well-behaved) | 100% | 100% |
| `palette_order` (may skip a Character) | 94% | 94% |
| `ignore_max` (over-picks copies) | 2% | 100% |
| `overshoot` (blows past the cap) | 7% | 100% |
| `theme_pure` (themed only) | 100% | 100% |

## Feasibility failures (gated before the model runs)

`titan-legions`, `chaos-titan-legions` — no detachments; cheapest unit is 1100
pts. `ArmyListStarterPrompt.buildFeasibilityIssue` blocks these before any model
call.

## Fixes shipped (succinct — the app calls tools on the model's judgement)

1. **`applyRosterPlan` clamps to legality** (primary): drop over-cap copies and
   skip units that exceed the points cap, then note the trim. Never adds or
   invents units — it only removes the model's illegal picks. 24 factions in the
   LLM run stayed legal because of it.
2. **Under-fill nudge** in the starter prompt (~12 words): tells the model to
   keep adding until nothing fits. Cut under-filled lists from 8 to 1.
3. **Starter unit table**: all legal `pts@models` sizes + `max` copy count per line.
4. **Detachments filtered to the DP budget** (World Eaters had over-budget picks).
5. **Feasibility gate** before the model runs.
6. **`applyRosterPlan` Status** includes `N left` remaining points.

## Remaining gaps (not worth prompt/context cost)

- **Theme share** is low for a few factions (Aeldari 11%, Leagues 18%, Drukhari
  23%) because theme words don't match catalog keywords (e.g. "aspect"). A
  synonym map would bloat every prompt; left as-is.
- **Adepta Sororitas** still under-fills (~86%): expensive themed units plus low
  copy caps leave a gap the model can't close from the 22-unit palette.
- Chat **Fill points** still uses the `addUnit` loop, which already rejects
  illegal copies one at a time.

