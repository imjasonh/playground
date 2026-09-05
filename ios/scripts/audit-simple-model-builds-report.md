# Simple-model Army List build audit

Two harnesses simulate a weak on-device model that may use only ids from
`ArmyListStarterPrompt`'s 22-unit palette and one `applyRosterPlan` call:

- `audit-simple-model-builds.py` — one greedy build per faction; checks the
  feasibility gate.
- `stress-simple-model-builds.py` — 840 builds (28 factions × 2 battle sizes ×
  up to 3 themes × 5 weak-model strategies), graded like the stronger model on
  legality, fill, and theme.

Run: `python3 ios/scripts/audit-simple-model-builds.py` and
`python3 ios/scripts/stress-simple-model-builds.py`.

## Stress run: legality by weak-model strategy

| Strategy | accept-all (old) | clamp (shipped) | fill | theme |
|----------|-----------------:|----------------:|-----:|------:|
| `char_first` (well-behaved) | 100% | 100% | 98% | 57% |
| `palette_order` (may skip a Character) | 94% | 94% | 98% | 59% |
| `ignore_max` (over-picks copies) | 2% | 100% | 40% | 63% |
| `overshoot` (blows past the cap) | 7% | 100% | 95% | 58% |
| `theme_pure` (themed only) | 100% | 100% | 62% | 81% |

The two failure-prone behaviors — ignoring copy caps and overshooting points —
are exactly what a small model does, and both were near-total failures under the
old accept-all `applyRosterPlan`. Clamping the plan lifts them to 100% legal with
no prompt cost.

## Top accept-all failure modes (of 840 builds)

| Issue | Count | Fix |
|-------|------:|-----|
| Over copy cap | 1611 unit-picks | `applyRosterPlan` clamp: drop copies past the cap |
| Over points limit | 157 lists | `applyRosterPlan` clamp: skip units that overshoot |
| No Warlord Character | 10 lists | Prompt + builder line: "Include at least one Character" |

## Feasibility failures (gated before the model runs)

| Faction | Why |
|---------|-----|
| `titan-legions` | No detachments; cheapest unit is 1100 pts |
| `chaos-titan-legions` | No detachments; cheapest unit is 1100 pts |

`ArmyListStarterPrompt.buildFeasibilityIssue` blocks these before any model call.

## Fixes shipped (succinct — context budget matters)

1. **`applyRosterPlan` clamps to legality** (primary): drop over-cap copies and
   skip units that would exceed the points limit, then note the trim. A weak
   model's over-picking becomes a legal roster instead of an ILLEGAL apply.
2. **Starter unit table**: all legal `pts@models` sizes + `max` copy count per line.
3. **Detachments filtered to the DP budget** (World Eaters had over-budget picks).
4. **Feasibility gate** before the model runs (titans, no DP fit, no Character).
5. **`applyRosterPlan` Status** includes `N left` remaining points to steer retries.

## Not changed (would bloat prompts / context)

- No theme-token synonym map; catalog keywords don't always match lore terms
  (e.g. Aeldari "aspect"). Theme share stays ~57–81%, acceptable.
- Chat **Fill points** still uses the `addUnit` loop, which already rejects
  illegal copies one at a time — the clamp is only needed for the bulk plan.
