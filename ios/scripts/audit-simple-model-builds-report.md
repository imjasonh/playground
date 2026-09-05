# Simple-model Army List build audit

Simulates a weak on-device model that may only use ids from `ArmyListStarterPrompt`'s
22-unit palette and one `applyRosterPlan` call, then greedily packs points.

Run: `python3 ios/scripts/audit-simple-model-builds.py`

## Expected failures at Incursion (1000 pts)

| Faction | Why |
|---------|-----|
| `titan-legions` | No detachments in catalog; cheapest unit is 1100 pts |
| `chaos-titan-legions` | No detachments; cheapest unit is 1100 pts |

These need a **feasibility gate** before calling the model (implemented in
`ArmyListStarterPrompt.buildFeasibilityIssue`).

## Hard themes (model may under-fill or miss theme)

| Faction | Theme issue |
|---------|-------------|
| `aeldari` | "aspect" rarely appears in datasheet keywords/names |
| `chaos-knights`, `imperial-knights` | Themed palette may top out near ~935 pts |
| `leagues-of-votann` | Narrow theme leaves few matches in top 22 |

## Tool/prompt fixes in PR (succinct)

1. **Starter unit table**: show all legal `pts@models` sizes and `max` copy count per line (helps packing without prose).
2. **`applyRosterPlan` Status**: include `N left` remaining points so retries can adjust.
3. **Feasibility gate**: block starter build when no detachments or cheapest unit exceeds the battle size.
4. **Builder instructions**: reference table columns instead of long examples.

## Not changed (context cost)

- No synonym map for theme tokens (would bloat prompts).
- No second tool for point totals (Status line is enough).
- Chat **Fill points** still uses `addUnit` loop — harder for weak models; separate follow-up.
