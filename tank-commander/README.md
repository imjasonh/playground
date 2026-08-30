# tank-commander

Monte Carlo simulator for the
[Tank Commander](https://github.com/imjasonh/tank-commander) tabletop rules.

v1 covers **Skirmish**: 1v1 stock tanks (AT + HE loadable), a fixed midline
wall with random forest/mud/rubble around it, offset starting rows, core
movement, turret arc, combat, crew wounds, fire, and cook-off. The same
heuristic AI plays both sides so result skew points at the rules (or
first-player bias), not uneven bots. Infantry, APCs, paid upgrades, air
strikes, and missions come later.

## Run

```bash
cd tank-commander
cargo test
cargo run --release -- sim --games 500 --seed 1
cargo run --release -- sim --games 1 --seed 42 --verbose   # event log
cargo run --release -- sim --games 200 --json              # machine-readable
```

## What it measures

Focus for now is **drama** and **stalemates**:

| Signal | Meaning |
|--------|---------|
| pens / glances / fires / cook-offs | How often shots do something cinematic |
| crew wounds / kills / abilities used | Narrative crew arc |
| comebacks | Side that trailed on HP still won |
| timed-out | Hit the 10-turn (20 activation) cap with both tanks fighting |
| low engagement | Few shots relative to activations |
| late stalemate | Long no-hit streak near the end |
| moves / hull turns / turret | Whether tanks maneuver or only duel in place |

The aggregate report ends with **suggested rules tweaks** when those rates
cross simple thresholds.

## Design notes

- **Natural 1 / natural 6.** A roll of 1 always fails and a roll of 6 always
  succeeds on hit, pen, glance-wound, fire, and cook-off checks. See
  [`RULES_CHANGES.md`](RULES_CHANGES.md).
- **Glance suppression.** A non-penetrating hit suppresses the target (−1
  action on its next activation, minimum 1; does not stack). Clears at the end
  of that activation.
- **Turn limit.** The rules say the battle ends after 10 turns. The sim
  treats that as 10 activations per side (20 total).
- **Turret arc.** A target is in arc when the nearest hex facing from shooter
  to target matches the turret facing (60° sector).
- **Hull turn vs turret.** On hull turn, the turret keeps its absolute facing
  (relative offset shifts). That matches "turret may remain in its current
  direction."
- **Skirmish win.** Disable or destroy the enemy. On timeout, higher remaining
  hull points wins; tie is a draw.
- **AI.** When LOS is blocked, pathfind to a firing hex (prefer near the
  enemy, forest cover second). When LOS is open, beam-search shoot / load /
  ability plans. Shared heuristic on both sides.
- **Skirmish map.** A midline building wall blocks the opening street; tanks
  take the north or south alley. Forest, mud, and rubble outside the wall are
  rolled each game. Starts sit on offset rows (`(1,3)` vs `(9,5)`) so each
  side's nearer alley differs.

Rules source of truth remains the upstream README, plus the house rules in
`RULES_CHANGES.md`. Where the text is ambiguous, the sim picks a documented
default rather than blocking.

## Layout

| Path | Role |
|------|------|
| `src/hex.rs` | Axial hex math, facings, LOS line |
| `src/unit.rs` | Tank, crew, armor facings |
| `src/board.rs` | Terrain and smoke |
| `src/combat.rs` | Hit / pen / glance / fire / cook-off |
| `src/action.rs` | Action enum and turn buffs |
| `src/game.rs` | Legal moves and activation loop |
| `src/scenario.rs` | Skirmish setup |
| `src/ai.rs` | Heuristic planner |
| `src/metrics.rs` | Drama / stalemate aggregates + suggestions |
| `src/dice.rs` | Natural 1 fails / natural 6 succeeds |
| `src/sim.rs` | Monte Carlo runner |
| `RULES_CHANGES.md` | House-rule log with sim before/after |
