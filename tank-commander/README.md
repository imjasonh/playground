# tank-commander

Monte Carlo simulator for the
[Tank Commander](https://github.com/imjasonh/tank-commander) tabletop rules.

Three scenarios share the same engine and heuristic AI:

| Scenario | Force | Board | Cap |
|----------|-------|-------|----:|
| `skirmish` | 1v1 stock tanks | 11×9 | 20 (10/side) |
| `combined` | tank (air support) + APC + infantry / side | 15×11 | 48 (24/side) |
| `platoon` | 3v3 stock tanks | 17×13 | 48 (24/side) |

Bigger maps keep a fixed midline wall (plus wing ruins) and roll denser
forest / mud / rubble outside reserved alleys and start hexes.

House rules live in [`RULES_CHANGES.md`](RULES_CHANGES.md).

## Run

```bash
cd tank-commander
cargo test
cargo run --release -- sim --scenario skirmish --games 500 --seed 1
cargo run --release -- sim --scenario platoon --games 200 --seed 1
cargo run --release -- sim --scenario combined --games 200 --seed 1
cargo run --release -- sim --games 1 --seed 42 --verbose   # event log
cargo run --release -- sim --games 200 --json              # machine-readable
```

## What it measures

Focus is **drama** and **stalemates**:

| Signal | Meaning |
|--------|---------|
| pens / glances / fires / cook-offs | How often shots do something cinematic |
| crew wounds / kills / abilities used | Narrative crew arc |
| comebacks | Side that trailed on HP still won |
| timed-out | Hit the activation cap with both sides still fighting |
| low engagement | Few shots relative to activations |
| late stalemate | Long no-hit streak near the end |
| moves / hull turns / turret | Whether units maneuver or only duel in place |
| air strikes / infantry kills | Combined-arms drama (combined scenario) |

The aggregate report ends with **suggested rules tweaks** when those rates
cross simple thresholds.

## Design notes

- **Natural 1 / natural 6.** A roll of 1 always fails and a roll of 6 always
  succeeds on hit, pen, glance-wound, fire, and cook-off checks. See
  [`RULES_CHANGES.md`](RULES_CHANGES.md).
- **Glance suppression.** A non-penetrating hit suppresses the target (−1
  action on its next activation, minimum 1; does not stack). Clears at the end
  of that activation.
- **Multi-unit activation.** Each turn the AI picks one operational unit on
  the active side. Fire actions name a specific target.
- **Turn limit.** The rules say the battle ends after 10 turns. Skirmish maps
  that to 10 activations per side. Platoon and combined raise the budget so
  each unit can still act a few times.
- **Turret arc.** Tanks need the nearest hex facing to match the turret.
  Infantry missiles ignore turret arc; APCs use AI weapons against infantry.
- **Hull turn vs turret.** On hull turn, the turret keeps its absolute facing
  (relative offset shifts).
- **Win.** Disable or destroy every enemy unit. On timeout, higher remaining
  hull points wins; tie is a draw.
- **AI.** When LOS is blocked, pathfind to a firing hex. When LOS is open,
  beam-search shoot / load / ability plans. Infantry prefer missiles and
  cover; APCs hunt infantry; tanks with air support may call a strike.
- **Map.** Skirmish stays on an 11×9 board with a compact midline block.
  Combined uses 15×11 and platoon 17×13: taller midline walls, small wing
  ruins, and more random forest/mud/rubble outside the alleys.

Rules source of truth remains the upstream README, plus the house rules in
`RULES_CHANGES.md`. Where the text is ambiguous, the sim picks a documented
default rather than blocking.

## Layout

| Path | Role |
|------|------|
| `src/hex.rs` | Axial hex math, facings, LOS line |
| `src/unit.rs` | Tank / APC / infantry, crew, armor |
| `src/board.rs` | Terrain and smoke |
| `src/combat.rs` | Hit / pen / glance / fire / cook-off |
| `src/action.rs` | Action enum and turn buffs |
| `src/game.rs` | Legal moves and activation loop |
| `src/scenario.rs` | Skirmish / platoon / combined setup |
| `src/ai.rs` | Multi-unit heuristic planner |
| `src/sim.rs` | Monte Carlo runner |
| `src/metrics.rs` | Drama / stalemate aggregates + suggestions |
| `RULES_CHANGES.md` | House rules and measured impact |
