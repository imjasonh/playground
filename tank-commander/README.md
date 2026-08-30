# tank-commander

Monte Carlo simulator for the
[Tank Commander](https://github.com/imjasonh/tank-commander) tabletop rules.

v1 covers **Skirmish**: 1v1 stock tanks, light terrain, core movement, turret
arc, AT fire, crew wounds, and cook-off. The same heuristic AI plays both
sides so result skew points at the rules (or first-player bias), not uneven
bots. Infantry, APCs, upgrades, air strikes, and missions come later.

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

The aggregate report ends with **suggested rules tweaks** when those rates
cross simple thresholds.

## Design notes

- **Turn limit.** The rules say the battle ends after 10 turns. The sim
  treats that as 10 activations per side (20 total).
- **Turret arc.** A target is in arc when the nearest hex facing from shooter
  to target matches the turret facing (60° sector).
- **Hull turn vs turret.** On hull turn, the turret keeps its absolute facing
  (relative offset shifts). That matches "turret may remain in its current
  direction."
- **Skirmish win.** Disable or destroy the enemy. On timeout, higher remaining
  hull points wins; tie is a draw.
- **AI.** Beam search over legal action sequences with a shared heuristic
  (range band, turret alignment, fire payoff, avoid presenting rear armor,
  extinguish fires). Swappable later for MCTS without changing the rules
  engine.

Rules source of truth remains the upstream README. Where the text is
ambiguous, the sim picks a documented default (see above) rather than
blocking.

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
| `src/sim.rs` | Monte Carlo runner |
