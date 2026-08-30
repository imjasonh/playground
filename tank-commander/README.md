# tank-commander

Monte Carlo simulator for the
[Tank Commander](https://github.com/imjasonh/tank-commander) tabletop rules.

Three scenarios share the same engine and heuristic AI:

| Scenario | Force | Board | Cap / idle stop |
|----------|-------|-------|-----------------|
| `skirmish` | 1v1 stock tanks | 11×9 | 20 hard (10/side) |
| `combined` | 2 tanks + 2 APCs + 2 infantry / side | 17×13 plaza | 240 hard; idle after 48 no-hit |
| `platoon` | 3v3 stock tanks | 19×15 funnel | 200 hard; idle after 40 no-hit |

Platoon and combined seal the midline except a **wide plaza gap** so forces
cannot pair off down parallel lanes. Combined adds forest approaches for
infantry cover, reliable next-activation air strikes (with scatter), and APC
vehicle spray. Combined starts, side baffles, and random terrain are
east–west mirrors. After initiative, the second player may nudge each
opposing unit by up to 1 hex before the first activation.

House rules and scenario setups live in [`RULES_CHANGES.md`](RULES_CHANGES.md).
That file tags each change as **Rule** (humans must follow), **Scenario**
(map/force), or **Sim** (AI / Monte Carlo only).

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
| timed-out | Hit the hard activation cap with both sides still fighting |
| idle-stalemate | Post-contact no-hit drought ended the game |
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
- **Multi-unit activation (Rule).** Each activation you must choose an
  operational unit that has not yet activated this **pass**. When every
  operational unit on your side has activated once, marks clear and a new
  pass starts. Fire actions name a specific target.
- **Turn limit.** Skirmish keeps a short hard cap (20) for Monte Carlo.
  Platoon/combined use a high safety-valve cap and an idle-stalemate stop
  (**Sim** clocks). Tabletop turn limits follow upstream unless a scenario
  says otherwise.
- **Turret arc.** Tanks need the nearest hex facing to match the turret.
  Infantry missiles ignore turret arc; APCs use AI weapons against infantry.
- **Hull turn vs turret.** On hull turn, the turret keeps its absolute facing
  (relative offset shifts).
- **Win.** Disable or destroy every enemy unit. On hard timeout or idle
  stalemate, more operational units wins, then remaining hull; tie is a draw.
- **AI.** When LOS is blocked, pathfind to a firing hex. When LOS is open,
  beam-search shoot / load / ability plans. Infantry prefer missiles and
  cover; APCs hunt infantry; tanks with air support may call a strike.
- **Map.** Skirmish stays on an 11×9 board with a compact midline block.
  Combined uses 17×13 and platoon 19×15, both with a sealed midline and a
  wide plaza gap (plus side baffles) so units funnel into one fight.
  Forest/mud/rubble scatter outside reserved hexes; infantry stepping into
  forest dig in automatically, and leaving forest clears dig-in.
- **Combined arms.** Air strikes arrive at the end of the caller's next
  activation, then scatter (d6: wild 2 / drift 1 / on target) before the
  blast template (impact + neighbors). Tank main gun (range 5) outranges
  infantry missiles (range 4). Main gun, missiles, and air kill through
  cover; only AI spray pins a dug-in squad. Firing a missile leaves cover.
  Forest gives −1 to hit (dig-in does not stack a second −1). APC AI spray
  can suppress vehicles. All suppression is temporary (clears at end of the
  unit's next activation). Suppressed infantry cannot fire missiles.
- **Platoon clock.** Hard cap 200 activations as a safety valve. After
  first contact, 40 activations with no hit ends the game as an idle
  stalemate (scored like a timeout). In practice platoon games wipe before
  either trips.

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
