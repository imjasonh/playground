# tank-commander

Monte Carlo simulator for the
[Tank Commander](https://github.com/imjasonh/tank-commander) tabletop rules.

Four scenarios share the same engine and heuristic AI — a learning ladder,
plus a Capture flag-raid:

| Scenario | Force | Board | Cap / idle stop |
|----------|-------|-------|-----------------|
| `skirmish` | 1v1 stock tanks (no upgrades) | 9×12 | 20 hard (10/side) |
| `squadron` | 3v3 stock tanks (no upgrades) | 18×12 open | 200 hard; idle after 40 no-hit |
| `platoon` | 3v3 tanks (≤10-pt lists) | 18×12 open | 200 hard; idle after 40 no-hit |
| `combined` | 2 tanks + 2 APCs + 2 infantry / side (lists) | 18×12 open | 240 hard; idle after 48 no-hit |
| `capture` | 1 tank + 3 loaded APCs / side (lists ≤10/≤4 + mines); flag Capture wins | 18×12 open | 200 hard; idle after 40 no-hit |
| `assault` | Attacker 1 tank+3 loaded APCs vs defender 1 tank+2 infantry (lists); Capture or hold | 18×12 open | 180 hard; idle after 50 no-hit (hold = defender) |

Squadron, platoon, combined, capture, and assault share one **18×12** mat with **scattered
building clumps and forest patches** (no sealed midline funnel). Skirmish is
half the width (**9×12**) with a compact midline block. Platoon/Combined/Capture/Assault
tanks spend up to **10** upgrade points (armor, engine, barrel, optics, AI, smoke,
medkit, LT; tanks may buy mines) and may spend fewer; APCs spend up to **4**.
On list scenarios (except Assault), the side with the **lower** total spend activates first and
skips second-player spoil; equal spend still rolls off and applies spoil.
Skirmish/Squadron always roll off and apply spoil. Assault: attacker
always first, defender spoils (list spend does not flip initiative). Combined tanks also get a
scenario air strike, next-activation air strikes (with scatter), and APC
vehicle spray. Combined and Capture starts and scatter are east–west mirrors.

Playable rules (upstream + house rules): [`rules.md`](rules.md).
Dated changelog with Rule / Scenario / Sim tags and sim metrics:
[`RULES_CHANGES.md`](RULES_CHANGES.md).

Printable unit boards (tank whiteboard, APC whiteboard, infantry card):
[`docs/unit-boards.pdf`](docs/unit-boards.pdf). Regenerate with
`python3 scripts/render_unit_boards.py` (needs `reportlab`).

## Run

```bash
cd tank-commander
cargo test
cargo run --release -- sim --scenario skirmish --games 400 --seed 1
cargo run --release -- sim --scenario squadron --games 150 --seed 1
cargo run --release -- sim --scenario platoon --games 150 --seed 1
cargo run --release -- sim --scenario combined --games 100 --seed 1
cargo run --release -- sim --scenario capture --games 100 --seed 1
cargo run --release -- sim --scenario assault --games 100 --seed 1
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
| objectives / win-by-capture | Flag Capture finishes (capture scenario) |

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
- **Map.** Boards are odd-q **flat-top** rectangles (column × row), matching a
  tabletop hex mat — not axial parallelograms. Platoon and combined share an
  **18×12** open mat (building clumps + forest patches). Skirmish is half
  the width (**9×12**) with a compact midline block. Forest/mud/rubble also
  scatter; infantry stepping into forest dig in automatically, and leaving
  forest clears dig-in.
- **Combined arms.** Air strikes arrive at the end of the caller's next
  activation, then scatter (d6: wild 2 / drift 1 / on target) before the
  blast template (impact + neighbors). Tank main gun (range 5) outranges
  infantry missiles (range 4). Main gun, missiles, and air kill through
  cover; only AI spray pins a dug-in squad. Firing a missile leaves cover.
  Forest gives −1 to hit (dig-in does not stack a second −1). AI spray is
  infantry-only (vehicles immune). All suppression is temporary (clears at end of the
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
| `src/hex.rs` | Axial math + odd-q flat-top offset map coords, facings, LOS line |
| `src/unit.rs` | Tank / APC / infantry, crew, armor |
| `src/board.rs` | Rectangular boards, terrain, smoke |
| `src/combat.rs` | Hit / pen / glance / fire / cook-off |
| `src/action.rs` | Action enum and turn buffs |
| `src/game.rs` | Legal moves and activation loop |
| `src/scenario.rs` | Skirmish / squadron / platoon / combined setup |
| `src/ai.rs` | Multi-unit heuristic planner |
| `src/sim.rs` | Monte Carlo runner |
| `src/metrics.rs` | Drama / stalemate aggregates + suggestions |
| `RULES_CHANGES.md` | House rules and measured impact |
