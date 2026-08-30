# Tank Commander simulator — rules and scenario changes

Changes applied in this playground relative to
<https://github.com/imjasonh/tank-commander>.

Every entry is tagged:

| Tag | Meaning |
|-----|---------|
| **Rule** | Changes how humans play. Must hold for any AI or player. |
| **Scenario** | Force composition, map, or mission setup for a named scenario. |
| **Sim** | Simulator-only: AI heuristics, Monte Carlo clocks, metrics. Does **not** change the tabletop rules. Balance must not depend on Sim-only behavior. |

Baseline for older Skirmish numbers: stock tanks, shared heuristic AI, 200
games, seed `7`, unless noted.

---

## 2026-08-30 — Natural 1 always fails, natural 6 always succeeds

**Type: Rule**

On every d6 success check (hit, penetration, glance wound, HE fire start,
cook-off):

- A natural **1** always fails.
- A natural **6** always succeeds.
- Otherwise use the normal target number / `roll + strength > armor` math.

**Why.** Stock AT (6) vs stock armor (6) pens on a roll of 1 (`1+6=7 > 6`),
which erased glances in Skirmish.

**Effect (200 games, seed 7):** glances return (~1.15/game); fights a bit
longer; first-player share unchanged (~57%).

---

## 2026-08-30 — Stock tanks can load HE (no upgrade)

**Type: Rule** (Skirmish stock loadout)

Stock tanks always have HE available. They still start loaded with AT.

**Why.** Without HE there was no path to fire / cook-off drama in Skirmish.

---

## 2026-08-30 — Blocked corridor + random terrain + offset starts

**Type: Scenario** (Skirmish map)

Midline building block, north/south alleys kept clear, random forest/mud/rubble
outside reserved hexes, offset start positions.

**Sim note.** The AI pathfinds when LOS is blocked. That is Sim behavior
implementing the same map humans would navigate.

---

## 2026-08-30 — Glance suppression

**Type: Rule**

A glancing hit suppresses the target (−1 action on its next activation,
minimum 1; does not stack). Clears at the end of that activation.

---

## 2026-08-30 — Multi-unit scenarios

**Type: Scenario**

| Scenario | Force | Board | Sim clock |
|----------|-------|-------|-----------|
| `skirmish` | 1v1 tanks | 11×9 | hard 20 |
| `combined` | tank + APC + infantry / side | 17×13 plaza | hard 160 + idle-32 |
| `platoon` | 3v3 tanks | 19×15 plaza | hard 200 + idle-40 |

**Sim:** activation caps and idle-stalemate stops are analysis clocks so
Monte Carlo games finish. Tabletop turn limits stay with the upstream rules
unless a Scenario explicitly says otherwise.

Timeout ranking (more operational units, then hull) is **Rule** for how a
clock-expired game is scored when you use a clock.

---

## 2026-08-30 — Platoon plaza funnel

**Type: Scenario**

19×15 board, sealed midline with a wide plaza gap and side baffles so tanks
cannot pair off down parallel N/S lanes.

**Sim:** high hard cap + post-contact idle stop so fights can wipe. AI must
check gun range before treating plaza LOS as a shot (bugfix; humans already
know range).

---

## 2026-08-30 — Combined arms: make every piece matter

**Problem.** Combined was a tank-vs-APC duel. Infantry rarely mattered, air
strikes arrived late (or never), and APCs had no job after infantry died.

### Rules

1. **Air strike timing.** The strike arrives at the end of the calling side's
   **next** activation (no delay dice). Blast template: aim hex + all
   adjacent hexes.
2. **Infantry cover.** Stepping into forest puts the squad in cover. The first
   hit against a squad in cover pins them (spend cover, apply suppressed)
   instead of destroying them. A later hit with no cover still kills.
3. **Infantry missiles.** Range 4. Prefer vehicle targets when choosing.
4. **APC spray.** AI weapons may target vehicles: a hit suppresses (no
   penetration / no hull damage). Against infantry, a hit still kills (or
   pins if in cover, per above).

### Scenario

5. **Combined map.** 17×13 plaza funnel (same idea as platoon) with denser
   forest near approaches so infantry have dig-in hexes.

### Sim only (not balance-critical)

- Heuristic AI preferences (when to call air, which missile, when to spray).
- Monte Carlo idle/hard clocks.

### Pass activation (was Sim; now Rule)

Earlier the sim biased the AI away from activating the same APC every time.
That is **not** enough for balance — a human (or a better AI) could still
camp one unit.

**Rule — pass activation.** When you activate, choose one of your operational
units that has **not** yet activated this **pass**. After every operational
unit on your side has activated once, clear the marks and start a new pass.
If only one unit remains, it may activate every time.

This is enforced in the engine (`activatable_ids` / `begin_activation`), not
only in the heuristic scorer.

**Effect (80 games, seed 7, after Rules + Scenario above):** ~100% decisive;
~2 air strikes/game; infantry kills ~1+; more suppressions and maneuver.
Second-player lean remains worth watching.

---

## How to add a change

1. Decide **Rule**, **Scenario**, or **Sim**.
2. If balance needs a behavior humans must follow, make it a **Rule** (or
   Scenario setup), implement it in the engine so illegal plays are impossible,
   and document it here.
3. Do **not** rely on AI scoring quirks alone for balance.
