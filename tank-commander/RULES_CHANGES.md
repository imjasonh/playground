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
| `combined` | 2 tanks + 2 APCs + 2 infantry / side | 17×13 plaza | hard 240 + idle-48 |
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

## 2026-08-30 — Air scatter, temporary suppression, pinned missiles

**Type: Rule**

### Air strike scatter

When a called strike arrives, roll d6 for impact:

| Roll | Result |
|------|--------|
| 1 | Wild — impact 2 hexes in a random direction (off-map dissipates) |
| 2–3 | Drift — impact 1 hex in a random direction (off-map dissipates) |
| 4–6 | On target |

Blast template is still **impact hex + all adjacent hexes**. A 1-hex drift
almost always still clips the original aim hex, so the strike remains useful
as area denial: staying put under the aim marker is unsafe; moving away is the
counterplay.

### All suppression is temporary

Glance, APC spray, cover pin, and air pin share one **Suppressed** status:
−1 action (minimum 1) on the unit's next activation, then it clears at the end
of that activation. Does not stack; a hit on an already-suppressed unit does
not refresh the duration. APC spray is not a permanent soft-lock.

### Suppressed infantry cannot fire missiles

While Suppressed, infantry legal actions omit missile shots (they may still
move, take cover, or use AI fire against other infantry).

**Why.** Combined still had a second-player lean and idle droughts. Scatter
softens free reactive air without deleting the denial tool; temporary
suppression + no missiles while pinned stops spray/pin loops from freezing the
plaza.

**Effect (80 combined / 200 skirmish / 80 platoon, seed 7):**

| Scenario | Decisive | 1st-player share | Idle stalemate | Notes |
|----------|----------|------------------|----------------|-------|
| Skirmish | 99% (unchanged) | 57% | 0% | No combined-only rules; regression clean |
| Platoon | 100% (unchanged) | 60% | 0% | Same |
| Combined | 96% (was 94%) | **29%** (was 36%) | 19% (was 20%) | ~2 air strikes/game still; suppressions down slightly; infantry kills ~1.1 |

Scatter keeps air in the game as denial, but the second-player lean got a bit
worse — first player's strike is less of a reliable opener, while the
responder still gets the last look. Idle droughts barely moved. Next lever is
still initiative / placement fairness (suggestion 4), not more Sim tweaks.

---

## 2026-08-30 — Second-player opposing-force nudge (combined)

**Type: Scenario** (combined only)

After initiative is rolled, the **second player** may move **each** opposing
unit up to **1 hex** (empty, passable, on-board; facing unchanged) before the
first activation.

**Intent note.** The earlier sketch was “second places a terrain baffle / nudges
*their own* start.” This experiment is the user’s sharper variant: second moves
*some of the opposing force*. The sim’s placement AI picks, per unit, the legal
hex that most spoils the opener (farther from second-player units, farther from
the plaza, strip infantry out of forest when possible). Humans would choose
freely within the 1-hex cap.

**Effect (80 combined, seed 7, vs prior combined):**

| Metric | Before | After nudge |
|--------|--------|-------------|
| Decisive | 96% | 94% |
| First-player share | 29% | **43%** |
| Idle stalemate | 19% | **14%** |
| Air strikes / game | ~2.0 | ~2.0 |

Surprising but useful: giving the second player a spoiling nudge *improved*
initiative balance. Likely because it delays the first-player rush into the
plaza kill zone that the responder was punishing. Color balance is still off
(Blue wins more games than Red regardless of who goes first) — map start
asymmetry is the next thing to look at.

---

## 2026-08-30 — Mirror combined map (skeleton, then scatter)

**Type: Scenario** (combined only)

### 1. Mirror starts + constant wall/baffles

Blue starts are the east–west mirrors of Red. Side baffles are mirrored pairs
(no more north-vs-south asymmetric stubs).

**Effect (80 games, seed 7, after nudge + skeleton mirror only):** first-player
share ~46%; color flipped to Red-heavy (53/27). Asymmetry moved into random
scatter.

### 2. Mirror random terrain

Scatter forest/mud/rubble only on the west half, then copy each tile to its
east–west mirror (counts are per-half so total density stays similar).

**Effect (80 games, seed 7, after 1+2):**

| Metric | After nudge only | + skeleton mirror | + mirrored scatter |
|--------|------------------|-------------------|--------------------|
| Decisive | 94% | 100% | **98%** |
| First-player share | 43% | 46% | **53%** |
| Red / Blue wins | 24 / 51 | 53 / 27 | **42 / 36** |
| Idle stalemate | 14% | 19% | 24% |

Color and initiative look healthy. Idle droughts ticked up — leave suggestion
3 alone for now; revisit if idle stays high across seeds.

---

## 2026-08-30 — Combined force: 2 of everything

**Type: Scenario** (combined only)

Each side fields **2 tanks** (each with one air strike), **2 APCs**, and
**2 infantry**. Starts remain east–west mirrors on the same 17×13 plaza.
Sim clocks raised to hard **240** / idle **48** so six-unit sides have room
to finish (Sim clocks; tabletop turn limits stay upstream unless adopted).

**Effect (80 games, seed 7, vs prior 1-of-each combined):**

| Metric | 1× force | **2× force** |
|--------|----------|--------------|
| Decisive | 98% | 96% |
| First-player share | 53% | **57%** |
| Red / Blue wins | 42 / 36 | 36 / 41 |
| Idle stalemate | 24% | **12%** |
| Hard timeout | 4% | **24%** |
| Air strikes / game | ~2.0 | ~3.9 |
| Infantry kills / game | ~0.9 | ~2.5 |

Doubling the force cuts the “one squad in cover stalls forever” idle pattern
roughly in half and makes combined feel busier (more air, more infantry
kills, more maneuver). Color stays close. Tradeoff: more games hit the hard
cap still fighting — wipe rates didn’t improve. First-player lean is mild.

---

## How to add a change

1. Decide **Rule**, **Scenario**, or **Sim**.
2. If balance needs a behavior humans must follow, make it a **Rule** (or
   Scenario setup), implement it in the engine so illegal plays are impossible,
   and document it here.
3. Do **not** rely on AI scoring quirks alone for balance.
