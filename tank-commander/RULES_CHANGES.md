# Tank Commander simulator — rules changes

House rules and clarifications applied in this playground sim, relative to the
upstream rules at <https://github.com/imjasonh/tank-commander>. Each entry
notes why it landed and what the Monte Carlo runs showed.

Baseline scenario for numbers below: Skirmish, stock tanks (armor 6/6/6, AT
strength 6, accuracy 4+), shared heuristic AI, 200 games, seed `7`, unless
noted.

---

## 2026-08-30 — Natural 1 always fails, natural 6 always succeeds

**Rule.** On every d6 success check in the sim (hit, penetration, glance
wound, HE fire start, cook-off):

- A natural **1** always fails.
- A natural **6** always succeeds.
- Otherwise use the normal target number / `roll + strength > armor` math.

Implemented in `src/dice.rs` and used from `src/combat.rs`.

**Why.** Upstream, stock AT (strength 6) vs stock armor 6 pens on every hit:
even a roll of 1 gives `1+6=7 > 6`. That erased glancing hits from Skirmish
and made every connect a hull-damage event.

**Effect on balance (same 200-game / seed 7 batch):**

| Metric | Before | After | Delta |
|--------|-------:|------:|------:|
| Red / Blue / Draw | 105 / 93 / 2 | 113 / 85 / 2 | slight Red drift |
| First-player win share | 57% (113/198) | 57% (113/198) | unchanged |
| Avg activations | 7.4 | 9.0 | +1.6 (~22% longer) |
| Timed out | 4 (2%) | 8 (4%) | still rare |
| Avg shots | 12.8 | 14.8 | more trading |
| Hit rate | 44% | 44% | unchanged* |
| Avg pens | 5.63 | 5.42 | slightly fewer |
| Avg glances | **0.00** | **1.15** | glances return |
| Avg crew wounds / kills | 4.37 / 1.26 | 4.50 / 1.52 | similar |
| Comebacks | 97 | 87 | still common |
| Auto suggestions | "too fast" + "never glances" | none (thresholds clear) | healthier |

\*Hit rate is unchanged because stock accuracy is already 4+: a natural 1
already missed and a natural 6 already hit. The meaningful change is
**penetration** (and the same floor/ceiling on wound / fire / cook-off, which
were already 4+ or 5+ so their rates barely move).

**Larger batch check (500 games, seed 1, after only):** still ~99% decisive,
~8.9 activations, ~1.12 glances/game, first-player share ~57%, no stalemate
flags. Side bias (Red vs Blue) is mostly start-position / first-player
coupling, not a rules asymmetry.

**Verdict.** This is a good keep. Glances come back (~1 per game), fights run
a bit longer without tipping into timeouts or low engagement, and the
railroad / "never glance" warnings clear. First-player edge is unchanged and
still worth watching when we add upgrades or missions.

**Open follow-ups (not applied yet):**

- Soften first-player bias (simultaneous activation, or defender places after
  initiative).
- Upgrade loadout matchups.
- Tune the AI's HE appetite if table players load HE less often than ~75%.

---

## 2026-08-30 — Stock tanks can load HE (no upgrade)

**Rule.** Skirmish stock tanks always have HE available. They still start
loaded with AT; `Load` may choose AT or HE. The old 1-point "High-Explosive
Rounds" upgrade is not spent in this scenario (upgrade economy comes later).

**Why.** After the 1/6 house rule, drama looked healthy except fires stayed
at 0.00 — Skirmish had no path to the fire / cook-off narrative without HE.

**Effect on balance (200 games, seed 7; baseline = post-1/6 house rule):**

| Metric | Before (1/6 only) | After (+ stock HE) | Delta |
|--------|------------------:|-------------------:|------:|
| Red / Blue / Draw | 113 / 85 / 2 | 103 / 95 / 2 | sides closer |
| First-player win share | 57% | 57% | unchanged |
| Avg activations | 9.0 | 9.3 | +0.3 |
| Timed out | 4% | 5% | still rare |
| Avg shots (AT / HE) | 14.8 (all AT) | 13.1 (3.1 / **10.0**) | HE-heavy mix |
| Hit rate | 44% | 44% | unchanged |
| Avg pens | 5.42 | 4.04 | fewer hull punches |
| Avg glances | 1.15 | 1.67 | more soft hits |
| Avg fires | **0.00** | **1.35** | cinema unlocked |
| Avg cook-offs | 0.47 | 0.65 | slightly up |
| Avg crew wounds / kills | 4.50 / 1.52 | 3.78 / 1.09 | gentler |
| Comebacks | 87 | 91 | still common |

**Larger batch (500 games, seed 1):** ~1.43 fires/game, ~9.9 HE shots vs
~3.2 AT, 4% timeouts, first-player share still ~58%, no stalemate flags.

**Verdict.** Keep. Fires land about once per game, pens soften without
killing decisiveness, and Red/Blue drifted toward even. First-player edge
is untouched. Caveat: the heuristic AI loads HE for ~75% of shots — higher
than many humans might — so treat fire rates as an upper bound until a
human playtest or a less HE-hungry policy.

---

## 2026-08-30 — Blocked corridor skirmish map

**Change.** The open east-west street between the tanks is closed with a 3×3
building wall on the midline (`q=4..6`, `r=3..5`). North and south alleys
remain open; forests sit on the alley mouths. Opening LOS is blocked — tanks
must move to find each other.

Also fixed two sim bugs that only showed up once flanks mattered:

- `Facing::turn_left` from East wrapped to West (u8 underflow).
- `facing_toward` mapped pixel angles onto the Facing enum in the wrong
  order (NE and SE swapped, etc.).
- Turret "left" stepped the offset the wrong way relative to hull left.

The AI now pathfinds to a firing hex when LOS is blocked, and aims/loads/fires
when geometric LOS exists.

**Why.** On the old open map, after a short close the game was mostly
Load→Fire→Load. Move was ~16% of actions. Terrain rarely forced a choice.

**Effect on balance (200 games, seed 7; baseline = stock HE on the open map):**

| Metric | Before (open) | After (walled) | Delta |
|--------|--------------:|---------------:|------:|
| Red / Blue / Draw | 103 / 95 / 2 | 61 / 135 / 4 | Blue-heavy |
| First-player win share | 57% | ~50% (99/196) | FP edge gone |
| Avg activations | 9.3 | 11.2 | +1.9 |
| Timed out | 5% | 6% | similar |
| Avg shots (AT / HE) | 13.1 (3.1 / 10.0) | 11.9 (3.7 / 8.2) | similar mix |
| Avg moves / hull turns | *(not tracked)* | **9.2 / 7.3** | real maneuver |
| Avg pens / glances | 4.04 / 1.67 | 3.79 / 1.86 | similar |
| Avg fires | 1.35 | 1.30 | similar |
| Comebacks | 91 | 59 | fewer |
| Late stalemates | 0 | 3 (2%) | rare |

**Verdict.** Keep the wall for option diversity — games now open with a
flanking choice instead of a staring contest. Side balance drifted Blue; next
pass should either offset starting rows, thin the wall, or add a reason to
contest one alley (objective / VP). First-player edge collapsing is a happy
accident of the approach race.

**Better layout ideas (not shipped yet):**

1. **One alley, not two** — a single gap forces contact; two alleys let tanks
   miss each other until late.
2. **Offset starts** — Red on `(1,3)`, Blue on `(9,5)` so the "natural" approach
   lanes differ and one side doesn't own a mirror.
3. **Objective hex** past the wall — VP for ending activation on it, so
   sitting back loses even if the duel is cautious.

---

## 2026-08-30 — Random terrain around the wall

**Change.** The 3×3 midline wall stays fixed. Forest (5–9), mud (2–4), and
rubble (1–3) hexes are scattered at random each game. Alley columns and the
hex in front of each tank stay clear; boards that somehow seal an alley are
re-rolled.

**Why.** Fixed forests made every game the same approach puzzle. Random cover
and footing should vary which alley is attractive and cut the Blue-heavy skew
from the fixed map (61 / 135).

**Effect on balance (200 games, seed 7; baseline = fixed forests/mud):**

| Metric | Fixed terrain | Random scatter | Delta |
|--------|--------------:|---------------:|------:|
| Red / Blue / Draw | 61 / 135 / 4 | **92 / 103 / 5** | sides much closer |
| First-player win share | ~50% | ~52% (101/195) | similar |
| Avg activations | 11.2 | 11.5 | similar |
| Timed out | 6% | 9% | slight up |
| Avg moves / hull turns | 9.2 / 7.3 | 8.7 / 6.7 | still maneuvering |
| Avg fires | 1.30 | 1.14 | similar |
| Comebacks | 59 | 78 | up |

**Larger batch (500 games, seed 1):** Red 207 / Blue 286 — still a Blue lean,
but far better than the fixed-map blowout.

**Verdict.** Keep. Same wall, different ground each game, and Red/Blue stopped
looking like a coin with Blue painted on both sides.

---

## 2026-08-30 — Offset starting rows

**Change.** Red starts at `(1,3)` facing east; Blue at `(9,5)` facing west
(was both on `r=4`). The wall and random scatter are unchanged.

**Why.** Even with random terrain, mirrored row starts let one side's "drive
north" habit win too often. Offset rows make each tank's nearer alley
different from turn one — a cheap asymmetry that doesn't add rules text.

**Effect on balance (200 games, seed 7; baseline = random terrain, same row):**

| Metric | Same row | Offset rows | Delta |
|--------|---------:|------------:|------:|
| Red / Blue / Draw | 92 / 103 / 5 | 110 / 88 / 2 | Red slightly up |
| First-player win share | 52% | 62% (122/198) | noisier at N=200 |
| Avg activations | 11.5 | 10.4 | slightly snappier |
| Timed out | 9% | 5% | down |
| Avg moves / hull turns | 8.7 / 6.7 | 8.2 / 5.4 | still real maneuver |
| Avg fires | 1.14 | 1.14 | unchanged |

**Larger batch (500 games, seed 1):** Red **251** / Blue **239** / Draw 10 —
near even. First-player share ~58% (285/490). Timeouts 6%. Drama (fires,
pens, comebacks) holds.

**Verdict.** Keep. Side balance is finally close on a big batch, games resolve
a bit faster, and the opening decision (which alley?) is no longer the same
puzzle for both players.

---

## 2026-08-30 — Glance suppression

**Rule.** When a shot hits but does not penetrate, the target becomes
**Suppressed** until the end of its next activation: **−1 action** that
activation (minimum 1). A second glance while already Suppressed does nothing
extra. The token clears when that activation ends.

**Why.** Mid-fight was Load→Fire→Load with glances often feeling like soft
misses (wound roll fails ≈ half the time). Suppression makes every glance
shake the crew without racing hull damage, and gives the shooter a short
tempo window.

**Effect on balance (200 games, seed 7; baseline = offset starts + random
terrain):**

| Metric | Before | After (+ suppression) | Delta |
|--------|-------:|----------------------:|------:|
| Red / Blue / Draw | 110 / 88 / 2 | 110 / 86 / 4 | similar |
| First-player win share | 62% | 57% (111/196) | slightly fairer |
| Avg activations | 10.4 | 10.4 | unchanged |
| Timed out | 5% | 6% | similar |
| Avg glances | 1.49 | 1.48 | — |
| Avg suppressions | 0 | **1.40** | almost every glance sticks |
| Avg pens / fires | 4.09 / 1.14 | 4.00 / 1.18 | drama holds |
| Comebacks | 72 | 75 | similar |

**Larger batch (500 games, seed 1):** Red 248 / Blue 239 / Draw 13. First-player
share ~56% (274/487). Avg **1.33 suppressions** / **1.41 glances**. Comebacks
173. Timeouts 7%. Decisive 97%.

**Verdict.** Keep. Glances now do something every time (~94% apply a fresh
token; the rest were already suppressed). Side balance and cinema stay healthy;
first-player edge eased a little. Worth a human playtest to confirm the −1
action feels like a punch, not a bookkeeping tax.

---

## How to re-check

```bash
cd tank-commander
cargo run --release -- sim --games 200 --seed 7
cargo run --release -- sim --games 500 --seed 1
```

When you change a rule, append a dated section here with before/after from the
same seed and game count so diffs stay comparable.
