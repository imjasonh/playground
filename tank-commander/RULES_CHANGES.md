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

## How to re-check

```bash
cd tank-commander
cargo run --release -- sim --games 200 --seed 7
cargo run --release -- sim --games 500 --seed 1
```

When you change a rule, append a dated section here with before/after from the
same seed and game count so diffs stay comparable.
