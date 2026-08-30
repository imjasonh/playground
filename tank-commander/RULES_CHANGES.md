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
- Stock HE or a one-shot ready-rack so fires show up in Skirmish drama stats.
- Upgrade loadout matchups.

---

## How to re-check

```bash
cd tank-commander
cargo run --release -- sim --games 200 --seed 7
cargo run --release -- sim --games 500 --seed 1
```

When you change a rule, append a dated section here with before/after from the
same seed and game count so diffs stay comparable.
