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
| `combined` | 2 tanks + 2 APCs + 2 infantry / side | 17×13 open | hard 240 + idle-48 |
| `platoon` | 3v3 tanks | 19×15 open | hard 200 + idle-40 |

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

## 2026-08-30 — Soften infantry cover + range pressure

**Type: Rule**

Stock ranges (unchanged, now intentional pressure):

| Unit | Weapon | Range |
|------|--------|-------|
| Tank | main gun | **5** |
| Infantry | missile | **4** |

A tank can shell a forest hex from outside missile range. Digging in and never
leaving is unsafe.

Cover softens:

1. **Main gun / missiles kill through cover.** No pin save against AT/HE or
   missiles. Forest still gives −1 to hit.
2. **Cover pin is AI-spray only.** APC (and infantry) AI weapons still pin a
   dug-in squad (spend cover + suppress).
3. **Air blast kills through cover** (HE-class).
4. **Revealing fire.** An infantry missile clears `in_cover`.
5. **No stacked dig-in penalty.** Forest −1 only; dig-in no longer adds a
   second −1.
6. **Leaving forest clears cover.** Ending a step in open ground drops dig-in.

**Sim:** infantry AI charges when a tank sits in gun range but outside missile
range (rational reaction to the Rule, not a balance crutch).

**Why.** Covered squads could sit in forest, shrug the first main-gun hit, and
re-dig — a long idle / hard-cap path in 2× combined.

**Effect (80 games, seed 7, 2× combined):**

| Metric | Before (2×) | **After soften** |
|--------|-------------|------------------|
| Decisive | 96% | **100%** |
| Avg activations | ~181 | **~164** |
| Hard timeout | 24% | **8%** |
| Idle stalemate | 12% | **11%** |
| Infantry kills / game | ~2.5 | **~2.8** |
| First-player share | 57% | 66% |
| Red / Blue | 36 / 41 | 38 / 42 |

Games finish more often and a bit sooner. Color stays even. First-player lean
ticked up — addressed next via setup spoil.

---

## 2026-08-30 — Second player may shift scatter terrain

**Type: Scenario**

After initiative, the second player’s spoil expands:

| Scenario | Unit nudges (1 hex each opposing) | Scatter shifts (budget) |
|----------|-----------------------------------|-------------------------|
| Skirmish | no (skewed color on offset starts) | **2** |
| Platoon | yes | **3** |
| Combined | yes | **4** |

**Scatter = forest / mud / rubble** (non-static). Each spend moves one tile by
1 hex onto an Open hex (may land under a unit). Source becomes Open.
**Buildings stay fixed.** Tiles may hop across the budget; a mud/rubble that
lands on a first-player vehicle freezes there. Mirrored scatter may break —
intentional.

**Sim:** placement AI strips FP infantry forest, gifts forest to SP infantry,
and hops mud onto FP vehicles / approaches. Humans choose freely within the
budget.

**Effect (seed 7; skirmish 100 / platoon+combined 80):**

| Scenario | FP share before | **After** | Color |
|----------|-----------------|-----------|-------|
| Skirmish | 62% | **56%** | 52/47 (healthy) |
| Platoon | 60% | **57%** | 41/39 |
| Combined | 66% | **59%** | 46/33 (Red lean) |

Initiative is closer everywhere. Combined still first-player-favored and a bit
Red-heavy after spoil — better than 66%, not solved. Hard timeout on combined
~11%, idle ~16%.

---

## 2026-08-30 — Engine fixes to match documented rules (Bugbot)

**Type: Rule** (engine alignment with upstream / [`rules.md`](rules.md); not new
house rules)

Three places the simulator disagreed with the playable ruleset:

1. **Fire damage.** −1 hull only at the end of the **burning unit’s own**
   activation (was: every unit after every activation).
2. **Cook-off splash.** Destroyed unit → rubble, and every unit within **2
   hexes** takes an automatic HE strength-4 hit (was: destroy + rubble only).
3. **Infantry screen.** Infantry adjacent to a friendly non-destroyed **tank**
   cannot be targeted by main gun, missiles, or AI spray (upstream rule;
   documented in `rules.md` but not enforced).

Disabled cook-off rolls still happen after every activation while the wreck
remains (disabled units cannot activate themselves) — that part was already
correct.

**Effect (seed 1; skirmish 500 / platoon+combined 200) vs prior same seed:**

| Scenario | Decisive | FP share | Avg act. | Hard TO | Idle | Notes |
|----------|----------|----------|----------|---------|------|-------|
| Skirmish | 98%→**95%** | 54%→**54%** | 11→**14** | 6%→**16%** | 0% | Slower fires → longer duels, more hard caps |
| Platoon | 100%→**99%** | 57%→**58%** | 42→**58** | 0% | 0% | Longer, more pens/fires; still clean |
| Combined | 99%→**98%** | 51%→**55%** | 160→**169** | 10%→**16%** | 18%→**24%** | Stall rates worse; infantry screen + slower burns |

Fire ticking only on the burning unit (correct rules) removes a lot of
accidental attrition speed. Cook-off splash adds local drama when wrecks
detonate. Combined’s idle/timeout problem is more visible now, not less.

---

## 2026-08-30 — Rectangular (odd-r) boards instead of axial parallelograms

**Type: Scenario** (map geometry; same scenario coordinates, different playable
shape)

Axial `(q, r)` ranges form a **parallelogram** on the hex lattice. Tabletop mats
are **rectangles**. Boards now use odd-r offset columns×rows (`Hex::offset`);
neighbor / distance math stays axial under the hood.

Same declared sizes (11×9 / 17×13 / 19×15) and the same designer coordinates,
but which edge hexes exist — and therefore approaches / LOS near the rim —
changed. This **does** change sim results.

**Effect (seed 1; 500 / 200 / 200) vs prior axial-parallelogram pass:**

| Scenario | Decisive | FP share | Color (R/B) | Hard TO | Idle |
|----------|----------|----------|-------------|---------|------|
| Skirmish | 95%→**95%** | 54%→**52%** | ~even | 16%→**18%** | 0% |
| Platoon | 99%→**100%** | 58%→**53%** | **139/60 Red** | 0% | 0% |
| Combined | 98%→**96%** | 55%→**46%** | ~even | 16%→**28%** | 24%→**14%** |

Platoon initiative is healthier; color balance broke (Red-heavy). Combined
flipped toward second player and more hard timeouts. Geometry was worth fixing
for fidelity; color bias on platoon needs a follow-up.

---

## 2026-08-30 — Drop plaza funnel; scatter buildings and forest clumps

**Type: Scenario**

Platoon and combined no longer use a sealed midline with a plaza gap. Those
boards are open mats with **random building clumps** and **forest patches**
(mud/rubble stay single tiles). Combined still mirrors scatter east–west.
Skirmish keeps its compact midline block.

Narratively this reads as farmland / copses / farmsteads instead of a
city-block kill funnel.

**Effect (seed 1; 500 / 200 / 200) vs prior rectangular-plaza pass:**

| Scenario | Decisive | FP share | Color | Hard TO | Idle |
|----------|----------|----------|-------|---------|------|
| Skirmish | 95%→**93%** | 52%→**55%** | ~even | 18%→**25%** | 0% |
| Platoon | 100%→**100%** | 53%→**41%** | Red lean | 0% | **1%** |
| Combined | 96%→**98%** | 46%→**47%** | Blue lean | 28%→**24%** | 14%→**10%** |

Platoon flipped to a second-player edge; combined timeouts eased a bit. Still
decisive. Worth iterating on initiative spoil / start symmetry next.

---

## 2026-08-30 — Shared battle mat; skirmish half-width

**Type: Scenario**

Platoon and combined share one **18×12** open mat. Combined keeps east–west
mirrored starts and scatter. Skirmish is **9×12** — half the battle width,
same height — with a compact midline block.

At 2″ flat-to-flat pointy-top hexes: battle mat ≈ 37″ × 21″; skirmish ≈ 19″ ×
21″.

**Effect (seed 1; 500 / 200 / 200):**

| Scenario | Decisive | FP share | Color | Hard TO | Idle |
|----------|----------|----------|-------|---------|------|
| Skirmish | **91%** | **44%** | Blue lean | **17%** | 0% |
| Platoon | **98%** | **51%** | Red lean | 0% | **2%** |
| Combined | **96%** | **52%** | ~even | **23%** | **18%** |

Platoon initiative looks healthy. Combined still times out / idles more than
we'd like — denser map or longer clocks may be next if this size sticks.

---

## 2026-08-30 — Stock field kit (smoke, medkit, lieutenant)

**Type: Rule / Scenario**

Stock tanks always field a **smoke launcher**, **medkit**, and **lieutenant**
(house rule, like stock HE). APCs get smoke. Medkit absorbs the first crew
injury; the LT auto-covers the first killed core role (acts as wounded). Smoke
is once per battle, range 2, and blocks LOS for the rest of the game. The AI
deploys smoke when threatened without a return shot, and covers with the LT
immediately after a kill.

**Effect (seed 1; 400 / 150 / 100) vs pre-kit same mat:**

| Scenario | Decisive | FP share | Smoke /game | Medkit | LT cover | Crew K |
|----------|----------|----------|-------------|--------|----------|--------|
| Skirmish | 91%→**90%** | 44%→**38%** | **1.93** | **1.86** | **0.56** | 1.70→**0.83** |
| Platoon | 98%→**95%** | 51%→**48%** | **5.83** | **5.94** | **2.95** | 8.06→**4.59** |
| Combined | 96%→**93%** | 52%→**43%** | **6.10** | **3.97** | **2.08** | 4.88→**3.03** |

They get used. Crew kills drop hard (medkit + LT). Decisive rate holds.
Skirmish / combined first-player share slipped — worth watching. Combined
timeouts/idles are a bit worse (smoke LOS?).

---

## 2026-08-30 — Full list upgrades (10-pt tanks / 4-pt APCs)

**Type: Rule / Scenario**

Stock scenarios now **list-build**: tanks spend up to 10 points (armor, engine,
extended barrel, optics, anti-infantry, smoke, medkit, lieutenant; Combined
may buy mines). APCs spend up to 4 (armor / engine / smoke). Combined air
strikes remain a scenario grant. HE stays free for stock tanks.

The AI deploys mines on approaches, sprays with tank AI weapons when equipped,
and still uses smoke / LT cover / medkit when those upgrades land.

**Effect (seed 1; 400 / 150 / 100) vs field-kit-only on the same mats:**

| Scenario | Decisive | FP share | Hard TO | Idle | Smoke/g | Medkit | Mines trig |
|----------|----------|----------|---------|------|---------|--------|------------|
| Skirmish | 90%→**84%** | 38%→**54%** | 21%→**67%** | 0% | 1.93→**1.06** | 1.86→**0.94** | — |
| Platoon | 95%→**100%** | 48%→**49%** | 0%→**6%** | ~1% | 5.83→**3.37** | 5.94→**3.26** | — |
| Combined | 93%→**95%** | 43%→**56%** | 32%→**40%** | 24%→**6%** | 6.10→**3.73** | 3.97→**2.20** | **5.62** |

**List mix (vehicles):** soft upgrades land ~55% of the time on skirmish/platoon;
leftover points favor **engine (~88%)** and **armor (~5.8 pts/tank)**. Combined
mines: ~1.2 charges/vehicle at list, **9.3 deployed / 5.6 triggered** per game.

Armor is doing real work — skirmish timeouts jumped because pens land less often
(4.3→3.3 pens/game) and glances stack up. Platoon stays decisive and fun.
Combined idles improved; timeouts and low-engagement are still the soft spots.

---

## 2026-08-30 — Under-spend initiative (skip spoil)

**Type: Rule / Scenario**

You may spend fewer than the list cap. After lists are built, compare each
side’s **total** upgrade points. The side that spent **less** activates first
and there is **no** second-player spoil. Equal totals still roll off and apply
spoil. The simulator picks a random target in `0..=budget` per vehicle so this
tradeoff shows up in Monte Carlo runs.

**Effect (seed 1; 400 / 150 / 100) vs full-list (always aiming at the cap):**

| Scenario | Decisive | FP share | Hard TO | Idle | Under-spend 1st | Avg pts/side | Gap |
|----------|----------|----------|---------|------|-----------------|--------------|-----|
| Skirmish | 84%→**93%** | 54%→**34%** | 67%→**26%** | 0% | **94%** | ~5.1 | 3.4 |
| Platoon | 100%→**96%** | 49%→**37%** | 6%→**1%** | ~1% | **96%** | ~15 | 6.2 |
| Combined | 95%→**94%** | 56%→**48%** | 40%→**32%** | 6%→**13%** | **94%** | ~14 | 4.7 |

Going light almost always wins initiative (~94%), but in skirmish/platoon the
**second** player still wins more games — the points gap (armor/engine) beats
the first-activation edge. Timeouts dropped hard on skirmish because average
lists are thinner (~5 pts/tank vs ~10). Worth watching whether humans game this
into a race to the bottom; if so, floor the target spend or weight toward the
cap in the sim.

---

## 2026-08-30 — Four-stage learning ladder

**Type: Scenario / Rule**

Scenarios are now a ladder:

| Stage | CLI | Force | Lists |
|-------|-----|-------|-------|
| 1 Intro | `skirmish` | 1v1 stock | no |
| 2 Squadron | `squadron` | 3v3 stock | no |
| 3 Platoon | `platoon` | 3v3 | ≤10 pts / tank |
| 4 Combined | `combined` | 2 tank + 2 APC + 2 inf / side | tanks ≤10 (+mines), APC ≤4; air grant |

Under-spend initiative applies only on list stages (3–4). Stock stages always
roll off and apply second-player spoil.

**Balance (seed 1; 400 / 150 / 150 / 100):**

| Stage | Decisive | FP share | Hard TO | Idle | Notes |
|-------|----------|----------|---------|------|-------|
| Skirmish | **92%** | 43% | 17% | 0% | Clean intro; pens 5.3, glances 1.9 |
| Squadron | **98%** | **48%** | **0%** | 3% | Best-balanced stock multi; Red-leaning color |
| Platoon | 96% | **37%** | 1% | 1% | Lists used; under-spend still hurts FP |
| Combined | 94% | 48% | 32% | 13% | Mines/air live; idle + low-eng soft |

**Rules coverage by stage**

| Rule family | Skirmish | Squadron | Platoon | Combined |
|-------------|----------|----------|---------|----------|
| Move / turn / turret / LOS / cover | ✓ | ✓ | ✓ | ✓ |
| AT + HE fire, pen / glance / suppress | ✓ | ✓ | ✓ | ✓ |
| Crew wound / kill / fire / cook-off | ✓ | ✓ | ✓ | ✓ |
| Pass activation (multi-unit) | — | ✓ | ✓ | ✓ |
| Unit + terrain spoil | terrain | ✓ | if lists tie | if lists tie |
| List upgrades + under-spend init | — | — | ✓ | ✓ |
| Smoke / medkit / LT | — | — | ✓ | ✓ |
| APC / infantry / AI spray / air / mines | — | — | — | ✓ |
| APC embark / mount / drop-off | — | — | — | ✓ |

Stock stages teach the core loop without list noise. Platoon is where soft
upgrades fire (~2.5 smoke / medkit per game). Combined is the only stage that
exercises air (**3.9**/g), mines (**4.7** deploy / **3.2** trig), and infantry
kills (**3.1**/g). Soft spots to watch: platoon first-player share under
under-spend, combined timeouts / low engagement, squadron Red color lean.

---

## 2026-08-30 — APC embarkation (interior ride)

**Type: Rule / Sim**

House rules filling in upstream Mount Up for Combined:

1. Each APC carries **one** squad.
2. Infantry **Mount Up** (1 AP) or APC **Embark** (1 AP) from an adjacent hex.
3. Infantry **Dismount** (1 AP, once per activation with Mount) into an adjacent
   empty hex.
4. APC **Drop off** is **free**, once per activation, only after at least one
   **Move**.
5. Embarked infantry share the APC hex, cannot be targeted, cannot fire/step,
   and die if the APC is disabled or destroyed.
6. Exterior tank-top riding is not used.

AI: infantry mount when out of missile range; APCs pick up idle squads, drive
toward the fight, then free-drop (prefer forest).

**Effect (Combined, 200 games, seed 42):**

| Metric | Value |
|--------|-------|
| Games with ≥1 mount/embark | **100%** |
| Mount / Embark / Dismount / Drop per game | 5.1 / 11.3 / 9.5 / 6.7 |
| Passenger kills | 0.04 |
| Decisive / FP share / hard TO / idle | 92% / ~52% / 36% / 13% |

They actually ride. APC Embark is the preferred pickup (~2× Mount). Almost
every load gets a Dismount or Drop. Passenger deaths are rare — the box is
doing its job. Balance vs the pre-embark Combined ladder numbers is in the
same neighborhood (decisive still high; timeouts still the soft spot). No
objectives yet — that is the next lever if you want more reason to cross the
board instead of circling.

---

## 2026-08-30 — Exterior tank riding

**Type: Rule / Sim**

Upstream exterior ride is live: infantry can Mount / be Embarked onto a
friendly **tank** (capacity 1). Shared free Drop off after a Move. Riders
share the tank hex and cannot be targeted, but **any hit** on the tank
(glance, pen, AI spray, mine, air) destroys them immediately.

AI prefers APC interior when both are available; tanks pick up only when they
cannot already shoot; exterior riders dismount aggressively near enemy guns.

**Effect (Combined, 200 games, seed 42) vs APC-only embark:**

| Metric | APC-only | + exterior |
|--------|----------|------------|
| Embark games | 100% | 100% |
| Mount (exterior) / Embark / Drop | 5.1 / 11.3 / 6.7 | 2.7 (**4.0** ext) / 10.0 / 4.7 |
| Passenger kills (exterior) | 0.04 | **1.09 (1.06)** |
| Decisive / hard TO / idle | 92% / 36% / 13% | **95% / 21% / 10%** |

They use the hulls — and pay for it. ~1 exterior wipe per game. Timeouts fell
(more infantry dying in transit / fights resolving). APC interior remains the
safer taxi.

---

## 2026-08-30 — Forest “behind” + APC armor cap (upstream)

**Type: Rule / Sim**

Two fidelity fixes from the Unimplemented list:

1. **Forest:** enemy accuracy −1 when the target is **in** a forest hex **or
   behind** one (any intervening forest on the line of fire). Forest still
   does not block LOS.
2. **APC armor:** list builder caps each facing at **+2** (tanks stay +3).

**Effect (Combined, 200 games, seed 42)** — A/B isolating each change:

| Build | Decisive | Hard TO | Idle | Hit rate | FP wins |
|-------|----------|---------|------|----------|---------|
| Exterior ride baseline (in-forest only, APC +3) | 95% | 21% | 10% | 72% | 93 |
| + forest behind only (APC still +3) | 95% | 24% | 9% | **69%** | 89 |
| + APC +2 only (forest still in-hex) | 95% | 21% | 10% | 72% | 93 |
| Both | 95% | 24% | 9% | **69%** | 89 |

Embark / mount / exterior-wipe rates unchanged (~100% embark games, ~4
exterior mounts, ~1.05 exterior kills).

**Verdict.** Neither moves decisive rate or embark usefulness. Forest behind
shaves a few points off hit rate and nudges timeouts up slightly — real but
small. APC armor cap is a fidelity fix with **no measurable Combined effect**
(4-pt APC budget rarely wanted front +3 anyway).

---

## 2026-08-30 — Stay embarked, deployment mines, tank-only cook-off

**Type: Rule / AI / Sim**

### Why embark was so high

The engine already allowed staying embarked. The AI did not:

1. Loaded vehicles always `DropOff` after ≤2 moves (even mid-map).
2. Embarked infantry always picked a `Dismount` when any hex was legal.
3. Scoring preferred shuttle activations, so the loop remounted forever.

### Fixes

1. **Stay embarked:** APC riders only dismount when within missile reach; exterior
   tank riders still bail near enemy guns (≤6). Vehicles only `DropOff` when
   close to the fight (≤5), not after two moves. Embarked infantry score low so
   they do not burn activations while riding.
2. **Deployment mines:** Combined places all purchased mines **after**
   initiative and **before** spoil. No mid-battle `DeployMine`.
3. **APC no cook-off:** only tanks roll cook-off / immediate fire cook-off.
   APCs at 0 hull are destroyed as wrecks with no ammo splash.

**Effect (Combined, 200 games, seed 42) vs prior exterior+forest+APC-cap build:**

| Metric | Before | After |
|--------|--------|-------|
| Embark / Drop / Dismount /game | 10.1 / 4.7 / 6.9 | **4.2 / 1.7 / 1.2** |
| Exterior mounts / rider kills | 4.0 / 1.05 | **1.9 / 1.23** |
| Cook-offs | ~4.4 | **2.86** |
| Mines deployed / triggered | ~4.8 / 2.8 (mid-battle) | **5.0 / 2.5** (all at setup) |
| Decisive / hard TO / idle | 95% / 24% / 9% | **96% / 21% / 14%** |

Embark still happens in 100% of games, but as a taxi ride, not a shuttle bus.
Cook-offs drop as expected (no APC blasts). Balance holds.

---

## 2026-08-30 — Deployment mine enemy clearance (N = 6)

**Type: Rule / Sim**

Deployment mines may not sit within **6 hexes** of an enemy vehicle (tank or
APC) at placement — `distance < 6` is illegal. Placer reaches midfield and
prefers the forward edge of that envelope so the rule actually shapes the
field.

**Why 6.** Stock gun range is 5. Clearance 6 keeps mines outside the enemy
start’s opening gun envelope while still on the approaches (need a second
move to step on them). A/B Combined (200 games, seed 42):

| Clearance | Decisive | Hard TO | Mines triggered |
|-----------|----------|---------|-----------------|
| 5 | 96% | 22% | **2.56** |
| **6** | **98%** | 26% | 2.31 |
| 7 | 97% | 30% | 2.31 |

5 is a hair more “useful” on triggers; 6 is the better balance (decisive up,
still ~2.3 triggers/game). 7 starts to push fields back and inflate timeouts.

---

## How to add a change

1. Decide **Rule**, **Scenario**, or **Sim**.
2. If balance needs a behavior humans must follow, make it a **Rule** (or
   Scenario setup), implement it in the engine so illegal plays are impossible,
   and document it here.
3. Do **not** rely on AI scoring quirks alone for balance.
