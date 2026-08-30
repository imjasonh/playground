# Tank Commander — working rules

Playable rules for this playground’s simulator and tabletop experiments.

Upstream source: [imjasonh/tank-commander](https://github.com/imjasonh/tank-commander).
House rules and scenario setups from balance work are folded in below. The
changelog of what changed and why lives in [`RULES_CHANGES.md`](RULES_CHANGES.md).

This is a **stop point**, not a final ruleset. Expect more edits after further
simulation.

Where this file and upstream disagree, **this file wins** for games run with
these house rules.

---

## Introduction

**Tank Commander** is a hex-grid tabletop game. Players take turns activating
units, spending actions to move and shoot. The usual goal is to destroy the
enemy force (or complete a mission).

The battle ends when the mission is complete, a player concedes, or a agreed
turn / activation clock expires (see [Ending the game](#ending-the-game)).

Models used for playtesting are Epic-scale Imperial Guard–style prints (see
upstream for STLs).

---

## Building your tank

### Stock tank

| Armor (F/S/R) | Accuracy | Hull points | Actions | Max move | Main gun |
|---------------|----------|-------------|---------|----------|----------|
| 6/6/6 | 4+ | 4 | 5 | 3 | range 5, AT (and HE — see house rule) |

**House rule — stock HE.** Stock tanks always have High-Explosive rounds
available to load. They still start the battle loaded with AT. The HE upgrade
below is redundant for stock Skirmish / Platoon / Combined as we play them; it
remains for custom / painted builds if you want the upgrade list complete.

### Upgrades (up to 10 points)

Spend up to 10 upgrade points before the game:

- **Armor** (1 per facing, max +3 per facing): raise that facing by 1.
  - Side cannot exceed front; rear cannot exceed side.
  - **Heavy armor:** if any facing took all 3 points, max move −1.
  - **Light armor:** if you bought no armor points, max move +1.
- **Engine** (1): max move +1 (stacks with light armor; can offset heavy).
- **Extended barrel** (1): main-gun range +1.
- **Enhanced optics** (1): accuracy +1 (better target number).
- **High-Explosive rounds** (1): may load HE (already true for stock under the
  house rule above).
- **Anti-infantry weapons** (1): AI weapon, range 2.
- **Smoke launcher** (1): place smoke in a hex within range 2.
- **Medkit** (1): the first crew injury ignores its penalty once.
- **Lieutenant commander** (1): fifth crew member (see Crew).
- **Air support** (2, advanced): one air strike per battle for that tank.
- **Anti-tank mines** (1 each, max 3, advanced): deploy mines.

Painted tanks get +1 upgrade point. An epic name plus named crew gets +1.

### Crew

Four core crew. Once per battle each may use their ability (one ability per
activation):

| Role | Ability |
|------|---------|
| Commander | *Booming Voice* — +2 actions this activation |
| Driver | *Move move move!* — move twice for one action, or three hexes straight |
| Gunner | *Bring it down!* — hit on 2+ this activation |
| Loader | *Quick Load* — loading costs 0 actions this activation |

**Lieutenant commander** (upgrade): may cover a killed role, always acting as
if that role were wounded until the lieutenant is killed.

---

## Dice

Rolls use a d6.

**House rule — natural 1 / natural 6.** On every success check (hit,
penetration, glance wound, HE fire start, cook-off, and similar):

- Natural **1** always fails.
- Natural **6** always succeeds.
- Otherwise use the normal target number or `roll + strength > armor` math.

---

## Initiative and setup

1. Roll off; highest chooses who activates first (or as the scenario says).
2. Apply any **scenario spoil** for the second player (see
   [Scenarios](#scenarios)).
3. First activation begins.

### Pass activation (multi-unit)

**House rule.** When you activate, choose one of your operational units that
has **not** yet activated this **pass**. After every operational unit on your
side has activated once, clear the marks and start a new pass. If only one
unit remains, it may activate every time.

(1v1 Skirmish is just alternating activations; the pass rule matters once a
side has two or more units.)

---

## Activating a unit

On activation, spend the unit’s actions (modified by wounds / suppression).
Typical tank actions:

- **Move** — forward one hex (max move per activation; terrain may cost more
  to leave).
- **Turn** — hull 60° left or right. Turret may turn with the hull or keep its
  absolute facing (relative offset shifts).
- **Rotate turret** — 60° left or right relative to the hull.
- **Load** — load AT or HE (if available).
- **Fire** — fire the loaded main-gun round at a legal target.
- **Fire AI weapon** — if equipped (see Anti-infantry weapons).
- **Deploy smoke** — if equipped.
- **Extinguish fire** — clear *on fire*.
- **Air strike** — if the tank has unused air support (advanced / Combined).

End the activation when you stop spending actions (or have none left). Then
resolve end-of-activation effects (suppression clearing, air-strike arrival
ticks — see below).

---

## Firing the main gun

### Target

Pick a target in range with line of sight to the **turret’s** facing (nearest
hex direction).

LOS is a line between hex centers. It is blocked by buildings, smoke, or
another unit on a hex between shooter and target (endpoints ignored).

Impact facing (front / side / rear) comes from the bearing of the shot relative
to the target’s hull facing.

### Hit and penetration

1. Roll to hit vs accuracy (4+ stock), modified by terrain (−1 if the target is
   in forest). Apply the natural 1 / 6 rule.
2. On a hit, roll d6 and add round strength. If `roll + strength >` armor on
   the impact facing, it is a **penetrating** hit; otherwise a **glancing**
   hit. Natural 1 never pens; natural 6 always pens.

| Round | Strength |
|-------|----------|
| AT | 6 |
| HE | 4 |

### Damage

- **Glance:** wound a random living crew member on 4+.  
  **House rule — glance suppression:** the target is also **Suppressed** (−1
  action on its next activation, minimum 1 action). Does not stack; does not
  refresh if already suppressed. Clears at the end of that next activation.
- **Penetrating hit:** always wound a random living crew member, and −1 hull.
  At 0 hull the unit is **disabled** (no actions; stays on the board).
- **HE fire:** on a glance or pen from HE, roll; on 5+ the target is *on
  fire*. Extinguish with an action. If not extinguished, −1 hull at the end of
  each of that unit’s activations until out or destroyed.
- **Cook-off:** at the end of each activation a disabled non-infantry unit
  remains, roll; on 4+ ammo cooks off — destroyed, replaced with rubble, and
  units within 2 hexes take an HE strength-4 hit. If the last hull point was
  lost to fire, cook-off is immediate.

Infantry are destroyed by any main-gun or missile **hit** (see
[Infantry cover](#infantry-cover)). They do not cook off.

### Wounded crew

| Role | Wounded | Killed |
|------|---------|--------|
| Commander | −1 action | −2 actions |
| Gunner | accuracy −1 | cannot fire |
| Loader | load costs 2 | cannot load (may fire what’s loaded; AI weapons OK) |
| Driver | max move −1 | cannot move or turn |

A second wound on an already-wounded crew member kills them.

---

## Suppression

**House rule — all suppression is temporary.**

Sources that apply **Suppressed**: glancing hits, APC (or infantry) AI spray
vs vehicles, and AI-spray pins vs dug-in infantry.

- −1 action on the unit’s **next** activation (minimum 1).
- Clears at the end of that activation.
- Does not stack or refresh while already suppressed.

**Suppressed infantry cannot fire missiles.** They may still move, take cover,
or use AI weapons against other infantry.

---

## Terrain

| Terrain | Effect |
|---------|--------|
| Open | No effect |
| Mud | 2 actions to leave |
| Rubble | 2 actions to leave |
| Forest | Enemy accuracy −1 vs a unit in the hex |
| Building | Impassable; blocks LOS |
| Hill (advanced) | Behind hill: enemy accuracy −1; on hill: hits use rear armor |
| Mines (advanced) | Entering: AT strength-6 pen check; then remove mine |

Smoke blocks LOS through its hex until the end of the battle (or as the
scenario says).

---

## Infantry

| Armor | Accuracy | Hull | Actions | Max move |
|-------|----------|------|---------|----------|
| 3/3/3 | 4+ | 1 | 3 | 2 |

**Weapons**

| Weapon | Range | Notes |
|--------|-------|-------|
| Missile launcher | **4** (house rule; upstream 3) | AT or HE; no load action; ignores turret arc |
| Anti-infantry (AI) | 2 | Vs infantry |

**Actions:** step (any facing), fire missile, fire AI, take cover, capture
objective, disarm mines, mount / dismount (as upstream).

**House rule vs upstream Take Cover.** Upstream forbids moving or firing while
in cover. Here, dig-in only affects how you take hits (and revealing fire when
you missile). You may still move or shoot while dug in.

Cannot be targeted while adjacent to a friendly tank (upstream rule; keep
unless a scenario says otherwise).

### Infantry cover

**House rules**

1. Ending a **step in forest** puts the squad in cover (`in cover`). Leaving
   forest clears cover. **Take cover** also digs in (open ground included).
2. Forest already gives −1 to hit. Dig-in does **not** stack a second −1.
3. **Main gun, missiles, and air blast kill through cover** — a hit destroys
   the squad (no “pin instead of kill” save).
4. **AI spray** vs a dug-in squad: on a hit, spend cover and apply Suppressed
   (pin) instead of destroying. A later hit with no cover kills.
5. **Revealing fire:** firing a missile clears cover.

Tank main gun range 5 vs missile range 4 is intentional: a tank can shell
forest from outside missile range, so camping cover forever is a losing plan.
Charge into range or die under HE/AT.

---

## Armored personnel carriers (APCs)

| Armor | Accuracy | Hull | Actions | Max move | AI range |
|-------|----------|------|---------|----------|----------|
| 4/4/4 | 4+ | 2 | 3 | 4 | 3 |

4 upgrade points at list-building (armor, engine, smoke — as upstream).

**Actions:** move, turn, fire AI, deploy smoke, extinguish fire.

**House rule — AI spray vs vehicles.** APC (and infantry) AI weapons may
target vehicles. A hit **suppresses** (no pen, no hull damage). Vs infantry, a
hit kills (or pins if in cover, above).

---

## Air strikes

**House rules** (replace upstream delay dice + directional blast walk)

1. Call the strike on a hex (costs an action; once per tank with air support).
2. It arrives at the end of the **calling side’s next activation** (no delay
   roll).
3. **Scatter** on arrival (d6):

   | Roll | Impact |
   |------|--------|
   | 1 | Wild — 2 hexes in a random direction (off-map dissipates) |
   | 2–3 | Drift — 1 hex random (off-map dissipates) |
   | 4–6 | On target |

4. **Blast template:** impact hex **and** all adjacent hexes. Each is hit with
   AT strength 6 (resolve as a main-gun AT hit against units there). Air blast
   **kills infantry through cover**.

Staying under the aim marker is unsafe even after a 1-hex drift; moving off the
template is the counterplay.

---

## Ending the game

- **Wipe:** destroy or disable every enemy unit — that side wins.
- **Concede / mission complete:** as agreed.
- **Clock:** if you use an activation or turn limit and both sides still have
  operational units, score by more operational units, then remaining hull;
  equal is a draw.

Upstream’s default “10 turns” still applies for open tabletop unless the
scenario sets another clock. Simulator Monte Carlo caps are analysis tools, not
required tabletop clocks — see [`RULES_CHANGES.md`](RULES_CHANGES.md).

---

## Scenarios

These are the setups the simulator balances against. Map sizes are hex
**columns × rows** on an odd-r rectangular mat (not an axial parallelogram).

### Skirmish

- **Force:** 1v1 stock tanks (HE available).
- **Board:** 9×12 with a midline building block, clear alleys, random
  forest/mud/rubble outside reserved hexes, offset starts.
- **Second-player spoil:** shift up to **2** scatter terrain tiles (forest /
  mud / rubble) by 1 hex each onto Open hexes before the first activation.
  Buildings stay fixed. No opposing-unit nudge (it skewed color on this map).

### Platoon

- **Force:** 3v3 stock tanks.
- **Board:** 18×12 open mat — scattered **building clumps** and **forest
  patches**, plus single mud/rubble tiles. No sealed midline or plaza funnel.
- **Second-player spoil:** nudge **each** opposing unit up to **1 hex**
  (empty, passable; facing unchanged), then shift up to **3** scatter tiles
  (same rules as below).

### Combined arms

- **Force:** per side — **2 tanks** (each with one air strike), **2 APCs**,
  **2 infantry**.
- **Board:** 18×12 open mat (same size as platoon) with building clumps and
  forest patches; starts and scatter are east–west **mirrored** at generation
  (second-player terrain spoil may break scatter symmetry on purpose).
- **Second-player spoil:** nudge each opposing unit up to 1 hex, then shift up
  to **4** scatter tiles.

### Scatter terrain spoil (shared rules)

- Eligible tiles: **forest, mud, rubble** only — not buildings.
- Each spend: move one tile **1 hex** onto an **Open** hex (may land under a
  unit). Source becomes Open.
- You may hop the same kind of tile across multiple spends; a mud/rubble that
  lands on a first-player **vehicle** should stay there (don’t keep sliding
  it).
- Humans choose freely within the budget; the sim uses a spoiling heuristic.

---

## Missions (upstream ideas, unchanged)

Examples from upstream: Basic Training, Capture Objectives, Breakthrough,
Destroy Target, Escort, Beach Landing, Urban Warfare, Cross Minefield, Disable
AA Guns. Use them with these house rules unless a mission card says otherwise.

---

## Optional / questionable ideas (upstream)

Weather, night fighting, campaigns, hover tanks, and so on remain optional
flavor from upstream — not required for the scenarios above.

---

## Credits

- Upstream design and models: [imjasonh/tank-commander](https://github.com/imjasonh/tank-commander)
- Model bases: [JahnZizka](https://cults3d.com/en/users/JahnZizka/3d-models) on Cults3D
- Hex reference: [Hexgrid](https://hamhambone.github.io/hexgrid/)

---

## Related files

| File | Role |
|------|------|
| [`RULES_CHANGES.md`](RULES_CHANGES.md) | Dated changelog (Rule / Scenario / Sim) with sim metrics |
| [`README.md`](README.md) | How to run the simulator |
