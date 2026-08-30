# Tank Commander — working rules

Playable rules for this playground’s simulator and tabletop experiments.

Upstream source: [imjasonh/tank-commander](https://github.com/imjasonh/tank-commander).
House rules and scenario setups from balance work are folded in below. The
changelog of what changed and why lives in [`RULES_CHANGES.md`](RULES_CHANGES.md).

This is a **stop point**, not a final ruleset. Expect more edits after further
simulation.

Where this file and upstream disagree, **this file wins** for games run with
these house rules.

**Unimplemented upstream material** is collected loudly in
[Unimplemented upstream](#unimplemented-upstream). If a line there and a house
rule here conflict, the house rule still wins for play — the Unimplemented
section is the fidelity gap list, not an alternate ruleset.

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

**House rule — list building.** **Platoon** and **Combined** tanks spend **up
to 10** upgrade points before the game (you may spend fewer). Combined tanks
may buy **mines**; each Combined tank also gets one air strike as a scenario
grant (does not consume list points). APCs spend **up to 4** points (armor,
engine, smoke). **Skirmish** and **Squadron** use stock tanks with no list.
The simulator picks a random target spend in `0..=budget` per vehicle when
lists apply.

### Upgrades (up to 10 points)

Spend up to 10 upgrade points before the game:

- **Armor** (1 per facing): raise that facing by 1.
  - **Tanks:** max **+3** per facing. Side cannot exceed front; rear cannot
    exceed side. **Heavy armor:** if any facing took all 3 points, max move −1.
    **Light armor:** if you bought no armor points, max move +1.
  - **APCs:** max **+2** per facing (same side ≤ front, rear ≤ side). Heavy
    armor does not apply (cannot reach +3). Light armor still applies if no
    armor points were bought.
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
- **Anti-tank mines** (1 each, max 3, advanced): placed during **deployment**
  (before spoil), not mid-battle. Must be at least **6 hexes** from every
  enemy vehicle at placement.

Painted tanks get +1 upgrade point. An epic name plus named crew gets +1.
(**Not** applied by the simulator list builder — see
[Unimplemented upstream](#unimplemented-upstream).)

### Crew

Four core crew. Once per battle each may use their ability (one ability per
activation):

| Role | Ability |
|------|---------|
| Commander | *Booming Voice* — +2 actions this activation |
| Driver | *Move move move!* — +1 max move this activation (partial; see Unimplemented) |
| Gunner | *Bring it down!* — hit on 2+ this activation |
| Loader | *Quick Load* — loading costs 0 actions this activation |

**Driver ability note.** Upstream allows moving twice for one action **or**
three spaces straight. The simulator currently only grants **+1 max move** for
the activation (see [Unimplemented upstream](#unimplemented-upstream)).

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

1. Build lists when the scenario uses them (Platoon / Combined). Sum each
   side’s total spend. Skirmish and Squadron skip lists.
2. **House rule — under-spend initiative** (list scenarios only). If one side
   spent **fewer** upgrade points than the other, that side activates first and
   there is **no** second-player spoil. If totals are equal — or the scenario
   has no lists — roll off as usual and apply any scenario spoil for the
   second player.
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
- **Embark / drop off** — load or unload infantry (see [Embarkation](#embarkation)).

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
- **Cook-off (tanks only):** at the end of each activation a disabled **tank**
  remains, roll; on 4+ ammo cooks off — destroyed, replaced with rubble, and
  units within 2 hexes take an HE strength-4 hit. If the last hull point was
  lost to fire, cook-off is immediate. **APCs never cook off** — at 0 hull they
  are destroyed as wrecks with no ammo blast.

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
| Forest | Enemy accuracy −1 vs a unit **in** or **behind** a forest (intervening forest on the line of fire; forest does not block LOS) |
| Building | Impassable; blocks LOS. Destroying buildings by fire is unimplemented. |
| Hill (advanced) | Unimplemented in the simulator — tabletop reference only. |
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

**Actions (simulator):** step (any facing), fire missile, fire AI, take cover,
**mount / dismount** (see [Embarkation](#embarkation)), **Capture** on an enemy
flag hex (see [Capture Objective](#capture-objective)).

Upstream also lists **Disarm Mines** — that is **not** in the simulator yet
(see [Unimplemented upstream](#unimplemented-upstream)).

**House rule vs upstream Take Cover.** Upstream forbids moving or firing while
in cover. Here, dig-in only affects how you take hits (and revealing fire when
you missile). You may still move or shoot while dug in.

Cannot be targeted while adjacent to a friendly tank (upstream rule; keep
unless a scenario says otherwise).

### Infantry cover

**House rules**

1. Ending a **step in forest** puts the squad in cover (`in cover`). Leaving
   forest clears cover. **Take cover** also digs in (open ground included).
2. Forest already gives −1 to hit (in or behind). Dig-in does **not** stack a second −1.
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

4 upgrade points at list-building (armor max **+2**/facing, engine, smoke —
as upstream).

**Actions:** move, turn, fire AI, deploy smoke, extinguish fire, **embark /
drop off** (see [Embarkation](#embarkation)).

**House rule — AI spray vs vehicles.** APC (and infantry) AI weapons may
target vehicles. A hit **suppresses** (no pen, no hull damage). Vs infantry, a
hit kills (or pins if in cover, above).

### Embarkation

**House rules** filling in upstream Mount Up (APC interior + tank exterior):

#### Shared

1. **Capacity:** each vehicle carries **one** infantry squad (interior or exterior).
2. **Mount Up** (infantry, 1 action): board an **adjacent** friendly APC or tank
   that has a free seat. Mount **or** dismount at most once per infantry
   activation.
3. **Embark** (vehicle, 1 action): load one **adjacent** friendly infantry
   squad into a free seat (APC or tank).
4. **Dismount** (infantry, 1 action): leave into an **adjacent** empty passable
   hex. Counts as the once-per-activation mount/dismount.
5. **Drop off** (vehicle, **0** actions): unload into an adjacent empty
   passable hex. Once per activation, only after at least one **Move**.
6. **While riding:** the squad shares the vehicle’s hex (does not occupy a
   separate hex). It **cannot be targeted**, cannot fire, and cannot step. It
   may still activate to **Dismount**, or **stay embarked** across activations
   while the vehicle keeps moving. Dig-in / cover clears on mount.

#### APC interior

7. Safer ride. Embarked infantry die if the APC is **disabled or destroyed**
   (including cook-off) — not on a mere glance.

#### Tank exterior (upstream)

8. Ride on the **outside** of a friendly tank.
9. **If the tank takes any hit** (glance, pen, AI spray, mine, air blast —
   anything that counts as a hit), exterior riders are **destroyed**
   immediately.
10. Riders also die if the tank is disabled or destroyed.

**Why bother.** APC move **4** and a hard box beat walking. Tank exterior is
faster repositioning when no APC is free — but one glance wipes the squad, so
dismount before you expect return fire.

### Capture Objective

Upstream:

> **Capture Objective**: Capture an objective. The unit must share the space with the objective to capture it. They don't need to remain on the space to hold it.

**Implemented** for the [Capture (flag raid)](#5-capture-flag-raid) scenario:

1. Each side deploys one **flag** hex in its backline.
2. An unembarked infantry unit that **shares** the **enemy** flag hex may spend
   **1 action** on **Capture**.
3. Capturing the enemy flag **wins immediately**. You do not need to stay on
   the hex afterward.
4. Wipe (no operational enemy units) still wins. Timeout / idle stalemate still
   resolve by attrition.

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

These are the setups the simulator balances against — a short learning ladder
from stock 1v1 up to combined arms. Map sizes are hex **columns × rows** on an
odd-r rectangular mat (not an axial parallelogram).

### 1. Skirmish (intro)

Learn maneuvering and shooting.

- **Force:** 1v1 **stock** tanks (HE free). **No upgrades.**
- **Board:** 9×12 with a midline building block, clear alleys, random
  forest/mud/rubble outside reserved hexes, offset starts.
- **Initiative:** roll off; second player always gets spoil.
- **Second-player spoil:** shift up to **2** scatter terrain tiles (forest /
  mud / rubble) by 1 hex each onto Open hexes before the first activation.
  Buildings stay fixed. No opposing-unit nudge (it skewed color on this map).

### 2. Squadron

Learn pass activation and group tactics.

- **Force:** 3v3 **stock** tanks (HE free). **No upgrades.**
- **Board:** 18×12 open mat — scattered **building clumps** and **forest
  patches**, plus single mud/rubble tiles. No sealed midline or plaza funnel.
- **Initiative:** roll off; second player always gets spoil.
- **Second-player spoil:** nudge **each** opposing unit up to **1 hex**
  (empty, passable; facing unchanged), then shift up to **3** scatter tiles
  (same rules as below).

### 3. Platoon

Same force and board as Squadron, plus list building.

- **Force:** 3v3 tanks with up to 10 upgrade points each (HE free; may spend
  fewer).
- **Board:** same 18×12 open mat as Squadron.
- **Initiative:** under-spend initiative (see above); spoil only when list
  totals tie.
- **Second-player spoil** (tied lists only): nudge **each** opposing unit up
  to **1 hex**, then shift up to **3** scatter tiles.

### 4. Combined arms

Full combined-arms game with lists.

- **Force:** per side — **2 tanks** (10-pt lists + one air strike each; mines
  allowed and placed at **deployment before spoil**), **2 APCs** (4-pt lists),
  **2 infantry**.
- **Board:** 18×12 open mat (same size as squadron/platoon) with building
  clumps and forest patches; starts and scatter are east–west **mirrored** at
  generation (second-player terrain spoil may break scatter symmetry on
  purpose).
- **Initiative:** under-spend initiative; spoil only when list totals tie.
- **Deployment mines:** after lists and initiative, every purchased mine is
  placed on the board **before** spoil. No mid-battle mine deployment. A mine
  must be at least **6 hexes** from every enemy vehicle (tank or APC) at
  placement — outside stock gun range, still on the midfield approaches.
- **Second-player spoil** (tied lists only): nudge each opposing unit up to 1
  hex, then shift up to **4** scatter tiles.

### 5. Capture (flag raid)

Objectives matter: race the other side's flag with embarked infantry.

- **Force:** per side — **1 tank** + **3 APCs**, each APC **pre-loaded** with
  one infantry squad. **No upgrades** (stock).
- **Board:** 18×12 open mat (mirrored starts/scatter like Combined). Each side
  has one **flag** hex in its backline (kept Open).
- **Win:** an infantry unit that **shares** the enemy flag hex may spend 1 AP
  on **Capture**. Capturing the enemy flag wins immediately. Wipe still wins;
  timeout / idle stalemate still resolve by attrition.
- **Initiative:** roll off; second player always gets spoil (nudge + 3 scatter).
- **Embarkation:** squads start inside their APCs; they may stay embarked until
  dropped near the flag (see [Embarkation](#embarkation)).

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
AA Guns. The simulator’s playable ladder is in [Scenarios](#scenarios)
(including **Capture** as a flag-raid variant). Full upstream mission text and
special rules for the rest are in [Unimplemented upstream](#unimplemented-upstream).

---

## Optional / questionable ideas (upstream)

Weather, night fighting, campaigns, hover tanks, and so on remain optional
flavor from upstream — also catalogued under Unimplemented.

---

## Unimplemented upstream

> **Loud fidelity gaps.** Everything below is in
> [imjasonh/tank-commander](https://github.com/imjasonh/tank-commander)
> `README.md` (verbatim quotes) but is **missing**, **partial**, or
> **replaced** in this playground’s rules / engine / AI. Do not treat this
> section as live tabletop rules for the ladder scenarios — use the sections
> above for that. Use this list when deciding what to port next.

Status tags: **missing** (not in engine), **partial** (weaker than upstream),
**replaced** (house rule differs; original text unused).

### Battle length — **replaced**

Upstream:

> The battle is over when the mission is complete, or a player concedes, or after 10 turns of play.

This file uses wipe / concede / mission / optional clocks. Simulator Monte
Carlo caps are analysis tools, not the upstream 10-turn default.

### Painted / named tanks — **missing** (sim)

Upstream:

> Tanks that are painted get an extra upgrade point. Tanks that are given a suitably epic name and have named crew members get an extra upgrade point.

Mentioned above for humans; the list builder never awards these.

### Driver *Move move move!* — **partial**

Upstream:

> _"Move move move!"_: the tank can move twice for one action, or move three spaces straight ahead

Simulator: only `max_move + 1` for that activation. No double-move-for-one-AP
and no three-hex straight special.

### APC armor cap (max +2 / facing) — **implemented**

Upstream:

> **Armor** (1 point per facing, max 2 per facing): Increases the armor of the tank by 1 point.

Live rules / list builder: APC facings max **+2**; tanks remain max **+3**.

### End-of-turn fire / cook-off timing — **replaced**

Upstream:

> If the fire is not extinguished, the tank loses 1 hull point at the end of each turn until the fire is extinguished, or the tank is destroyed.
>
> At the end of every turn a disabled tank is on the table (including the turn it was disabled), roll a die. On a 4+, the ammunition cooks off.

Simulator: fire ticks at the end of **that unit’s activation**; disabled
cook-off rolls after **every** activation on the board. Multi-unit games tick
much faster than upstream’s shared “turn.”

### Forest “behind” cover — **implemented**

Upstream:

> **Forest**: When a tank is in or behind a forest space, enemy accuracy is -1. No movement penalty.

Live rules: −1 when the target hex is Forest, or any intervening hex on the
line of fire is Forest (forest never blocks LOS).

### Destroy buildings by fire — **missing**

Upstream:

> **Building**: Buildings are impassable terrain. Tanks can fire rounds at buildings to turn them into Rubble.

Buildings stay impassable forever in the sim. No “shoot the wall” action.

### Hills — **missing**

Upstream:

> (Advanced) **Hill**: When a tank is immediately behind a hill space, enemy accuracy is -1. When a tank is on a hill space, all hits against it are taken against the rear armor value.

No `Hill` terrain type in the board code. Not placed on any ladder map.

### Take Cover lock — **replaced**

Upstream:

> **Take Cover**: Enemies shooting this unit have -1 accuracy until the next turn. The unit cannot move or fire while in cover.

House rule: dig-in does not forbid move/fire; forest/dig-in interaction is
under [Infantry cover](#infantry-cover).

### Capture Objective — **implemented** (see [Capture Objective](#capture-objective))

Upstream:

> **Capture Objective**: Capture an objective. The unit must share the space with the objective to capture it. They don't need to remain on the space to hold it.

Live rules: flag markers + Capture action on the Capture scenario. Other
upstream missions that need multiple objectives or attacker/defender roles are
still missing (see [Upstream missions](#upstream-missions--missing-as-playable-scenarios)).

### Disarm Mines — **missing**

Upstream:

> **Disarm Mines**: Remove an adjacent mine space from the board.

Mines can be **deployed** and **triggered** by vehicles. Infantry cannot disarm
them.

### Exterior tank-top riding — **implemented** (see [Embarkation](#embarkation))

Upstream:

> **Mount Up / Dismount**: Infantry units can mount or dismount from a tank. They can only mount or dismount once per turn.
> - Infantry can ride on the outside of tanks. If the tank takes any hits while infantry are mounted on the outside, they are destroyed.
> - Infantry can ride inside Armored Personnel Carriers (APCs). See below.

Live rules: exterior tank ride + APC interior under [Embarkation](#embarkation)
(capacity, free drop-off, and APC pick-up Embark are house clarifications —
upstream never defined them).

### Upstream air-strike procedure — **replaced**

Upstream:

> Mark a space anywhere on the board. In the next turn, the player must roll a 6+ for the air strike to hit. On the following turn, it's a 5+, and then 4+, and so on. An air strike is never called on a roll of a 1.
>
> When an air strike is carried out, the marked space is hit with an AT round with a strength of 6. Roll a die to determine the direction of the blast (1 is north, 2 is northeast, and so on). Then roll a die to determine the distance of the blast (1 is 1 space, 2 is 2 spaces, and so on). Each of those spaces are also hit with an AT round with a strength of 6.

Live rules: fixed one-activation delay, scatter table, impact + adjacent blast
— see [Air strikes](#air-strikes).

### Infantry missile range — **replaced**

Upstream:

> Infantry units are equipped with Anti-Infantry Weapons with a range of 2 spaces, and a missile launcher with AT and HE rounds and a range of 3 spaces.

House rule: missile range **4**.

### Upstream missions — **missing** (as playable scenarios)

Upstream:

> - **Basic Training:** One tank driving to spaces and shooting targets, to learn basic rules.
> - **Skirmish:** 1-vs-1 tank battle with light terrain.
> - **Capture Objectives:** Use infantry to capture 1, 2 or 3 spaces on the board.

The simulator’s **Capture** scenario is a 1v1 flag raid (one flag each, instant
win on Capture). Multi-objective cards and the rest of this list remain missing.
> - **Breakthrough:** Move your tank to the other side of the board to win. One player is the attacker, the other is the defender.
> - **Destroy Target:** Destroy a specific target on the board. The target can be a building, a tank, or an infantry unit.
> - **Escort:** Move an infantry squad across the battlefield alive.
> - **Beach Landing:** Attacker/defender where attackers begin in water (as Mud), with defenders guarding 3 objectives on the beach.
> - **Urban Warfare:** Navigate tank columns through a maze of streets to take the town's central plaza.
> - **Cross Minefield:** Navigate across a minefield with infantry disabling mines.
> - **Disable AA Guns:** 3 air strikes available for free, but they fail on 2+ while 3 AA guns are intact. Destroy those guns and call in support.

The simulator’s ladder (`skirmish` / `squadron` / `platoon` / `combined`) is
**not** these cards. Capture / Breakthrough / Escort / Beach / Urban /
Minefield / AA Guns need objectives, attacker–defender roles, or special AA
rules that do not exist in code.

### Optional / questionable ideas — **missing**

Upstream:

> - **Weather:** Roll a die at the beginning of each turn. On a 1, a storm hits. All tanks have -1 accuracy, and all infantry have -1 movement.
> - **Night Fighting:** Accurancy is lowered by 1, visible range is lowered by 3. Tanks can use an action to fire flares to light up 3 spaces around them for both sides.
> - **Campaign Progressions**: Players can keep track of their tanks and crew from battle to battle. Crew members can gain experience, and tanks can be upgraded with new equipment.
> - **Hover Tanks, Walkers, Aliens, etc.**: Add new units to the game with different movement and armor values.

Not in the simulator. Spelling “Accurancy” is upstream’s.

### Upstream prose quirks (not gaps we invented)

Upstream infantry text says “armor value of 2” while the infantry table is
`3/3/3` — we follow the **table**. Upstream also says infantry “can fire at
tanks within 2 spaces” while listing a range-3 missile; we treat the missile
range (house 4) as authoritative.

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
