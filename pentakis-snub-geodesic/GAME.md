# PENTAKIS — a real-time strategy board game on a geodesic globe

**Rules version 0.3** (see §9 for the playtest changelog).

A 2–4 player RTS played on the physical frequency-2 spherical pentakis snub
dodecahedron in this directory: harvest energy from the globe's 12 wells,
train squads, push supply lines around the planet, and storm the enemy
capital — all in real time, paced by sand timers instead of turns.

- **Players:** 2–4
- **Time:** 15–18 minutes of live play (6 pulses × 3 min, hard cap), ~25–30
  minutes with setup; the turn-based variant runs 45–60 minutes
- **Elevator pitch:** StarCraft's macro loop (harvest → build → army → attack)
  compressed onto a 9-inch globe you physically rotate, with sand-timer
  cooldowns instead of APM.

---

## 1. Why this shape is a good map

The mesh (282 vertices, 840 edges, 560 triangles) has exactly the structure a
strategy map wants:

| Node class | Count | Valence | Game role |
|---|---|---|---|
| **Wells** (raised pentagon apexes) | 12 | 5 | Resource nodes + capitals. Spread with icosahedral symmetry — maximally even coverage of the globe. |
| **Ridges** (original snub-dodecahedron vertices) | 60 | 6 | High ground; the only other nodes you can build on. |
| **Fields** (subdivision midpoints) | 210 | 6 | Open terrain for movement and battles. |

Measured well-to-well graph distances (hops along edges): from any well, 5
other wells are **6 hops** away, 5 are **10 hops**, and the antipodal well is
**14 hops**. That gives natural fair starts:

- **2 players:** antipodal wells (14 hops apart). Note the 12 wells then split
  into two "home clusters" of 6 — this is why the 2-player domination
  threshold is 7, not 6 (§6).
- **3 players:** any of 20 triples of wells that are pairwise 10 hops apart.
- **4 players:** a "golden rectangle" set of 4 wells where *every* player sees
  the same distance profile to the others: one rival at 6, one at 10, one at
  14 hops.

Units occupy **nodes** and move along **edges**. The triangles are just the
planet's skin (and look great printed).

## 2. Physical build

### The globe

- **Diameter:** 9 in / 229 mm (fits the 8–10 in constraint with margin for the
  stand). At this size the mesh edges run **23–27 mm** (~1 in) node to node.
- **Fabrication:** 3D-print the sphere from `geodesic.stl` scaled to 229 mm
  (×2.286 from the 100 mm-diameter file), split into printable sections — two
  hemispheres, or twelve pentagonal caps (one per well, each cap = the 20
  triangles of one kised pentagon) which nest better on small printers.
- **Node sockets:** drill/model a **3 mm hole, 5 mm deep** at each of the 282
  vertices. For magnetic retention, embed a **4×2 mm neodymium disc** at the
  bottom of each socket, all with the same polarity facing out; pieces carry
  the opposite pole. The peg gives shear alignment, the magnet gives pull-off
  retention, so the globe can be rotated freely — even inverted — without
  shedding pieces. (Pegs alone also work if you prefer a friction fit:
  print pegs at 3.2 mm and ream holes to taste. Test magnet strength at
  23 mm spacing: adjacent pieces should not visibly pull toward each other.)
- **Node marking:** ring-engrave the 12 wells (fill with contrasting paint or
  press-fit a brass grommet) and dot-engrave the 60 ridges. Fields stay bare.
- **Stand:** a weighted printed ring (~90 mm inner diameter) with three PTFE
  or felt pads. The globe sits loose in the cradle and rotates in any
  direction; players spin it to reach their front lines.

### Pieces (per player color)

| Piece | Qty | Physical form |
|---|---|---|
| HQ dome | 1 | 20 mm dome, peg + magnet |
| Extractor | 4 | ring that surrounds a well socket |
| Barracks | 3 | small block |
| Turret | 3 | small tower |
| Relay | 5 | thin pylon |
| Legion squad | 6 | 14 mm base with a **strength dial (1–4)** and a snap-on cap that hides it |
| Skirmisher | 4 | 12 mm base, no dial (always 1 pip, printed distinct) |
| Colossus | 2 | tall walker with a **5-position dial** (starts at 5) and cap |

Squad dials solve the "stacking on a sphere" problem: one piece per node,
its dial is the squad size. Caps keep dials hidden (§5); if caps prove
fiddly at the table, play the open-information variant (§7).

### Off-globe components

- Per player: a dashboard (action slots + build costs), **two sand timers**
  (30 s and 60 s), a **Reaction token**, ~20 energy tokens.
- Shared: one **3-minute pulse timer**, a pulse track (6 spaces), a bell,
  and 12 "raided" markers.

## 3. Setup

1. Pick starting wells by player count (see §1). Place your HQ dome on your
   well, one Legion (dial 2, capped) on any adjacent node, and one Skirmisher
   on any node within 2 hops.
2. Take 3 energy. Set both your timers on your dashboard, drained. Reaction
   token face up.
3. Start the 3-minute pulse timer. The game is now live — there are no turns.

## 4. The real-time engine

You act by **committing a timer**: place one of your drained sand timers,
flowing, onto an action slot on your dashboard, *say the action out loud*
("Maneuver!", "Assault W9!"), and perform it immediately. That timer cannot
be used again until it drains. With a 30 s and a 60 s timer you average one
action every ~20 seconds — your "APM budget."

**Quick actions (30 s timer only):**

- **MANEUVER** — move up to 2 of your pieces, each up to its speed
  (Skirmisher 3 edges, Legion 2, Colossus 1). Moving a Legion onto your own
  Legion merges dials (max 4). You may also split: leave pips behind as a
  new squad piece. Colossi never merge or split.
- **ASSAULT** — attack an adjacent enemy node with one of your pieces
  (§5). One battle per assault.

**Heavy actions (60 s timer only):**

- **CONSTRUCT** — pay and place 1 building on an empty well or ridge node in
  your **supply network**: your HQ, plus any node within 2 hops of one of
  your Relays or buildings (Relay chains extend your reach across the globe,
  pylon-style).
- **TRAIN** — pay and place any number of things you can afford at **one**
  site (your HQ or any one Barracks): new pieces appear on that building's
  node or adjacent to it, and/or add dial pips to squads on or adjacent to
  it (max 4).

**Costs:** Skirmisher 1 ⚡ · Legion pip 1 ⚡ · Colossus 4 ⚡ · Extractor 2 ⚡ ·
Barracks 3 ⚡ · Turret 2 ⚡ · Relay 1 ⚡.

### The pulse (economy heartbeat)

When the 3-minute pulse timer drains, whoever notices first flips it and
rings the bell (flipping promptly is mandatory, not tactical). Advance the
pulse track; everyone simultaneously collects:

- 1 ⚡ base income (requires your HQ standing), plus
- 1 ⚡ per well you control (a unit or building of yours on it), plus
- 1 ⚡ extra per Extractor on a well you control.

Then everyone turns their Reaction token face up and removes "raided"
markers. Hand cap: 10 ⚡.

**Game end:** the game ends the moment the 6th-pulse sand drains (not when
the bell rings — no bell-timing games).

### Table etiquette (keeps real-time sane)

- One hand on the globe at a time. **The globe may not be rotated while any
  player's fingers are on a piece.**
- A timer must be *placed and flowing*, and the action called aloud, before
  you touch pieces.
- If two players reach for interacting pieces simultaneously, the
  **defender** (owner of the stationary piece) resolves first.
- Anyone may call **"CLASH"** to freeze the two players involved in a combat
  until it's resolved; everyone else keeps playing.

## 5. Combat (deterministic — no dice, no arguments)

Everything fights with **pips**: a Legion's dial (1–4), a Skirmisher's 1, a
Colossus's dial (up to 5). Dials stay capped except during resolution.

An ASSAULT resolves in strict order:

1. **Declare.** Point at your attacking piece (the **spearhead**, adjacent
   to the target) and the target node.
2. **React.** The defender, if their Reaction token is face up, may flip it
   and move one of their pieces from a node adjacent to the target *into*
   the target node (dials merge for this battle, may exceed 4 temporarily).
3. **Reveal.** Both sides uncap. Attack total **A** = spearhead pips + pips
   of every other piece of yours adjacent to the target (supporters —
   they don't move). Defense total **D** = defending pips **+1** if the node
   is a well or ridge **+2** if a friendly Turret is on or adjacent to it.
   A node with only buildings defends with 1 pip + bonuses.
4. **Resolve.**
   - **A > D — captured.** All defending pieces are destroyed. The attacker
     then removes pips equal to the *defender's pips* (not bonuses) from the
     spearhead and/or supporters, their choice, and moves one surviving
     participant onto the node. Extractors and Relays on the node are
     captured intact; Barracks, Turrets, and HQs are demolished.
   - **A ≤ D — repelled.** The spearhead is destroyed. The defender removes
     pips equal to **half the spearhead's pips (round down)**. Supporters
     are untouched.
5. **Salvage.** Every player immediately collects 1 ⚡ per 2 pips they just
   lost (round down). Re-cap all dials.

Notes that fall out of this: a 1-pip probe reveals a defender's strength at
the cost of the piece and nothing else; even fights favor the defender;
bonuses decide *whether* a fort falls, but never increase its teeth; and no
position on the globe is unbreakable — mass enough adjacent pips and
anything falls.

**RAID** (Skirmisher only): as your ASSAULT action, target an adjacent enemy
node containing **only buildings**. Steal 2 ⚡ from that player and retreat
along the edge you came from. Each well can be raided once per pulse (mark
it), and a node with a Turret on or adjacent to it cannot be raided.

## 6. Winning

Victory is checked **the instant** the condition occurs:

- **Domination:** control **7 of 12 wells** (2 players) or **6 of 12**
  (3–4 players) → immediate win.
- **Timeout:** when the 6th-pulse sand drains, most wells controlled wins;
  tiebreak by total pips on the globe, then energy in hand.

**No elimination.** Losing your HQ costs you its 1 ⚡ base income and its
training site — a serious wound, not a funeral. You keep playing; Barracks
still train.

## 7. Variants

- **Open information (casual):** skip the dial caps; all strengths public.
  Faster and friendlier; combat becomes fully predictable, so expect more
  maneuver and fewer battles.
- **Turn-based (no timers):** players alternate taking 2 actions each
  (any mix); Reactions work the same; run a pulse after every full round;
  play 8 pulses. Good for teaching and solo testing.
- **Skirmish globe:** restrict play to the 72 well+ridge nodes (movement
  hops count along ridge-to-ridge adjacency through fields). Faster, denser,
  chess-like; good for 2 players in 30 minutes.
- **Fog of war (lite):** you may only ASSAULT a node if one of your units is
  within 2 hops at the start of the action — no cross-globe alpha strikes.

## 8. Balance knobs for playtesting

The numbers most likely to need tuning, in expected order:

1. **Pulse length (3 min)** — shorter starves builds, longer favors turtling.
2. **Repelled-assault damage (half spearhead pips)** — the dial between
   "probing is free chip damage" (too high) and "forts never erode" (zero).
3. **Turret bonus (+2)** and high-ground (+1) — the defense economy; with
   combined assaults these set how many attackers a fort is "worth."
4. **Salvage rate (1 ⚡ / 2 pips)** — the comeback engine; raise it if losses
   snowball, lower it if wars feel consequence-free.
5. **Relay reach (2 hops)** — how fast fronts can be projected; with speed-2
   squads a 14-hop push takes ~7 quick actions (~4–5 minutes), so relays are
   what make cross-globe pressure viable.

## 9. Changelog (design playtests)

Three simulated 2-player games drove v0.1 → v0.3:

| Ver | Found in play | Change |
|---|---|---|
| 0.1→0.2 | Antipodal starts split the wells into two uncontested clusters of 6, so "control 6" was a no-contact execution race | 2P domination raised to 7 wells |
| 0.1→0.2 | Max defense (4+1+2=7) beat max attack (5): fortified wells were permanently uncapturable, rewarding pure turtling | Combined assault: supporters adjacent to the target add their pips |
| 0.1→0.2 | Public dials + deterministic combat meant battles only happened when pre-decided; defenders had zero counterplay | Hidden dials (caps) + defender Reaction (once per pulse) |
| 0.1→0.2 | Watching an opponent's flowing timers guaranteed unanswerable attacks | Reaction is timer-free |
| 0.1→0.2 | Skirmisher raid loops forced garrisoning every well forever | Raids once per well per pulse; Turrets block raids; retreat path defined |
| 0.1→0.2 | Losing an army was pure snowball with no comeback; elimination benched a player | Salvage (1 ⚡ / 2 pips lost); HQ loss no longer eliminates |
| 0.2→0.3 | 1-pip probes chipped forts 1-for-1 while scouting — strictly profitable, turtling overnerfed | Repelled assaults deal only half the spearhead's pips (probes chip 0) |
| 0.2→0.3 | Reaction/reveal ordering was ambiguous and leaked hidden info | Strict declare → react → reveal → resolve sequence |
| 0.2→0.3 | Dial-less Colossus was a special case in every combat sentence | Colossus got a 5-pip dial; all damage is pips everywhere |
| 0.2→0.3 | Bell-ringing at the final pulse was a tiebreak exploit | Game ends when the sand drains; prompt flipping is mandatory |
