# PENTAKIS — a real-time strategy board game on a geodesic globe

A 2–4 player RTS played on the physical frequency-2 spherical pentakis snub
dodecahedron in this directory: harvest energy from the globe's 12 wells,
train squads, push supply lines around the planet, and storm the enemy
capital — all in real time, paced by sand timers instead of turns.

- **Players:** 2–4
- **Time:** 45–75 minutes
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

- **2 players:** antipodal wells (14 hops apart).
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
  print pegs at 3.2 mm and ream holes to taste.)
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
| Legion squad | 6 | 14 mm base with a **strength dial (1–4)** |
| Skirmisher | 4 | 12 mm base, no dial (always strength 1, printed distinct) |
| Colossus | 2 | tall walker, no dial (always strength 5) |

Squad dials solve the "stacking on a sphere" problem: one piece per node,
its dial is the squad size.

### Off-globe components

- Per player: a dashboard (action slots + build costs), **two sand timers**
  (30 s and 60 s), ~20 energy tokens.
- Shared: one **3-minute pulse timer**, a pulse track (6 spaces), and a bell.

## 3. Setup

1. Pick starting wells by player count (see §1). Place your HQ dome on your
   well, one Legion (dial 2) on any adjacent node, and one Skirmisher on any
   node within 2 hops.
2. Take 3 energy. Set both your timers on your dashboard, drained.
3. Start the 3-minute pulse timer. The game is now live — there are no turns.

## 4. The real-time engine

You act by **committing a timer**: place one of your drained sand timers,
flowing, onto an action slot on your dashboard and immediately perform that
action. That timer cannot be used again until it drains. With a 30 s and a
60 s timer you average one action every ~20 seconds — your "APM budget."

**Quick actions (30 s timer only):**

- **MANEUVER** — move up to 2 of your pieces, each up to its speed
  (Skirmisher 3 edges, Legion 2, Colossus 1). Moving onto your own Legion
  merges dials (max 4). You may also split: leave pips behind as a new squad
  piece.
- **ASSAULT** — move 1 piece onto an adjacent enemy node and resolve combat
  (§5). One battle per assault.

**Heavy actions (60 s timer only):**

- **CONSTRUCT** — pay and place 1 building on an empty well or ridge node in
  your **supply network**: your HQ, plus any node within 2 hops of one of
  your Relays or buildings (Relay chains extend your reach across the globe,
  pylon-style).
- **TRAIN** — pay and place new units, or add dial pips to existing squads,
  at your HQ or any Barracks (new pieces appear on the building's node or
  adjacent to it). Any amount you can afford, one site per action.

**Costs:** Skirmisher 1 ⚡ · Legion pip 1 ⚡ · Colossus 4 ⚡ · Extractor 2 ⚡ ·
Barracks 3 ⚡ · Turret 2 ⚡ · Relay 1 ⚡.

### The pulse (economy heartbeat)

When the 3-minute pulse timer drains, **any** player flips it, rings the
bell, and advances the pulse track. Everyone simultaneously collects:

- 1 ⚡ base income (HQ), plus
- 1 ⚡ per well they control (a unit or building of theirs on it), plus
- 1 ⚡ extra per Extractor on a well they control.

Hand cap: 10 ⚡. The game ends at the **6th pulse**.

### Table etiquette (keeps real-time sane)

- One hand on the globe at a time; rotate it freely, never to obstruct.
- A timer must be *placed and flowing* before you touch pieces.
- If two players reach for interacting pieces simultaneously, the
  **defender** (owner of the stationary piece) resolves first.
- Anyone may call **"CLASH"** to freeze the two players involved in a combat
  until it's resolved; everyone else keeps playing.

## 5. Combat (deterministic — no dice, no arguments)

When a piece assaults an adjacent enemy node, compare single totals:

- **Attacker:** unit strength (dial value; Skirmisher 1; Colossus 5).
- **Defender:** unit strength **+1 if on a well or ridge** (high ground)
  **+2 if a friendly Turret is on or adjacent to the node**. A building
  alone defends with strength 1 (+ bonuses).

Higher total wins; the loser's piece is removed and the winning attacker
advances onto the node. **Ties destroy one pip on both sides** (pieces
without dials are removed) and the attacker retreats. A Colossus that wins
against a node with a building destroys the building too; other winners
capture Extractors and Relays intact but demolish Barracks, Turrets, and HQs.

Skirmisher special — **RAID:** as an assault against a node containing only a
building, a Skirmisher steals 2 ⚡ from that player instead of fighting,
then retreats. Cheap harassment, just like the real thing.

## 6. Winning

Immediately when checked at any pulse:

- **Domination:** you control **6 of the 12 wells** → instant win.
- **Decapitation:** an HQ's destruction eliminates that player (pieces stay,
  inert, until captured). Last player standing wins.
- **Timeout:** after the 6th pulse, most wells controlled wins; tiebreak by
  energy in hand, then by total dial pips on the globe.

## 7. Variants

- **Turn-based (no timers):** players alternate taking 2 actions each
  (any mix, no timer restriction); run a pulse after every full round; play
  8 pulses. Same rules otherwise — good for teaching and for solo testing.
- **Skirmish globe:** restrict play to the 72 well+ridge nodes (movement
  hops count along ridge-to-ridge adjacency through fields). Faster, denser,
  chess-like; good for 2 players in 30 minutes.
- **Fog of war (lite):** you may only ASSAULT a node if one of your units is
  within 2 hops at the start of the action — no cross-globe alpha strikes.

## 8. Balance knobs for playtesting

These are the numbers most likely to need tuning, in expected order:

1. **Pulse length (3 min)** — shorter starves builds, longer favors turtling.
2. **Domination threshold (6 wells)** — raise to 7 if games end too fast.
3. **Turret bonus (+2)** and high-ground (+1) — the whole defense economy.
4. **Relay reach (2 hops)** — controls how fast fronts can be projected;
   with average speed-2 squads a 14-hop assault takes ~7 quick actions
   (~4–5 minutes), so relays are what make cross-globe pressure viable.
5. **Colossus cost (4 ⚡)** — it wins every open-field fight except a full
   Legion on high ground (4+1); price it so it's a siege investment, not
   default.
