# Reverse evolution & known interesting seeds

Research notes for making Life stacks that are both **interesting** (complexity
gate) and **supportable** (removability gate).

## The tip identity

A breakaway tip is created for every Life cell at generation `z` whose cell
directly below is empty. In Life terms that is exactly a **birth**
(dead → alive at that XY). Therefore:

> every birth ≡ one support tip

Interesting evolution is driven by births and deaths. Tip-free histories can
only **shrink** (deaths / spark die-off) into ash — they cannot grow or move.

## Backward search (`--pattern reverse`)

Idea: choose a sparse still-life **ash** as `Z(T_end)`, then walk backward
through predecessors, pruning high-tip transitions.

### What works

- **Zero-birth predecessors** of still lifes are easy to find: add “spark”
  cells in a margin-2 neighborhood that die in one step. The layer transition
  needs **no tips**.
- Implemented in `src/reverse.rs` and exposed as `--pattern reverse`
  (seed selects the ash garden).

### What doesn’t (yet)

- Those spark predecessors almost never have further zero-birth grandparents.
  Empirically, reverse depth on 16×16 ash gardens is **~1 generation**, then
  the stack pads with still life to fill `--depth`.
- That fails the complexity gate (need activity until generation ≥ 8).
- Allowing 1–4 births per reverse layer (stochastic search) did not yield
  depth ≥ 8 on the same boards — finding long predecessor chains is a hard
  combinatorial search (SAT / specialized Life tools), not a local flip walk.

So reverse-from-ash is tip-light but **too shallow** to pass “interesting”
without a much stronger predecessor engine.

## Known interesting seeds

| Pattern | Lifespan (typical) | Printable Z @ 4 mm | Supportable? |
|---------|-------------------:|--------------------|--------------|
| R-pentomino | ~1103 | needs ~4.4 m height | No — many rest-on-model tips (`sc≈45`) |
| Acorn | ~5206 | absurd | No (same class) |
| Diehard | 130 then empty | 520 mm > A1 Mini 180 mm | Tip-heavy while alive |
| Thunderbird | ~243 | still tall | ~186 tips in first 24 gens |
| B-heptomino | settles @2 on small boards | fits | **TOO BORING** |
| Glider / LWSS | never settles (leaves board) | fits Z | No — moving = births every layer |
| Plus → traffic light | settles @6 (p2) | fits | Tip-heavy oscillator contacts |

Classic methuselahs are the wrong scale for FDM at 4 mm/cell: they need
hundreds of generations, and the chaotic middle is exactly the regime that
forces rest-on-model tree branches.

## Practical paths forward

1. **Weaken removability** (e.g. allow ≤1 rest-on-model) — near-miss soups at
   settle≥8 already score ~75 with a single rest landing.
2. **Stronger reverse engine** (SAT / lifelib-style predecessor search) aimed
   at long shrink-only histories — still tip-light by construction, if depth
   can reach the complexity floor.
3. **Hybrid**: reverse only the top K layers into ash (clean removable top),
   forward-search the bottom for interesting seeds that *reach* that ash —
   same dual-gate tension unless (1) or (2) lands.
