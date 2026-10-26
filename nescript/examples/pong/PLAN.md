# Pong — Implementation Plan

A production-quality Pong example for NEScript in the same vein as
`examples/war.ne`. This is the living plan: each step is checked off
as it completes, and any mid-flight design changes land in the
"Design revisions" section at the bottom.

---

## 1. Scope & quality bar

- **Title screen**: big "PONG" banner (later milestones), 3-option menu
  (CPU VS CPU / 1 PLAYER / 2 PLAYERS), cursor, blinking "PRESS A"
  prompt, brisk title march, autopilot to CPU VS CPU after
  `TITLE_AUTO_FRAMES` with no input so the headless golden capture
  reaches gameplay.
- **Gameplay**: two paddles, smooth ball physics, proper hit-angle
  deflection, responsive controls, dashed center line, two-digit
  score HUD above each side.
- **Powerups**: three types that spawn periodically, bounce around
  the playfield, and apply an effect when caught by a paddle:
  1. **LONG** — catching paddle extends from 24→40 px for the next
     `LONG_PADDLE_HITS` paddle hits.
  2. **FAST** — catching paddle's next hit doubles the ball's x
     velocity for that ball's remaining life.
  3. **MULTI** — catching paddle's next hit spawns two extra balls
     at the hit point (so 1→3 balls, each scores independently).
- **Victory**: first to `WIN_SCORE` points. Big "PLAYER N WINS"
  banner, fanfare, auto-return to title.
- **Audio**: every feel event gets a dedicated sfx, plus a title
  march and a victory fanfare.

---

## 2. File layout

```
examples/pong.ne                 top-level: game decl, palette, Tileset, includes, start
examples/pong/PLAN.md            this document
examples/pong/constants.ne       layout + gameplay + powerup + phase constants
examples/pong/assets.ne          Tileset sprite block (every custom CHR tile)
examples/pong/audio.ne           sfx + music declarations
examples/pong/state.ne           all mutable globals
examples/pong/rng.ne             8-bit Galois LFSR
examples/pong/render.ne          draw_paddle, draw_ball, draw_score, draw_word_* helpers
examples/pong/input.ne           paddle_step(side) — unified human + CPU paddle update
examples/pong/ball.ne            multi-ball physics (update, paddle & wall collision)
examples/pong/powerup.ne         powerup spawn, bounce, catch, apply
examples/pong/title_state.ne     state Title + menu
examples/pong/serve_state.ne     state Serve (brief pause before launch)
examples/pong/play_state.ne     state Playing (phase machine)
examples/pong/victory_state.ne   state Victory
```

---

## 3. Hardware budget

### Sprite budget per frame (max 64 OAM slots)

| Entity               | Sprites | Notes                          |
|----------------------|---------|--------------------------------|
| Left paddle          | 3-5     | 3 in normal, 5 in long mode    |
| Right paddle         | 3-5     | same                           |
| Active balls         | 1-3     | up to `MAX_BALLS = 3`          |
| Powerup              | 0-1     | one slot when active           |
| Center-line dashes   | ~7      | 1 tile every 32 px, at x = 124 |
| HUD score digits     | 4       | 2 digits per side              |
| **Steady-state max** | ~24     | well under 64                  |

### Sprite-per-scanline check (W0109 budget = 8)

Paddles are at x = 16 and x = 232, separated by 216 px. The ball and
powerup live in the middle of the playfield; center-line dashes live
at x = 124. HUD digits live at y = 16 (above the playfield). Worst
case scanline hits one paddle-tile + ball + powerup + center-line
dash = 4 sprites. Comfortable.

### Tile budget (max 256)

| Group                       | Tiles |
|-----------------------------|-------|
| A-Z alphabet (8×8)          | 26    |
| 0-9 digits (8×8)            | 10    |
| BIG PONG banner (4 × 2×2)   | 16    |
| Paddle (top/mid/bot caps)   | 3     |
| Ball                        | 1     |
| Cursor arrow                | 1     |
| Center-line dash            | 1     |
| Powerup icons (L, F, M)     | 3     |
| **Total**                   | ~61   |

### RAM budget

| Structure             | Bytes |
|-----------------------|-------|
| Paddle state (× 2)    | ~16   |
| Ball state (× 3)      | ~24   |
| Powerup state         | ~10   |
| Scores + mode + phase | ~12   |
| RNG + timers + misc   | ~12   |
| **Total**             | ~74   |

All well within the NEScript 1280-byte general RAM ceiling.

---

## 4. Milestones

- [x] **M1** — Skeleton & title screen
- [x] **M2** — Paddles with input and clamping; HUD scores
- [x] **M3** — Single-ball physics (serve, bounce, score-out)
- [x] **M4** — Multi-ball via parallel ball_* arrays (structural — arrays loop from M3)
- [x] **M5** — CPU paddle AI; title mode pick dispatch
- [x] **M6** — Long-paddle powerup plumbing (draw + collision wired in M3)
- [x] **M7** — Fast-ball + multi-ball-on-next-hit flags
- [x] **M8** — Powerup entity (spawn, bounce, catch, apply)
- [x] **M9** — Victory state + fanfare
- [x] **M10** — Audio + polish pass
- [x] **M11** — Golden capture + README/examples/README entries
- [ ] **M12** — Compiler bug cleanup (revert workarounds where fixable)
- [ ] **M13** — Thorough code review pass

---

## 5. Design decisions (locked in M1)

- `WIN_SCORE = 7`
- `MAX_BALLS = 3`
- Paddle height: 24 px normal, 40 px long
- Ball base speed: 1 px/frame on each axis; FAST doubles x to 2
- Powerup spawn cadence: every `POWERUP_SPAWN_FRAMES` (~240) frames
- Powerups bounce off all four walls, catchable by either paddle
- CPU AI: 1 px/frame toward ball y, 4-frame reaction lag, ±4 px miss zone
- Default autopilot mode: CPU VS CPU (so the golden harness captures gameplay)

---

## 6. Design revisions

(empty — record any mid-flight changes here)
