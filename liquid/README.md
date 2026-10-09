# liquid

`liquid` simulates a tank of liquid in your terminal. You push it, pull it into
blobs, pour more in, and tilt the tank, all with the mouse and a few keys.

It's a Go program built on [Bubble Tea](https://github.com/charmbracelet/bubbletea)
v2, [Lip Gloss](https://github.com/charmbracelet/lipgloss) v2, and
[bubblezone](https://github.com/lrstanley/bubblezone) v2.

## Run

Go fetches the toolchain that `go.mod` asks for if yours is older:

```bash
cd liquid
go run .
```

The tank looks best in a terminal with 24-bit color. In a 256-color terminal,
Bubble Tea maps each color to the nearest one it has. The program honors
`NO_COLOR`, but the liquid is hard to read without color. The terminal must be
at least 56 columns by 12 rows.

## Controls

| Mouse | Action |
|-------|--------|
| Drag | Push the liquid away from the cursor |
| Right drag | Pull the liquid into a blob that follows the cursor |
| Middle drag | Pour more liquid |
| Shift or Alt while moving | Attract the liquid |
| Ctrl while moving | Disperse the liquid |
| Wheel | Resize the brush |
| Click a toolbar button | Same as its key |

Many terminals use Shift with the mouse to select text, so they never send the
program a Shift-modified mouse event. If Shift doesn't attract, hold Alt
instead, or press Tab to make plain hovering attract or disperse.

Terminals only report modifiers along with mouse events, so the program can't
tell when you let go of Shift while the cursor is still. Attraction stops 1.5
seconds after the last mouse event.

| Key | Action |
|-----|--------|
| Space | Pause or resume |
| `.` | Step one frame while paused |
| `r` | Reset the scene |
| `1` to `5` | Dam break, double dam, droplet, pool, zero-gravity blob |
| Arrow keys | Point gravity that way, as if you tilted the tank |
| `g` | Turn gravity on or off |
| `s` | Shake the tank |
| `v` | Switch between the liquid, particles, and heat views |
| `c` | Change colors: ocean, lava, slime, ink, mercury |
| Tab | Make hovering attract, disperse, or do nothing |
| `[` and `]` | Resize the brush |
| `?` | Show every control |
| `q` | Quit |

The ink theme is two liquids, cyan and magenta. Try the double dam with it and
stir the middle.

## Flags

| Flag | Default | Description |
|------|---------|-------------|
| `-scene` | `dam` | Starting scene: `dam`, `double`, `drop`, `pool`, or `blob` |
| `-theme` | `ocean` | Colors: `ocean`, `lava`, `slime`, `ink`, or `mercury` |
| `-view` | `liquid` | How to draw the liquid: `liquid`, `particles`, or `heat` |
| `-particles` | `2200` | About how many particles each scene starts with |
| `-fps` | `60` | Frames per second, from 10 to 120 |
| `-seed` | `0` | Seed for the random jitter in scenes; `0` picks one at random |

The simulation takes about 1.5 ms per step for 2,000 particles on one core,
and runs 180 steps per second. If it can't keep up, it slows down rather than
falling behind.

## How it works

The code has three packages under `internal/`.

`sim` is the physics. The liquid is particles, simulated with double density
relaxation from Clavet, Beaudoin, and Poulin,
[Particle-based Viscoelastic Fluid Simulation](https://dl.acm.org/doi/10.1145/1073368.1073400)
(SCA 2005). Each step:

1. Accelerates particles by gravity and by the brush.
1. Damps the speed at which neighbors approach each other (viscosity).
1. Moves each particle along its velocity.
1. Moves neighbors apart or together so the density relaxes toward a rest
   density. A second, always-repulsive near density keeps particles from
   clumping and gives the liquid surface tension, so it forms droplets.
1. Pushes particles out of the walls and derives new velocities from how far
   each particle moved.

Particles at a wall have no neighbors on one side, so the walls act as if
resting liquid filled the space beyond them. The density and pressure that
liquid adds are integrals over a half plane, computed once into a table.
Particles are sorted into grid cells one interaction radius across at every
step, so neighbors are adjacent in memory. The relaxation keeps resting liquid
trembling slightly, so particles slower than 1.5 h/s, where h is the
interaction radius, lose speed until the liquid is still.

`render` draws the tank. In the liquid and heat views, each terminal cell is
two square pixels drawn with the upper half block character, using the
foreground color for the top pixel and the background color for the bottom one.
Particles are splatted into density, velocity, and dye fields. Liquid darkens
with depth below the surface, fast liquid near the surface turns to foam, and
thin liquid is translucent spray. The particles view draws each particle as one
braille dot, which gives 2×4 dots per cell. The brush outline is always
braille, so it stays thin over the liquid.

`ui` is the Bubble Tea model. Lip Gloss lays out the header, the bordered
tank, and the toolbar, and its compositor draws the help panel over the
running simulation. bubblezone marks the tank and every toolbar button as a
zone: to handle a mouse event, the model asks the zone manager which button
was hit, or where in the tank the cursor is, instead of recomputing the layout.
Bubble Tea calls `View` after every message, and mouse motion can arrive
hundreds of times a second, so the model draws once per frame and caches the
result.

## Test

```bash
cd liquid
go test ./...
```

CI runs `go build ./...` and `go test -race ./...`. The UI tests drive the
model with real bubblezone zones and a fake clock.

## Record the demo

`demo/record.sh` builds the program, runs it under
[asciinema](https://asciinema.org/) 3, and converts the recording to a GIF with
[agg](https://github.com/asciinema/agg):

```bash
cd liquid
demo/record.sh /tmp/liquid-demo
```

`demo/drive.py` plays the part of the terminal. It writes the same SGR mouse
reports that a terminal sends when you drag and hover, so the recording shows
real input passing through Bubble Tea and bubblezone.

GitHub shows images in pull requests and READMEs through a proxy that rejects
files over 5 MiB. The recording's size, length, and frame rate keep the GIF
under that limit, and the script warns if it isn't. If
[gifsicle](https://www.lcdf.org/gifsicle/) is installed, the script also
optimizes the GIF.
