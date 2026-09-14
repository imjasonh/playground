# Hexland

Raise and lower land on a hex map the way RollerCoaster Tycoon does it on
squares. Each hex owns six shared corners. Painting a tile lifts those
corners, so neighbors tilt into slopes. A second step on the same tile
makes a cliff unless **Smooth** is on, which pulls the next ring along.

The renderer only draws dirt on the island rim. Shared edges stay open,
so a hillside is one mesh instead of a stack of hex boxes.

**Path** paints a road. **Clear path** erases it. Right-click or Shift
while **Path** is selected also clears. **Corner** moves one vertex.
**Level** copies the first tile's height across the stroke. **Water** is
a global plane; anything below it floods.

## Controls

- Drag to paint. Right-click or Shift lowers land, or clears a path.
- **Tile** edits one hex. **Patch** edits the hex and its neighbors.
- Ctrl-drag or Command-drag orbits. Two fingers pan, pinch-zoom, and
  twist. Space-drag or Alt-drag pans.
- Scroll zooms. Shift-scroll spins. Alt-scroll tilts.
- **Q** / **E** spin. **R** / **F** tilt. **1**–**6** pick tools.

## Run locally

```bash
npm start
```

Then open http://localhost:3000. Tests:

```bash
npm test
```
