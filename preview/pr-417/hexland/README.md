# Hexland

Raise and lower land on a hex map the way RollerCoaster Tycoon does it on
squares. Each hex owns six shared corners. Painting a tile lifts those
corners, so neighbors tilt into slopes. A second step on the same tile
makes a cliff unless **Smooth** is on, which pulls the next ring along.

**Corner** moves one vertex. **Level** copies the first tile's height
across the stroke. **Water** is a global plane; anything below it floods.

## Controls

- Drag to paint. Right-click or Shift lowers when **Raise** is selected.
- **Tile** edits one hex. **Patch** edits the hex and its neighbors.
- Two fingers pan, pinch-zoom, and twist. Space-drag or Alt-drag pans.
- Scroll zooms. Shift-scroll spins. **Q** / **E** also spin.

## Run locally

```bash
npm start
```

Then open http://localhost:3000. Tests:

```bash
npm test
```
