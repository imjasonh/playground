# Cold Climb

A touch-first browser game inspired by the two-handle mechanics of mechanical
climbing arcade games. Raise both ends of the bar to climb, tilt it to roll the
ball sideways, and land in the glowing pocket without touching any dark pocket.

## Controls

- **Touch / pen:** drag up or down on the left and right controls. Each control
  tracks its own pointer, so both ends can move at the same time.
- **Keyboard:** `W` / `S` move the left end; arrow up / arrow down move the
  right end.
- **Restart:** press `R` or use the Restart button.

The ten targets are played from bottom to top. A successful target resets the
bar at the bottom and lights the next pocket; a miss costs one of three balls.

## Run locally

The game has no runtime dependencies and can be served as static files:

```bash
npm start
```

Then open <http://localhost:3000>. Run the physics tests with:

```bash
npm test
```
