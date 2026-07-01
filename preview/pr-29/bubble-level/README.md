# Bubble Level

A gyroscope-powered bubble (spirit) level for the browser. Lay your phone on a
surface and the bubble floats to the high side — exactly like the air bubble in a
carpenter's level. A big digital readout shows how many degrees you're off, and
the whole thing glows green when the surface is level.

## How it works

The app listens to the [`deviceorientation`](https://developer.mozilla.org/docs/Web/API/Window/deviceorientation_event)
event, which reports the device's `beta` (front/back) and `gamma` (left/right)
tilt. Those angles are turned into a bubble position by projecting gravity onto
the plane of the screen and floating the bubble toward the raised side. All of
that math lives in `src/level.js` as pure, framework-free functions.

- **Bullseye vial** — the round center vial reads tilt on both axes at once
  (best for a phone lying flat).
- **Tube vials** — the horizontal tube reads left/right tilt, the vertical tube
  reads front/back tilt.
- **Calibrate** — zero the level against whatever surface the phone is resting on
  so a slightly-off table reads as flat. The offset is saved in `localStorage`;
  **Reset calibration** clears it.
- **Rotation-aware** — `deviceorientation` always reports tilt in the device's
  natural (portrait) frame, so the bubble vector is rotated by
  `screen.orientation.angle` to stay correct when the phone is turned to
  landscape (rather than relying on orientation lock, which needs fullscreen and
  isn't supported on iOS Safari). In short landscape the layout also switches to
  a side-by-side view so the dial stays visible.

## Play

Open `index.html` in a browser, or run a local server:

```bash
npm install
npm start
```

Then visit http://localhost:3000 — on a phone, allow motion access when prompted.

### Notes on device support

- **iOS Safari** requires a tap to grant motion-sensor access, so the app shows
  an **Enable motion sensors** button first.
- **Desktops / devices without a gyroscope** fall back to a **preview mode**:
  drag inside the circle (or use the arrow keys, `0` to re-center) to see the
  level respond.

## Tests

```bash
npm test          # unit tests for the tilt math (Jest)
npm run test:e2e  # mobile + desktop browser tests (Playwright)
npm run test:all  # both
```

## Project layout

- `src/level.js` — pure tilt geometry (bubble position, tilt angle, calibration)
- `src/app.js` — browser UI: sensor permission, rendering loop, calibration,
  desktop preview
- `index.html` / `styles.css` — markup and styling
- `tests/` — Jest unit tests
- `e2e/` — Playwright mobile/desktop tests
