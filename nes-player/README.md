# NES player

Play the NEScript example ROMs in the browser with
[jsnes](https://github.com/bfirsh/jsnes), or open your own `.nes` file.

The game list comes from the GitHub contents API for
[`nescript/examples`](../nescript/examples) on `main`. Each ROM is
downloaded from `raw.githubusercontent.com` on `main` when you pick it, so a
ROM rebuilt on `main` shows up here without a redeploy. If the API refuses
the request (it allows 60 anonymous requests an hour per IP address), the
page falls back to the last list it loaded.

You can drop a `.nes` file anywhere on the page or choose one with
**Open .nes file**. It is read locally and is not uploaded.

`?rom=<name>` opens a game from the list, for example
`?rom=dvd_screensaver`.

## Controls

| Button | Player 1 | Player 2 |
|--------|----------|----------|
| D-pad | Arrow keys | W A S D |
| B | Z | F |
| A | X | G |
| Select | Right Shift | R |
| Start | Enter | T |

The first gamepad connected is player 1, and the second is player 2.
Gamepads use the standard mapping: the right face button is A, the bottom
one is B. On a touch screen the page shows a controller for player 1.

## How it runs

`src/player.js` runs a `jsnes.NES` at 60.0988 frames a second from
`requestAnimationFrame` and feeds its samples to an AudioWorklet. The
emulator is built with the `AudioContext`'s own sample rate. The worklet
keeps at most 120 ms of audio queued and drops the oldest samples past
that, so the gap between the NES frame rate and the display's refresh rate
can't build up lag.

## Run locally

```bash
cd nes-player
npm start
```

Open http://localhost:3000. Tests:

```bash
npm test
```

## Update jsnes

`vendor/jsnes.min.js` is a copy of `jsnes/dist/jsnes.min.js`, so GitHub
Pages can serve the app without a build step. After you change the jsnes
version:

```bash
npm install
npm run vendor
```
