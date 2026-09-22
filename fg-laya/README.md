# Laya / Jev FlightGear autopilot

A FlightGear addon plus a Node loop that reads the instruments and asks a
[System One](https://openrouter.ai/docs/guides/community/jev) model what to do
with aileron, elevator, rudder, and throttle. The model is Laya or Jev when
you have one. Otherwise the same questions run through a local System One
backend so you can still fly.

The airplane starts in the air and holds a left-hand circle, or it flies to
random waypoints and never stops.

## How it decides

Every tick the loop builds a JSON state from latitude, longitude, altitude,
airspeed, pitch, roll, heading, vertical speed, slip, and the current
waypoint. Then it asks four `choice` questions and one `noul`:

| Question | Type | What the answer moves |
| --- | --- | --- |
| `aileron` | choice | roll / heading |
| `elevator` | choice | pitch / altitude |
| `throttle` | choice | airspeed |
| `rudder` | choice | slip |
| `arrived` | noul | retarget the next waypoint |

The surfaces only move after those answers. There is no separate PID writing
the controls.

Backends, in order of `SYSTEMONE_BACKEND` or autodetection:

1. `jev` — `POST https://openrouter.ai/api/alpha/decisions` with
   `typesafe/jev-1.13` when `OPENROUTER_API_KEY` is set.
2. `laya` — `POST $LAYA_URL` with the same `{ state, questions }` body. Point
   this at a local Laya or `system-one` server.
3. `local` — in-process System One that returns the same answer shapes
   (choice + probabilities + confidence, noul). Used when the other two are
   not configured.

## Run the built-in airplane

This does not need FlightGear. It is the same decision loop over a Cessna-shaped
kinematic model, with an instrument HUD:

```bash
cd fg-laya
npm test
npm start
```

Open http://127.0.0.1:8788. Default mission is a 1.6 nm left-hand orbit west of
San Francisco, starting at 3,500 ft and 100 kt.

Random waypoints:

```bash
node scripts/fly.js --world sim --mode waypoints
```

## Fly it in FlightGear

Install FlightGear 2020.3 or later. The Ubuntu package is `flightgear`.

```bash
bash scripts/start-fg.sh
```

That starts a Cessna 172 already airborne over the water, and opens Phi HTTP on
port 9146 plus telnet on 5501. After it connects, the Node loop freezes the
FDM, starts the Lycoming (magnetos, mixture, JSBSim `set-running`), runs
`reposition` at 3,500 ft / 105 kt, and switches to chase view.

Ubuntu 2020.3 has no `--addon` switch; the loop writes `/controls/flight/*`
over HTTP (`POST /json/<path>` with `{"value": ...}`). On a newer FlightGear
that accepts `--addon`, pass `--addon=$PWD/addon` yourself so the Nasal side
copies `/laya/cmd/*` as well. If the airplane leaves the envelope (below 400 ft,
under 50 kt, or inverted), the loop repositions it and keeps flying.

In a second terminal:

```bash
node scripts/fly.js --world fg --mode circle
```

`--world auto` uses FlightGear when the property server answers, and the
built-in model otherwise.

## Point it at Jev or Laya

```bash
export OPENROUTER_API_KEY=...
node scripts/fly.js --world sim --backend jev
```

```bash
export LAYA_URL=http://127.0.0.1:8080/systemone
node scripts/fly.js --world sim --backend laya
```

`LAYA_URL` must accept `POST` JSON `{ "state": ..., "questions": ... }` and
return `{ "answers": { "aileron": { "type": "choice", "choice": "...", ... }, ... } }`.
That is the OpenRouter Decisions / TypeSafe System One contract. A local
`system-one` ONNX server from [PyPI](https://pypi.org/project/system-one/)
works once you have fetched a Laya graph.

## Tests

```bash
cd fg-laya
npm test
```

The loop test runs 90 seconds of closed-loop flight and checks that altitude,
speed, and bank stay in the envelope while heading travels more than 200
degrees around the circle.

## Layout

```
fg-laya/
├── addon/           FlightGear addon (addon.xml + Nasal)
├── hud/             instrument + probability display
├── scripts/fly.js   decision loop
├── scripts/start-fg.sh
├── src/             observe, questions, System One, nav, kinematics
└── tests/
```
