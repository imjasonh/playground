import test from "node:test";
import assert from "node:assert/strict";

import {
  CAR,
  RCProAmGame,
  TRACK,
  aiControlsForCar,
  applyCarInputs,
  centerlinePoint,
  createCar,
  createGridPositions,
  isOnTrack,
  pushOntoTrack,
  rankCars,
  resolveTrackCollision,
  steerAxisFromDrag,
  updateLapCounter,
} from "../src/game.js";

function advance(game, seconds, step = 1 / 60) {
  for (let elapsed = 0; elapsed < seconds; elapsed += step) {
    game.update(Math.min(step, seconds - elapsed));
  }
}

test("steer drag becomes a clamped axis", () => {
  assert.equal(steerAxisFromDrag(100, 142, 42), 1);
  assert.equal(steerAxisFromDrag(100, 58, 42), -1);
  assert.equal(steerAxisFromDrag(100, 121, 42), 0.5);
  assert.equal(steerAxisFromDrag(Number.NaN, 100), 0);
});

test("centerline points stay on the circuit", () => {
  for (let index = 0; index < 64; index += 1) {
    const point = centerlinePoint(index / 64);
    assert.ok(isOnTrack(point.x, point.y));
  }
});

test("off-track points get nudged back without large jumps", () => {
  const onLine = centerlinePoint(0.25);
  const offX = onLine.x - onLine.tangentY * (TRACK.halfWidth + 12);
  const offY = onLine.y + onLine.tangentX * (TRACK.halfWidth + 12);

  const corrected = pushOntoTrack(offX, offY);
  assert.equal(corrected.wall, "edge");
  assert.ok(isOnTrack(corrected.x, corrected.y));
  assert.ok(Math.hypot(corrected.x - offX, corrected.y - offY) < 22);
});

test("throttle and steering produce forward motion with lateral grip", () => {
  const start = centerlinePoint(0.1);
  const car = createCar({ id: "test", x: start.x, y: start.y, angle: start.angle });

  applyCarInputs(car, 1, 0.4, 0.2);
  assert.ok(car.vx ** 2 + car.vy ** 2 > 0);
  assert.ok(car.skid >= 0);
});

test("wall collisions slide along the barrier instead of teleporting", () => {
  const start = centerlinePoint(0.6);
  const car = createCar({
    id: "test",
    x: start.x - start.tangentY * (TRACK.halfWidth + 6),
    y: start.y + start.tangentX * (TRACK.halfWidth + 6),
    angle: start.angle,
    vx: Math.cos(start.angle) * 120,
    vy: Math.sin(start.angle) * 120,
  });
  const beforeX = car.x;
  const beforeY = car.y;

  const hit = resolveTrackCollision(car);
  assert.equal(hit, true);
  assert.ok(isOnTrack(car.x, car.y));
  assert.ok(Math.hypot(car.x - beforeX, car.y - beforeY) < 20);
});

test("lap counter detects a finish-line crossing", () => {
  const car = createCar({
    id: "test",
    x: centerlinePoint(0.01).x,
    y: centerlinePoint(0.01).y,
    progress: 0.92,
    vx: 80,
    vy: 0,
  });
  car.lastProgress = 0.92;

  const crossed = updateLapCounter(car);
  assert.equal(crossed, true);
  assert.equal(car.lap, 1);
});

test("rankCars orders by laps then progress", () => {
  const leader = createCar({ id: "leader", lap: 2, progress: 0.4 });
  const chaser = createCar({ id: "chaser", lap: 2, progress: 0.2 });
  const lapped = createCar({ id: "lapped", lap: 1, progress: 0.95 });

  const ranked = rankCars([lapped, chaser, leader]);
  assert.deepEqual(ranked.map((car) => car.id), ["leader", "chaser", "lapped"]);
  assert.equal(leader.position, 1);
  assert.equal(lapped.position, 3);
});

test("AI produces bounded throttle and steering", () => {
  const start = centerlinePoint(0.2);
  const car = createCar({
    id: "volt",
    x: start.x,
    y: start.y,
    angle: start.angle,
    aiSkill: 0.8,
    aiAggression: 0.6,
  });

  const controls = aiControlsForCar(car);
  assert.ok(controls.throttle >= 0.48 && controls.throttle <= 1);
  assert.ok(controls.steer >= -1 && controls.steer <= 1);
});

test("grid positions stage cars on the start straight", () => {
  const grid = createGridPositions(5);
  assert.equal(grid.length, 5);
  for (const spot of grid) {
    assert.ok(isOnTrack(spot.x, spot.y));
  }
});

test("a race moves from countdown into racing", () => {
  const game = new RCProAmGame();
  game.start();
  assert.equal(game.phase, "countdown");

  advance(game, 3.2);
  assert.equal(game.phase, "racing");
  assert.ok(game.cars.length === 5);
  assert.ok(game.playerCar);
});

test("boost can be triggered once during a race", () => {
  const game = new RCProAmGame();
  game.start();
  advance(game, 3.2);

  assert.equal(game.triggerBoost(), true);
  assert.equal(game.playerCar.boostTime > 0, true);
  assert.equal(game.triggerBoost(), false);
});

test("computer opponents keep moving on track during a race", () => {
  const game = new RCProAmGame();
  game.start();
  advance(game, 3.2);
  advance(game, 4);

  for (const car of game.cars) {
    if (car.isPlayer) {
      continue;
    }
    assert.ok(Math.hypot(car.vx, car.vy) > 5, `${car.id} should be moving`);
    assert.ok(isOnTrack(car.x, car.y), `${car.id} should stay on track`);
  }
});

test("repeated wall hits stay near the impact point", () => {
  const start = centerlinePoint(0.35);
  const car = createCar({
    id: "test",
    x: start.x - start.tangentY * (TRACK.halfWidth + 10),
    y: start.y + start.tangentX * (TRACK.halfWidth + 10),
    angle: start.angle,
    vx: Math.cos(start.angle + 0.8) * 160,
    vy: Math.sin(start.angle + 0.8) * 160,
  });
  const originX = car.x;
  const originY = car.y;

  for (let step = 0; step < 8; step += 1) {
    applyCarInputs(car, 1, 0.6, 1 / 60);
    resolveTrackCollision(car);
  }

  assert.ok(Math.hypot(car.x - originX, car.y - originY) < 80);
  assert.ok(isOnTrack(car.x, car.y));
});
