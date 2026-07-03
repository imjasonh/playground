import test from "node:test";
import assert from "node:assert/strict";

import {
  CAR,
  RCProAmGame,
  TRACK,
  WORLD,
  aiControlsForCar,
  applyCarInputs,
  centerlinePoint,
  createCar,
  createGridPositions,
  isOnTrack,
  progressFromPoint,
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

test("centerline points stay inside the carpet ring", () => {
  for (let index = 0; index < 64; index += 1) {
    const point = centerlinePoint(index / 64);
    assert.ok(isOnTrack(point.x, point.y));
  }
});

test("off-track points get pushed back to the boundary", () => {
  const outside = pushOntoTrack(WORLD.cx + TRACK.outerA + 20, WORLD.cy);
  assert.equal(outside.wall, "outer");
  assert.ok(isOnTrack(outside.x, outside.y));

  const inside = pushOntoTrack(WORLD.cx + TRACK.innerA - 20, WORLD.cy);
  assert.equal(inside.wall, "inner");
  assert.ok(isOnTrack(inside.x, inside.y));
});

test("throttle and steering produce forward motion with lateral grip", () => {
  const car = createCar({ id: "test", x: WORLD.cx, y: WORLD.cy + TRACK.centerB - 20, angle: -Math.PI / 2 });

  applyCarInputs(car, 1, 0.4, 0.2);
  assert.ok(car.vx ** 2 + car.vy ** 2 > 0);
  assert.ok(car.skid >= 0);
});

test("wall collisions bleed speed off the boundary normal", () => {
  const car = createCar({
    id: "test",
    x: WORLD.cx + TRACK.outerA + 5,
    y: WORLD.cy,
    angle: 0,
    vx: 120,
    vy: 0,
  });

  const hit = resolveTrackCollision(car);
  assert.equal(hit, true);
  assert.ok(isOnTrack(car.x, car.y));
  assert.ok(Math.abs(car.vx) < 120);
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
  const car = createCar({
    id: "volt",
    x: centerlinePoint(0.2).x,
    y: centerlinePoint(0.2).y,
    angle: centerlinePoint(0.2).angle,
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
