import test from "node:test";
import assert from "node:assert/strict";

import {
  BOARD,
  ColdClimbGame,
  HOLE_BOUNDS,
  HOLE_COUNT,
  createHoles,
  axisFromDrag,
  pointToSegmentDistanceSquared,
} from "../src/game.js";

// Small deterministic PRNG so layout assertions are reproducible.
function mulberry32(seed) {
  let state = seed >>> 0;
  return () => {
    state = (state + 0x6d2b79f5) >>> 0;
    let t = state;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function advance(game, seconds, step = 1 / 60) {
  for (let elapsed = 0; elapsed < seconds; elapsed += step) {
    game.update(Math.min(step, seconds - elapsed));
  }
}

function placeBallInHole(game, hole) {
  game.roundGrace = 0;
  game.leftBarY = hole.y + BOARD.ballOffset;
  game.rightBarY = hole.y + BOARD.ballOffset;
  game.ballX = hole.x;
  game.ballVelocityX = 0;
  game.setControls(0, 0);
  game.update(1 / 120);
}

test("drag distance becomes a clamped control axis", () => {
  assert.equal(axisFromDrag(200, 171, 58), 0.5);
  assert.equal(axisFromDrag(200, 260, 58), -1);
  assert.equal(axisFromDrag(200, 100, 58), 1);
  assert.equal(axisFromDrag(Number.NaN, 100), 0);
});

test("point-to-segment distance detects swept collisions", () => {
  assert.equal(pointToSegmentDistanceSquared(5, 2, 0, 0, 10, 0), 4);
  assert.equal(pointToSegmentDistanceSquared(12, 0, 0, 0, 10, 0), 4);
  assert.equal(pointToSegmentDistanceSquared(3, 4, 0, 0, 0, 0), 25);
});

test("the two controls move the bar ends independently", () => {
  const game = new ColdClimbGame();
  game.start();
  game.setControls(1, 0);
  advance(game, 0.2);

  assert.ok(game.leftBarY < BOARD.resetBarY);
  assert.equal(game.rightBarY, BOARD.resetBarY);
  assert.ok(Math.abs(game.rightBarY - game.leftBarY) <= BOARD.maxTilt);
});

test("bar tilt rolls the ball toward the lower end", () => {
  const game = new ColdClimbGame();
  game.start();
  game.roundGrace = 10;
  game.leftBarY = 700;
  game.rightBarY = 820;
  const startingX = game.ballX;

  advance(game, 0.4);

  assert.ok(game.ballVelocityX > 0);
  assert.ok(game.ballX > startingX);
});

test("maximum tilt is enforced under opposing controls", () => {
  const game = new ColdClimbGame();
  game.start();
  game.roundGrace = 10;
  game.setControls(1, -1);
  advance(game, 1);

  assert.ok(
    Math.abs(game.rightBarY - game.leftBarY) <= BOARD.maxTilt + 0.0001,
  );
});

test("landing in the lit pocket advances to the next target", () => {
  const game = new ColdClimbGame();
  game.start();

  placeBallInHole(game, game.holes[0]);
  const [holeEvent] = game.consumeEvents().filter((event) => event.type === "hole");
  assert.equal(game.phase, "falling");
  assert.equal(holeEvent.success, true);

  advance(game, BOARD.fallDuration + 0.05);
  assert.equal(game.phase, "playing");
  assert.equal(game.level, 1);
  assert.equal(game.target.id, 2);
  assert.ok(game.score >= 1000);
  assert.equal(game.lives, 3);
});

test("landing in a dark pocket costs a ball without changing target", () => {
  const game = new ColdClimbGame();
  game.start();

  placeBallInHole(game, game.holes[1]);
  const [holeEvent] = game.consumeEvents().filter((event) => event.type === "hole");
  assert.equal(holeEvent.success, false);

  advance(game, BOARD.fallDuration + 0.05);
  assert.equal(game.phase, "playing");
  assert.equal(game.level, 0);
  assert.equal(game.target.id, 1);
  assert.equal(game.lives, 2);
});

test("the third missed pocket ends the game", () => {
  const game = new ColdClimbGame();
  game.start();

  for (let miss = 0; miss < 3; miss += 1) {
    placeBallInHole(game, game.holes[1]);
    advance(game, BOARD.fallDuration + 0.05);
  }

  assert.equal(game.phase, "gameover");
  assert.equal(game.lives, 0);
});

test("clearing the final target wins the game", () => {
  const game = new ColdClimbGame();
  game.start();
  game.level = game.holes.length - 1;

  placeBallInHole(game, game.holes.at(-1));
  advance(game, BOARD.fallDuration + 0.05);

  assert.equal(game.phase, "won");
  assert.equal(game.level, game.holes.length);
  assert.ok(game.score > 0);
});

test("each play randomises the pockets but keeps ten numbered targets", () => {
  const game = new ColdClimbGame(mulberry32(123));
  const firstLayout = game.holes;

  game.start();
  const secondLayout = game.holes;

  assert.equal(secondLayout.length, HOLE_COUNT);
  assert.deepEqual(
    secondLayout.map((hole) => hole.id),
    Array.from({ length: HOLE_COUNT }, (_, index) => index + 1),
  );
  // start() builds a brand new layout rather than reusing the previous one.
  assert.notStrictEqual(firstLayout, secondLayout);
  assert.notDeepEqual(
    firstLayout.map((hole) => ({ x: hole.x, y: hole.y })),
    secondLayout.map((hole) => ({ x: hole.x, y: hole.y })),
  );
});

test("an injected generator makes layouts reproducible", () => {
  assert.deepEqual(createHoles(mulberry32(42)), createHoles(mulberry32(42)));
  assert.notDeepEqual(createHoles(mulberry32(42)), createHoles(mulberry32(7)));
});

test("every randomly placed pocket stays within the ball's reach", () => {
  // A flat bar can park the ball center anywhere in this envelope, so any
  // pocket inside it can be touched — the layout is never unwinnable.
  const minReachX = BOARD.barLeftX + BOARD.ballRadius;
  const maxReachX = BOARD.barRightX - BOARD.ballRadius;
  const minReachY = BOARD.minBarY - BOARD.ballOffset;
  const maxReachY = BOARD.maxBarY - BOARD.ballOffset;

  for (let attempt = 0; attempt < 300; attempt += 1) {
    for (const hole of createHoles()) {
      assert.ok(hole.x >= minReachX && hole.x <= maxReachX, `x ${hole.x} reachable`);
      assert.ok(hole.y >= minReachY && hole.y <= maxReachY, `y ${hole.y} reachable`);
      assert.ok(hole.x >= HOLE_BOUNDS.minX && hole.x <= HOLE_BOUNDS.maxX);
      assert.ok(hole.y >= HOLE_BOUNDS.minY && hole.y <= HOLE_BOUNDS.maxY);
    }
  }
});

test("pockets climb upward and never share a capture zone", () => {
  // Adjacent capture zones must not overlap; that leaves a clear horizontal
  // corridor at every height, so there is always a path up the wall.
  const minimumGap = 2 * BOARD.captureRadius;

  for (let attempt = 0; attempt < 300; attempt += 1) {
    const holes = createHoles();

    for (let i = 1; i < holes.length; i += 1) {
      // Lower id sits lower on the wall (larger y) and is targeted first.
      assert.ok(
        holes[i - 1].y - holes[i].y > minimumGap,
        "consecutive pockets climb with a clear vertical gap",
      );
    }

    for (let i = 0; i < holes.length; i += 1) {
      for (let j = i + 1; j < holes.length; j += 1) {
        const distance = Math.hypot(
          holes[i].x - holes[j].x,
          holes[i].y - holes[j].y,
        );
        assert.ok(distance > minimumGap, "pocket centers stay apart");
      }
    }
  }
});
