import test from "node:test";
import assert from "node:assert/strict";

import {
  BOARD,
  ColdClimbGame,
  HOLES,
  axisFromDrag,
  pointToSegmentDistanceSquared,
} from "../src/game.js";

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

  placeBallInHole(game, HOLES[0]);
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

  placeBallInHole(game, HOLES[1]);
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
    placeBallInHole(game, HOLES[1]);
    advance(game, BOARD.fallDuration + 0.05);
  }

  assert.equal(game.phase, "gameover");
  assert.equal(game.lives, 0);
});

test("clearing the final target wins the game", () => {
  const game = new ColdClimbGame();
  game.start();
  game.level = HOLES.length - 1;

  placeBallInHole(game, HOLES.at(-1));
  advance(game, BOARD.fallDuration + 0.05);

  assert.equal(game.phase, "won");
  assert.equal(game.level, HOLES.length);
  assert.ok(game.score > 0);
});
