import test from "node:test";
import assert from "node:assert/strict";

import {
  ArtilleryGame,
  WORLD,
  chooseComputerAim,
  createProjectile,
  createTerrain,
  deformTerrain,
  normalizeAim,
  pointToSegmentDistanceSquared,
  randomWind,
  terrainHeightAt,
} from "../src/game.js";

function advance(game, seconds, step = 1 / 60) {
  for (let elapsed = 0; elapsed < seconds; elapsed += step) {
    game.update(Math.min(step, seconds - elapsed));
  }
}

function forceDirectHit(game, targetIndex) {
  assert.equal(game.phase, "aiming");
  const shooter = game.activePlayer;
  const target = game.tanks[targetIndex];
  const direction = target.x > game.tanks[shooter].x ? 1 : -1;
  game.fire();
  Object.assign(game.projectile, {
    x: target.x - direction * 52,
    y: target.y,
    vx: direction * 520,
    vy: 0,
    wind: 0,
    age: 0.5,
  });
  game.update(0.08);
}

test("the fixed battlefield includes level firing pads", () => {
  const terrain = createTerrain();

  assert.equal(terrain.length, WORLD.width + 1);
  assert.equal(terrainHeightAt(terrain, 150), 458);
  assert.equal(terrainHeightAt(terrain, 1050), 451);
  assert.ok(terrainHeightAt(terrain, 620) < terrainHeightAt(terrain, 500));
});

test("craters lower the terrain without changing distant ground", () => {
  const terrain = createTerrain();
  const centerBefore = terrainHeightAt(terrain, 500);
  const distantBefore = terrainHeightAt(terrain, 700);

  deformTerrain(terrain, 500, 40, 30);

  assert.equal(terrainHeightAt(terrain, 500), centerBefore + 30);
  assert.equal(terrainHeightAt(terrain, 700), distantBefore);
  assert.ok(
    terrainHeightAt(terrain, 525) > terrainHeightAt(createTerrain(), 525),
  );
});

test("aim values are rounded and clamped to playable limits", () => {
  assert.deepEqual(normalizeAim(44.6, 71.7), { angle: 45, power: 72 });
  assert.deepEqual(normalizeAim(-100, 900), {
    angle: WORLD.minAngle,
    power: WORLD.maxPower,
  });
  assert.deepEqual(normalizeAim(Number.NaN, Number.NaN), {
    angle: 45,
    power: 70,
  });
});

test("left and right tanks launch toward one another", () => {
  const terrain = createTerrain();
  const leftShot = createProjectile(terrain, 0, { angle: 45, power: 70 }, 0);
  const rightShot = createProjectile(terrain, 1, { angle: 45, power: 70 }, 0);

  assert.ok(leftShot.vx > 0);
  assert.ok(rightShot.vx < 0);
  assert.ok(leftShot.vy < 0);
  assert.ok(rightShot.vy < 0);
});

test("crosswind accelerates rounds in its direction", () => {
  const east = new ArtilleryGame(() => 0.5);
  const west = new ArtilleryGame(() => 0.5);
  east.start();
  west.start();
  east.wind = 10;
  west.wind = -10;
  east.fire();
  west.fire();

  advance(east, 0.12);
  advance(west, 0.12);

  assert.ok(east.projectile.vx > west.projectile.vx);
  assert.ok(east.projectile.x > west.projectile.x);
});

test("segment distance catches a fast projectile crossing a tank", () => {
  assert.equal(pointToSegmentDistanceSquared(10, 5, 0, 0, 20, 0), 25);
  assert.equal(pointToSegmentDistanceSquared(30, 0, 0, 0, 20, 0), 100);
});

test("a direct hit removes armor and deforms the battlefield", () => {
  const game = new ArtilleryGame(() => 0.5);
  game.start();
  const groundBefore = terrainHeightAt(game.terrain, game.tanks[1].x);

  forceDirectHit(game, 1);

  assert.equal(game.phase, "resolving");
  assert.equal(game.tanks[1].health, 100 - WORLD.directDamage);
  assert.ok(terrainHeightAt(game.terrain, game.tanks[1].x) > groundBefore);
  const impact = game.consumeEvents().find((event) => event.type === "impact");
  assert.equal(impact.directTank, 1);
  assert.equal(impact.damages[1], WORLD.directDamage);
});

test("an out-of-range shot passes the turn without damage", () => {
  const game = new ArtilleryGame(() => 0.5);
  game.start();
  game.fire();
  Object.assign(game.projectile, {
    x: WORLD.width + 88,
    y: 100,
    vx: 500,
    vy: 0,
    wind: 0,
    age: 1,
  });

  game.update(0.02);
  assert.equal(game.phase, "resolving");
  assert.deepEqual(
    game.tanks.map((tank) => tank.health),
    [100, 100],
  );

  advance(game, WORLD.explosionDuration + 0.05);
  assert.equal(game.phase, "aiming");
  assert.equal(game.activePlayer, 1);
});

test("destroying a tank ends the duel after the explosion", () => {
  const game = new ArtilleryGame(() => 0.5);
  game.start(1);
  game.tanks[0].health = WORLD.directDamage;

  forceDirectHit(game, 0);
  advance(game, WORLD.explosionDuration + 0.05);

  assert.equal(game.tanks[0].health, 0);
  assert.equal(game.phase, "gameover");
  const result = game.consumeEvents().find((event) => event.type === "gameover");
  assert.equal(result.winner, 1);
});

test("the computer finds a viable shot but adds bounded inaccuracy", () => {
  const game = new ArtilleryGame(() => 0.5);
  game.start(1);
  game.wind = 0;

  const exact = chooseComputerAim({
    terrain: game.terrain,
    tanks: game.tanks,
    shooterIndex: 1,
    wind: 0,
    random: () => 0.5,
  });
  const imperfect = chooseComputerAim({
    terrain: game.terrain,
    tanks: game.tanks,
    shooterIndex: 1,
    wind: 0,
    random: () => 0.99,
  });

  assert.ok(exact.solutionDistance <= WORLD.tankRadius + WORLD.projectileRadius);
  assert.ok(exact.angle >= WORLD.minAngle && exact.angle <= WORLD.maxAngle);
  assert.ok(exact.power >= WORLD.minPower && exact.power <= WORLD.maxPower);
  assert.notDeepEqual(
    { angle: exact.angle, power: exact.power },
    { angle: imperfect.angle, power: imperfect.power },
  );
});

test("wind generation spans both directions and includes calm conditions", () => {
  assert.equal(randomWind(() => 0), -12);
  assert.equal(randomWind(() => 1), 12);
  assert.equal(randomWind(() => 0.5), 0);
});
