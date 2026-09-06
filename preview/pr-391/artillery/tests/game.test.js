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
  tankPose,
  terrainHeightAt,
} from "../src/game.js";

function mulberry32(seed) {
  let state = seed >>> 0;
  return () => {
    state = (state + 0x6d2b79f5) >>> 0;
    let value = state;
    value = Math.imul(value ^ (value >>> 15), value | 1);
    value ^= value + Math.imul(value ^ (value >>> 7), value | 61);
    return ((value ^ (value >>> 14)) >>> 0) / 4294967296;
  };
}

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

test("each duel gets reproducible random terrain with level firing pads", () => {
  const terrain = createTerrain(mulberry32(11));
  const sameSeed = createTerrain(mulberry32(11));
  const otherSeed = createTerrain(mulberry32(29));

  assert.equal(terrain.length, WORLD.width + 1);
  assert.deepEqual(terrain, sameSeed);
  assert.notDeepEqual(terrain, otherSeed);
  assert.ok(Math.min(...terrain) >= 414);
  assert.ok(Math.max(...terrain) <= 520);

  for (const tankX of [150, 1050]) {
    const padHeight = terrainHeightAt(terrain, tankX);
    for (let offset = -40; offset <= 40; offset += 10) {
      assert.equal(terrainHeightAt(terrain, tankX + offset), padHeight);
    }
  }
});

test("craters lower the terrain without changing distant ground", () => {
  const original = createTerrain(mulberry32(7));
  const terrain = original.slice();
  const centerBefore = terrainHeightAt(terrain, 500);
  const distantBefore = terrainHeightAt(terrain, 700);

  deformTerrain(terrain, 500, 40, 30);

  assert.equal(terrainHeightAt(terrain, 500), centerBefore + 30);
  assert.equal(terrainHeightAt(terrain, 700), distantBefore);
  assert.ok(terrainHeightAt(terrain, 525) > terrainHeightAt(original, 525));
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
  const terrain = createTerrain(() => 0.5);
  const leftShot = createProjectile(terrain, 0, { angle: 45, power: 70 }, 0);
  const rightShot = createProjectile(terrain, 1, { angle: 45, power: 70 }, 0);

  assert.ok(leftShot.vx > 0);
  assert.ok(rightShot.vx < 0);
  assert.ok(leftShot.vy < 0);
  assert.ok(rightShot.vy < 0);
});

test("elevation remains world-relative after a tank is tilted by a crater", () => {
  const terrain = createTerrain(() => 0.5);
  deformTerrain(terrain, 120);
  const pose = tankPose(terrain, 0);
  const shot = createProjectile(terrain, 0, { angle: 45, power: 70 }, 0);
  const launchAngle = (Math.atan2(-shot.vy, Math.abs(shot.vx)) * 180) / Math.PI;

  assert.notEqual(pose.groundAngle, 0);
  assert.ok(Math.abs(launchAngle - 45) < 0.0001);
});

test("crosswind creates a meaningful change in the projectile path", () => {
  const east = new ArtilleryGame(() => 0.5);
  const west = new ArtilleryGame(() => 0.5);
  east.start();
  west.start();
  east.wind = 10;
  west.wind = -10;
  east.fire();
  west.fire();

  advance(east, 0.4);
  advance(west, 0.4);

  assert.ok(east.projectile.vx > west.projectile.vx);
  assert.ok(east.projectile.x - west.projectile.x > 25);
});

test("projectile simulation advances faster than real time", () => {
  const game = new ArtilleryGame(() => 0.5);
  game.start();
  game.wind = 0;
  game.fire();

  game.update(0.1);

  assert.ok(game.projectile.age >= 0.16);
  assert.ok(game.projectile.age <= 0.18);
});

test("segment distance catches a fast projectile crossing a tank", () => {
  assert.equal(pointToSegmentDistanceSquared(10, 5, 0, 0, 20, 0), 25);
  assert.equal(pointToSegmentDistanceSquared(30, 0, 0, 0, 20, 0), 100);
});

test("a direct hit removes armor without trapping the tank in its crater", () => {
  const game = new ArtilleryGame(() => 0.5);
  game.start();
  const terrainBefore = game.terrain.slice();
  const groundBefore = terrainHeightAt(game.terrain, game.tanks[1].x);

  forceDirectHit(game, 1);

  assert.equal(game.phase, "resolving");
  assert.equal(game.tanks[1].health, 100 - WORLD.directDamage);
  const impact = game.consumeEvents().find((event) => event.type === "impact");
  assert.equal(impact.directTank, 1);
  assert.equal(impact.damages[1], WORLD.directDamage);
  assert.equal(terrainHeightAt(game.terrain, game.tanks[1].x), groundBefore);
  assert.ok(
    terrainHeightAt(game.terrain, impact.x - WORLD.craterRadius + 10) >
      terrainHeightAt(terrainBefore, impact.x - WORLD.craterRadius + 10),
  );
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
  assert.notEqual(imperfect.estimatedWind, 0);
});

test("computer inaccuracy prevents consistently damaging firing solutions", () => {
  let directHits = 0;
  let damagingHits = 0;
  let totalDamage = 0;
  const trials = 24;

  for (let attempt = 0; attempt < trials; attempt += 1) {
    const game = new ArtilleryGame(mulberry32(100 + attempt));
    game.start(1);
    const aim = chooseComputerAim({
      terrain: game.terrain,
      tanks: game.tanks,
      shooterIndex: 1,
      wind: game.wind,
      random: mulberry32(900 + attempt),
    });
    game.setAim(aim.angle, aim.power);
    game.fire();
    advance(game, 6);
    const impact = game.consumeEvents().find((event) => event.type === "impact");
    if (impact?.directTank === 0) {
      directHits += 1;
    }
    if (impact && Math.max(...impact.damages) > 0) {
      damagingHits += 1;
    }
    totalDamage += impact ? Math.max(...impact.damages) : 0;
  }

  assert.ok(directHits < trials * 0.4, `${directHits}/${trials} direct hits`);
  assert.ok(
    damagingHits < trials * 0.65,
    `${damagingHits}/${trials} damaging hits`,
  );
  assert.ok(totalDamage / trials < 22, `${totalDamage / trials} average damage`);
});

test("wind generation spans both directions and includes calm conditions", () => {
  assert.equal(randomWind(() => 0), -16);
  assert.equal(randomWind(() => 1), 16);
  assert.equal(randomWind(() => 0.5), 0);
});
