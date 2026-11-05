export const WORLD = Object.freeze({
  width: 1200,
  height: 640,
  gravity: 245,
  windScale: 7,
  speedScale: 5.15,
  projectileTimeScale: 1.7,
  projectileRadius: 6,
  tankRadius: 28,
  tankHalfHeight: 16,
  barrelLength: 46,
  minAngle: 12,
  maxAngle: 82,
  minPower: 28,
  maxPower: 100,
  blastRadius: 96,
  craterRadius: 54,
  craterDepth: 34,
  directDamage: 62,
  explosionDuration: 0.55,
  maxShotTime: 10,
});

const TANK_X = Object.freeze([150, 1050]);
const FIXED_STEP = 1 / 120;
const TERRAIN_CONTROL_SPACING = 100;
const PAD_HALF_WIDTH = 46;
const PAD_BLEND_WIDTH = 42;

export function clamp(value, minimum, maximum) {
  return Math.min(maximum, Math.max(minimum, value));
}

function finiteOr(value, fallback) {
  return Number.isFinite(value) ? value : fallback;
}

function smoothstep(amount) {
  return amount * amount * (3 - 2 * amount);
}

function flattenTankPad(terrain, centerX, preferredHeight) {
  const padHeight = Number.isFinite(preferredHeight)
    ? preferredHeight
    : Math.round(terrainHeightAt(terrain, centerX));
  const outerRadius = PAD_HALF_WIDTH + PAD_BLEND_WIDTH;
  const start = Math.max(0, Math.floor(centerX - outerRadius));
  const end = Math.min(terrain.length - 1, Math.ceil(centerX + outerRadius));

  for (let x = start; x <= end; x += 1) {
    const distance = Math.abs(x - centerX);
    if (distance <= PAD_HALF_WIDTH) {
      terrain[x] = padHeight;
      continue;
    }

    const amount = smoothstep((distance - PAD_HALF_WIDTH) / PAD_BLEND_WIDTH);
    terrain[x] = padHeight + (terrain[x] - padHeight) * amount;
  }
}

export function createTerrain(random = Math.random) {
  const sample = typeof random === "function" ? random : Math.random;
  const controlPoints = [];
  let previousHeight = 466;

  for (let x = 0; x <= WORLD.width; x += TERRAIN_CONTROL_SPACING) {
    const proposedHeight = 466 + (sample() * 2 - 1) * 54;
    const height = clamp(
      proposedHeight,
      Math.max(414, previousHeight - 44),
      Math.min(520, previousHeight + 44),
    );
    controlPoints.push([x, height]);
    previousHeight = height;
  }

  const terrain = new Float64Array(WORLD.width + 1);
  let pointIndex = 0;

  for (let x = 0; x <= WORLD.width; x += 1) {
    while (
      pointIndex < controlPoints.length - 2 &&
      x > controlPoints[pointIndex + 1][0]
    ) {
      pointIndex += 1;
    }

    const [leftX, leftY] = controlPoints[pointIndex];
    const [rightX, rightY] = controlPoints[pointIndex + 1];
    const amount = smoothstep((x - leftX) / (rightX - leftX));
    terrain[x] = leftY + (rightY - leftY) * amount;
  }

  TANK_X.forEach((x) => flattenTankPad(terrain, x));
  return terrain;
}

export function terrainHeightAt(terrain, x) {
  if (!terrain?.length) {
    return WORLD.height;
  }

  const boundedX = clamp(finiteOr(x, 0), 0, terrain.length - 1);
  const left = Math.floor(boundedX);
  const right = Math.min(terrain.length - 1, left + 1);
  const amount = boundedX - left;
  return terrain[left] + (terrain[right] - terrain[left]) * amount;
}

export function deformTerrain(
  terrain,
  centerX,
  radius = WORLD.craterRadius,
  depth = WORLD.craterDepth,
) {
  if (!terrain?.length || !Number.isFinite(centerX) || radius <= 0 || depth <= 0) {
    return terrain;
  }

  const start = Math.max(0, Math.floor(centerX - radius));
  const end = Math.min(terrain.length - 1, Math.ceil(centerX + radius));

  for (let x = start; x <= end; x += 1) {
    const normalized = (x - centerX) / radius;
    if (Math.abs(normalized) > 1) {
      continue;
    }
    const bowl = Math.sqrt(1 - normalized * normalized);
    terrain[x] = Math.min(WORLD.height - 12, terrain[x] + depth * bowl);
  }

  return terrain;
}

export function normalizeAim(angle, power) {
  return Object.freeze({
    angle: clamp(
      Math.round(finiteOr(Number(angle), 45)),
      WORLD.minAngle,
      WORLD.maxAngle,
    ),
    power: clamp(
      Math.round(finiteOr(Number(power), 70)),
      WORLD.minPower,
      WORLD.maxPower,
    ),
  });
}

export function randomWind(random = Math.random) {
  const sample = typeof random === "function" ? random : Math.random;
  const wind = Math.round((sample() * 32 - 16) * 10) / 10;
  return Math.abs(wind) < 0.9 ? 0 : wind;
}

export function pointToSegmentDistanceSquared(px, py, ax, ay, bx, by) {
  const dx = bx - ax;
  const dy = by - ay;
  const lengthSquared = dx * dx + dy * dy;

  if (lengthSquared === 0) {
    return (px - ax) ** 2 + (py - ay) ** 2;
  }

  const amount = clamp(((px - ax) * dx + (py - ay) * dy) / lengthSquared, 0, 1);
  const nearestX = ax + dx * amount;
  const nearestY = ay + dy * amount;
  return (px - nearestX) ** 2 + (py - nearestY) ** 2;
}

export function tankPose(terrain, playerIndex) {
  const index = playerIndex === 1 ? 1 : 0;
  const x = TANK_X[index];
  const leftGround = terrainHeightAt(terrain, x - 18);
  const rightGround = terrainHeightAt(terrain, x + 18);
  return {
    x,
    y: terrainHeightAt(terrain, x) - WORLD.tankHalfHeight,
    direction: index === 0 ? 1 : -1,
    groundAngle: clamp(Math.atan2(rightGround - leftGround, 36), -0.24, 0.24),
  };
}

export function barrelPose(terrain, playerIndex, aim) {
  const pose = tankPose(terrain, playerIndex);
  const normalizedAim = normalizeAim(aim?.angle, aim?.power);
  const radians = (normalizedAim.angle * Math.PI) / 180;
  const groundCosine = Math.cos(pose.groundAngle);
  const groundSine = Math.sin(pose.groundAngle);
  const vectorX = pose.direction * Math.cos(radians);
  const vectorY = -Math.sin(radians);
  const baseX = pose.x + 7 * groundSine;
  const baseY = pose.y - 7 * groundCosine;

  return {
    ...pose,
    aim: normalizedAim,
    baseX,
    baseY,
    tipX: baseX + vectorX * WORLD.barrelLength,
    tipY: baseY + vectorY * WORLD.barrelLength,
    vectorX,
    vectorY,
  };
}

export function createProjectile(terrain, playerIndex, aim, wind = 0) {
  const barrel = barrelPose(terrain, playerIndex, aim);
  const speed = barrel.aim.power * WORLD.speedScale;
  return {
    x: barrel.tipX,
    y: barrel.tipY,
    vx: barrel.vectorX * speed,
    vy: barrel.vectorY * speed,
    age: 0,
    wind: finiteOr(wind, 0),
    shooter: playerIndex === 1 ? 1 : 0,
  };
}

function advanceProjectile(projectile, deltaSeconds) {
  projectile.vx += projectile.wind * WORLD.windScale * deltaSeconds;
  projectile.vy += WORLD.gravity * deltaSeconds;
  projectile.x += projectile.vx * deltaSeconds;
  projectile.y += projectile.vy * deltaSeconds;
  projectile.age += deltaSeconds;
}

function terrainCollision(terrain, previousX, previousY, projectile) {
  const distance = Math.hypot(projectile.x - previousX, projectile.y - previousY);
  const samples = Math.max(1, Math.ceil(distance / 3));

  for (let sample = 1; sample <= samples; sample += 1) {
    const amount = sample / samples;
    const x = previousX + (projectile.x - previousX) * amount;
    const y = previousY + (projectile.y - previousY) * amount;

    if (
      x >= 0 &&
      x <= WORLD.width &&
      y + WORLD.projectileRadius >= terrainHeightAt(terrain, x)
    ) {
      return {
        x,
        y: terrainHeightAt(terrain, x) - WORLD.projectileRadius,
      };
    }
  }

  return null;
}

function projectileOutOfBounds(projectile) {
  return (
    projectile.x < -90 ||
    projectile.x > WORLD.width + 90 ||
    projectile.y > WORLD.height + 80 ||
    projectile.age > WORLD.maxShotTime
  );
}

function traceCandidate({ terrain, tanks, shooterIndex, angle, power, wind }) {
  const projectile = createProjectile(
    terrain,
    shooterIndex,
    { angle, power },
    wind,
  );
  const targetIndex = shooterIndex === 0 ? 1 : 0;
  const target = tanks[targetIndex];
  let closestDistance = Number.POSITIVE_INFINITY;

  for (let step = 0; step < WORLD.maxShotTime * 60; step += 1) {
    const previousX = projectile.x;
    const previousY = projectile.y;
    advanceProjectile(projectile, 1 / 60);

    const distanceSquared = pointToSegmentDistanceSquared(
      target.x,
      target.y,
      previousX,
      previousY,
      projectile.x,
      projectile.y,
    );
    closestDistance = Math.min(closestDistance, Math.sqrt(distanceSquared));

    if (
      distanceSquared <=
      (WORLD.tankRadius + WORLD.projectileRadius) ** 2
    ) {
      return 0;
    }

    const terrainHit = terrainCollision(
      terrain,
      previousX,
      previousY,
      projectile,
    );
    if (terrainHit) {
      return Math.min(
        closestDistance,
        Math.hypot(terrainHit.x - target.x, terrainHit.y - target.y),
      );
    }

    if (projectileOutOfBounds(projectile)) {
      break;
    }
  }

  return closestDistance;
}

export function chooseComputerAim({
  terrain,
  tanks,
  shooterIndex = 1,
  wind = 0,
  random = Math.random,
}) {
  const sample = typeof random === "function" ? random : Math.random;
  const estimatedWind = wind + (sample() * 2 - 1) * 6;
  let best = { angle: 45, power: 72, score: Number.POSITIVE_INFINITY };

  const consider = (angle, power) => {
    if (
      angle < WORLD.minAngle ||
      angle > WORLD.maxAngle ||
      power < WORLD.minPower ||
      power > WORLD.maxPower
    ) {
      return;
    }

    const score = traceCandidate({
      terrain,
      tanks,
      shooterIndex,
      angle,
      power,
      wind: estimatedWind,
    });
    if (score < best.score) {
      best = { angle, power, score };
    }
  };

  for (let angle = 18; angle <= 80; angle += 4) {
    for (let power = 32; power <= 100; power += 4) {
      consider(angle, power);
    }
  }

  const coarseBest = best;
  for (let angle = coarseBest.angle - 4; angle <= coarseBest.angle + 4; angle += 1) {
    for (let power = coarseBest.power - 6; power <= coarseBest.power + 6; power += 1) {
      consider(angle, power);
    }
  }

  const accuracyRoll = sample();
  const spread = accuracyRoll < 0.1 ? 0.5 : accuracyRoll > 0.75 ? 2 : 1.35;
  const angleError = (sample() * 2 - 1) * 6 * spread;
  const powerError = ((sample() * 2 - 1) * 10 - 2.5) * spread;
  const aim = normalizeAim(best.angle + angleError, best.power + powerError);

  return Object.freeze({
    ...aim,
    solutionDistance: best.score,
    estimatedWind,
  });
}

function createTanks(terrain) {
  return TANK_X.map((x, index) => ({
    id: index,
    x,
    y: terrainHeightAt(terrain, x) - WORLD.tankHalfHeight,
    health: 100,
  }));
}

export class ArtilleryGame {
  constructor(random = Math.random) {
    this.random = typeof random === "function" ? random : Math.random;
    this.events = [];
    this.terrain = createTerrain(this.random);
    this.tanks = createTanks(this.terrain);
    this.aims = [normalizeAim(45, 72), normalizeAim(45, 72)];
    this.activePlayer = 0;
    this.wind = randomWind(this.random);
    this.phase = "ready";
    this.projectile = null;
    this.lastImpact = null;
    this.resolutionTime = 0;
  }

  get currentAim() {
    return this.aims[this.activePlayer];
  }

  start(firstPlayer = 0) {
    this.terrain = createTerrain(this.random);
    this.tanks = createTanks(this.terrain);
    this.aims = [normalizeAim(45, 72), normalizeAim(45, 72)];
    this.activePlayer = firstPlayer === 1 ? 1 : 0;
    this.wind = randomWind(this.random);
    this.phase = "aiming";
    this.projectile = null;
    this.lastImpact = null;
    this.resolutionTime = 0;
    this.events.length = 0;
    this.events.push({
      type: "started",
      player: this.activePlayer,
      wind: this.wind,
    });
  }

  setAim(angle, power) {
    if (this.phase !== "aiming") {
      return this.currentAim;
    }

    this.aims[this.activePlayer] = normalizeAim(angle, power);
    return this.currentAim;
  }

  fire() {
    if (this.phase !== "aiming") {
      return false;
    }

    const shooter = this.activePlayer;
    const aim = this.currentAim;
    this.projectile = createProjectile(this.terrain, shooter, aim, this.wind);
    this.lastImpact = null;
    this.phase = "projectile";
    this.events.push({
      type: "fired",
      player: shooter,
      aim,
      wind: this.wind,
      projectile: { ...this.projectile },
    });
    return true;
  }

  update(deltaSeconds) {
    if (!Number.isFinite(deltaSeconds) || deltaSeconds <= 0) {
      return;
    }

    let remaining = Math.min(deltaSeconds, 0.12);
    while (remaining > 0) {
      const step = Math.min(FIXED_STEP, remaining);
      this.#step(step);
      remaining -= step;
    }
  }

  consumeEvents() {
    return this.events.splice(0);
  }

  #step(deltaSeconds) {
    if (this.phase === "projectile" && this.projectile) {
      this.#stepProjectile(deltaSeconds);
      return;
    }

    if (this.phase === "resolving") {
      this.resolutionTime += deltaSeconds;
      if (this.resolutionTime >= WORLD.explosionDuration) {
        this.#finishResolution();
      }
    }
  }

  #stepProjectile(deltaSeconds) {
    const projectile = this.projectile;
    const previousX = projectile.x;
    const previousY = projectile.y;
    advanceProjectile(projectile, deltaSeconds * WORLD.projectileTimeScale);

    for (let index = 0; index < this.tanks.length; index += 1) {
      if (index === projectile.shooter && projectile.age < 0.28) {
        continue;
      }

      const tank = this.tanks[index];
      if (
        pointToSegmentDistanceSquared(
          tank.x,
          tank.y,
          previousX,
          previousY,
          projectile.x,
          projectile.y,
        ) <=
        (WORLD.tankRadius + WORLD.projectileRadius) ** 2
      ) {
        this.#beginResolution({
          kind: "tank",
          x: projectile.x,
          y: projectile.y,
          directTank: index,
        });
        return;
      }
    }

    const terrainHit = terrainCollision(
      this.terrain,
      previousX,
      previousY,
      projectile,
    );
    if (terrainHit) {
      this.#beginResolution({ kind: "terrain", ...terrainHit, directTank: null });
      return;
    }

    if (projectileOutOfBounds(projectile)) {
      this.#beginResolution({
        kind: "out",
        x: clamp(projectile.x, 0, WORLD.width),
        y: clamp(projectile.y, -80, WORLD.height),
        directTank: null,
      });
    }
  }

  #beginResolution(impact) {
    const shooter = this.activePlayer;
    const tankPositions = this.tanks.map((tank) => ({ x: tank.x, y: tank.y }));
    const tankGroundHeights = this.tanks.map(
      (tank) => tank.y + WORLD.tankHalfHeight,
    );
    const damages = this.tanks.map((tank, index) => {
      if (impact.kind === "out") {
        return 0;
      }
      if (impact.directTank === index) {
        return WORLD.directDamage;
      }

      const distance = Math.hypot(
        impact.x - tankPositions[index].x,
        impact.y - tankPositions[index].y,
      );
      return Math.round(
        52 * Math.max(0, 1 - distance / WORLD.blastRadius),
      );
    });

    damages.forEach((damage, index) => {
      this.tanks[index].health = Math.max(0, this.tanks[index].health - damage);
    });

    if (impact.kind !== "out") {
      deformTerrain(this.terrain, impact.x);
      this.tanks.forEach((tank, index) => {
        flattenTankPad(this.terrain, tank.x, tankGroundHeights[index]);
        tank.y = tankGroundHeights[index] - WORLD.tankHalfHeight;
      });
    }

    this.projectile = null;
    this.phase = "resolving";
    this.resolutionTime = 0;
    this.lastImpact = {
      ...impact,
      shooter,
      damages,
    };
    this.events.push({ type: "impact", ...this.lastImpact });
  }

  #finishResolution() {
    const defeated = this.tanks.findIndex((tank) => tank.health <= 0);
    if (defeated !== -1) {
      const winner = defeated === 0 ? 1 : 0;
      this.phase = "gameover";
      this.events.push({ type: "gameover", winner, defeated });
      return;
    }

    this.activePlayer = this.activePlayer === 0 ? 1 : 0;
    this.wind = randomWind(this.random);
    this.phase = "aiming";
    this.lastImpact = null;
    this.events.push({
      type: "turn",
      player: this.activePlayer,
      wind: this.wind,
    });
  }
}
