export const WORLD = Object.freeze({
  width: 800,
  height: 600,
});

export const TRACK = Object.freeze({
  halfWidth: 58,
  lapCount: 3,
  finishT: 0,
});

export const CAR = Object.freeze({
  length: 15,
  width: 9,
  radius: 8,
  maxSpeed: 248,
  accel: 520,
  brake: 760,
  drag: 1.35,
  grip: 7.2,
  steerRate: 3.45,
  wallBounce: 0.38,
  bumpStrength: 0.55,
});

export const RACE = Object.freeze({
  countdownSeconds: 3,
  minSpeedForLap: 28,
});

// Closed circuit: long straights, a hairpin, esses, and a loop around the carpet pile.
const CONTROL_POINTS = Object.freeze([
  [500, 520],
  [640, 508],
  [730, 450],
  [748, 340],
  [690, 175],
  [530, 92],
  [350, 98],
  [190, 175],
  [118, 285],
  [165, 395],
  [285, 468],
  [410, 512],
]);

const clamp = (value, min, max) => Math.min(max, Math.max(min, value));

function catmullRom(p0, p1, p2, p3, t) {
  const t2 = t * t;
  const t3 = t2 * t;
  return {
    x:
      0.5 *
      (2 * p1[0] +
        (-p0[0] + p2[0]) * t +
        (2 * p0[0] - 5 * p1[0] + 4 * p2[0] - p3[0]) * t2 +
        (-p0[0] + 3 * p1[0] - 3 * p2[0] + p3[0]) * t3),
    y:
      0.5 *
      (2 * p1[1] +
        (-p0[1] + p2[1]) * t +
        (2 * p0[1] - 5 * p1[1] + 4 * p2[1] - p3[1]) * t2 +
        (-p0[1] + 3 * p1[1] - 3 * p2[1] + p3[1]) * t3),
  };
}

function buildCenterline(samplesPerSegment = 10) {
  const count = CONTROL_POINTS.length;
  const points = [];

  for (let index = 0; index < count; index += 1) {
    const p0 = CONTROL_POINTS[(index - 1 + count) % count];
    const p1 = CONTROL_POINTS[index];
    const p2 = CONTROL_POINTS[(index + 1) % count];
    const p3 = CONTROL_POINTS[(index + 2) % count];

    for (let step = 0; step < samplesPerSegment; step += 1) {
      const t = step / samplesPerSegment;
      const sample = catmullRom(p0, p1, p2, p3, t);
      const previous = points.at(-1);
      if (previous && Math.hypot(sample.x - previous.x, sample.y - previous.y) < 0.5) {
        continue;
      }
      points.push(sample);
    }
  }

  let totalLength = 0;
  for (let index = 0; index < points.length; index += 1) {
    const next = points[(index + 1) % points.length];
    const length = Math.hypot(next.x - points[index].x, next.y - points[index].y);
    points[index].segmentLength = length;
    totalLength += length;
  }

  let traveled = 0;
  for (const point of points) {
    point.arc = traveled / totalLength;
    traveled += point.segmentLength;
  }

  return Object.freeze({
    points: Object.freeze(points.map((point) => Object.freeze({ ...point }))),
    length: totalLength,
  });
}

export const CENTERLINE = buildCenterline();

export function steerAxisFromDrag(startX, currentX, travel = 42) {
  if (!Number.isFinite(startX) || !Number.isFinite(currentX) || travel <= 0) {
    return 0;
  }

  return clamp((currentX - startX) / travel, -1, 1);
}

export function normalizeAngle(angle) {
  let next = angle;
  while (next > Math.PI) next -= Math.PI * 2;
  while (next < -Math.PI) next += Math.PI * 2;
  return next;
}

function pointAtIndex(index, centerline = CENTERLINE) {
  const points = centerline.points;
  const current = points[index];
  const next = points[(index + 1) % points.length];
  const tangentX = next.x - current.x;
  const tangentY = next.y - current.y;
  const length = Math.hypot(tangentX, tangentY) || 1;
  return {
    x: current.x,
    y: current.y,
    t: current.arc,
    tangentX: tangentX / length,
    tangentY: tangentY / length,
  };
}

export function centerlinePoint(t, centerline = CENTERLINE) {
  const target = ((t % 1) + 1) % 1;
  const points = centerline.points;

  for (let index = 0; index < points.length; index += 1) {
    const nextArc = points[(index + 1) % points.length].arc;
    const endArc = index === points.length - 1 ? 1 : nextArc;
    if (target >= points[index].arc && target <= endArc) {
      const span = endArc - points[index].arc || 1;
      const amount = (target - points[index].arc) / span;
      const current = points[index];
      const next = points[(index + 1) % points.length];
      const x = current.x + (next.x - current.x) * amount;
      const y = current.y + (next.y - current.y) * amount;
      const tangentX = next.x - current.x;
      const tangentY = next.y - current.y;
      const length = Math.hypot(tangentX, tangentY) || 1;
      const tx = tangentX / length;
      const ty = tangentY / length;
      return Object.freeze({
        x,
        y,
        t: target,
        angle: Math.atan2(ty, tx),
        tangentX: tx,
        tangentY: ty,
      });
    }
  }

  return pointAtIndex(0, centerline);
}

export function nearestTrackPoint(x, y, centerline = CENTERLINE) {
  const points = centerline.points;
  let best = null;

  for (let index = 0; index < points.length; index += 1) {
    const start = points[index];
    const end = points[(index + 1) % points.length];
    const dx = end.x - start.x;
    const dy = end.y - start.y;
    const lengthSquared = dx * dx + dy * dy;

    let amount = 0;
    if (lengthSquared > 0) {
      amount = clamp(((x - start.x) * dx + (y - start.y) * dy) / lengthSquared, 0, 1);
    }

    const px = start.x + dx * amount;
    const py = start.y + dy * amount;
    const distance = Math.hypot(x - px, y - py);
    const segmentLength = Math.hypot(dx, dy) || 1;
    const tangentX = dx / segmentLength;
    const tangentY = dy / segmentLength;
    const nextArc = points[(index + 1) % points.length].arc;
    const endArc = index === points.length - 1 ? 1 : nextArc;
    const span = endArc - start.arc || 1;
    const t = start.arc + amount * span;

    if (!best || distance < best.distance) {
      const normalX = distance > 0.001 ? (x - px) / distance : -tangentY;
      const normalY = distance > 0.001 ? (y - py) / distance : tangentX;
      best = {
        x: px,
        y: py,
        t,
        distance,
        tangentX,
        tangentY,
        normalX,
        normalY,
      };
    }
  }

  return best;
}

export function isOnTrack(x, y, track = TRACK, centerline = CENTERLINE) {
  const nearest = nearestTrackPoint(x, y, centerline);
  return nearest.distance <= track.halfWidth - 0.5;
}

export function progressFromPoint(x, y, centerline = CENTERLINE) {
  return nearestTrackPoint(x, y, centerline).t;
}

export function pushOntoTrack(x, y, track = TRACK, centerline = CENTERLINE) {
  const nearest = nearestTrackPoint(x, y, centerline);
  const limit = track.halfWidth - CAR.radius;
  if (nearest.distance <= limit) {
    return {
      x,
      y,
      wall: null,
      normalX: nearest.normalX,
      normalY: nearest.normalY,
    };
  }

  const penetration = nearest.distance - limit;
  return {
    x: x - nearest.normalX * penetration,
    y: y - nearest.normalY * penetration,
    wall: "edge",
    normalX: nearest.normalX,
    normalY: nearest.normalY,
  };
}

export function trackEdges(centerline = CENTERLINE, track = TRACK) {
  const inner = [];
  const outer = [];

  for (let index = 0; index < centerline.points.length; index += 1) {
    const point = pointAtIndex(index, centerline);
    const nx = -point.tangentY;
    const ny = point.tangentX;
    inner.push({
      x: point.x - nx * track.halfWidth,
      y: point.y - ny * track.halfWidth,
    });
    outer.push({
      x: point.x + nx * track.halfWidth,
      y: point.y + ny * track.halfWidth,
    });
  }

  return { inner, outer };
}

export function createCar(options = {}) {
  const {
    id,
    name,
    color,
    accent,
    isPlayer = false,
    x = 0,
    y = 0,
    angle = -Math.PI / 2,
    vx = 0,
    vy = 0,
    lap = 0,
    progress = 0,
    aiSkill = 0.72,
    aiAggression = 0.55,
  } = options;

  return {
    id,
    name,
    color,
    accent,
    isPlayer,
    x,
    y,
    angle,
    vx,
    vy,
    lap,
    progress,
    lastProgress: progress,
    finished: false,
    finishTime: null,
    position: 0,
    aiSkill,
    aiAggression,
    steerInput: 0,
    throttleInput: 0,
    boostTime: 0,
    skid: 0,
  };
}

export const DEFAULT_RACERS = Object.freeze([
  {
    id: "player",
    name: "You",
    color: "#ff3b30",
    accent: "#ffd60a",
    isPlayer: true,
    aiSkill: 0,
    aiAggression: 0,
  },
  {
    id: "volt",
    name: "Volt",
    color: "#0a84ff",
    accent: "#ffffff",
    aiSkill: 0.78,
    aiAggression: 0.62,
  },
  {
    id: "mint",
    name: "Mint",
    color: "#30d158",
    accent: "#1c4228",
    aiSkill: 0.7,
    aiAggression: 0.48,
  },
  {
    id: "sun",
    name: "Sun",
    color: "#ff9f0a",
    accent: "#5c3200",
    aiSkill: 0.84,
    aiAggression: 0.7,
  },
  {
    id: "violet",
    name: "Violet",
    color: "#bf5af2",
    accent: "#f5e0ff",
    aiSkill: 0.74,
    aiAggression: 0.58,
  },
]);

export function createGridPositions(count, centerline = CENTERLINE) {
  const start = centerlinePoint(0.97, centerline);
  const positions = [];
  for (let index = 0; index < count; index += 1) {
    const row = Math.floor(index / 2);
    const side = index % 2 === 0 ? -1 : 1;
    const lateral = side * (10 + row * 11);
    const back = row * 16;
    positions.push({
      x: start.x - start.tangentX * back - start.tangentY * lateral,
      y: start.y - start.tangentY * back + start.tangentX * lateral,
      angle: start.angle,
    });
  }
  return positions;
}

export function applyCarInputs(car, throttle, steer, deltaSeconds, constants = CAR) {
  const throttleInput = clamp(Number.isFinite(throttle) ? throttle : 0, -1, 1);
  const steerInput = clamp(Number.isFinite(steer) ? steer : 0, -1, 1);
  car.throttleInput = throttleInput;
  car.steerInput = steerInput;

  const headingX = Math.cos(car.angle);
  const headingY = Math.sin(car.angle);
  const forwardSpeed = car.vx * headingX + car.vy * headingY;
  const lateralSpeed = car.vx * -headingY + car.vy * headingX;

  const boostMultiplier =
    car.boostTime > 0 ? 1.22 + Math.min(car.boostTime, 0.35) * 0.4 : 1;
  if (car.boostTime > 0) {
    car.boostTime = Math.max(0, car.boostTime - deltaSeconds);
  }

  let nextForward = forwardSpeed;
  if (throttleInput >= 0) {
    nextForward += throttleInput * constants.accel * boostMultiplier * deltaSeconds;
  } else {
    nextForward += throttleInput * constants.brake * deltaSeconds;
  }

  const grip = constants.grip * (car.isPlayer ? 1 : 0.94 + car.aiSkill * 0.05);
  const nextLateral = lateralSpeed * Math.exp(-grip * deltaSeconds);
  car.skid = clamp(Math.abs(lateralSpeed) / 70, 0, 1);

  const speed = Math.hypot(car.vx, car.vy);
  const steerScale = clamp(speed / constants.maxSpeed, 0.22, 1);
  car.angle += steerInput * constants.steerRate * steerScale * deltaSeconds;

  const newHeadingX = Math.cos(car.angle);
  const newHeadingY = Math.sin(car.angle);
  car.vx = nextForward * newHeadingX - nextLateral * newHeadingY;
  car.vy = nextForward * newHeadingY + nextLateral * newHeadingX;

  const drag = Math.exp(-constants.drag * deltaSeconds);
  car.vx *= drag;
  car.vy *= drag;

  const nextSpeed = Math.hypot(car.vx, car.vy);
  const maxSpeed = constants.maxSpeed * boostMultiplier;
  if (nextSpeed > maxSpeed) {
    car.vx = (car.vx / nextSpeed) * maxSpeed;
    car.vy = (car.vy / nextSpeed) * maxSpeed;
  }

  car.x += car.vx * deltaSeconds;
  car.y += car.vy * deltaSeconds;
}

export function resolveTrackCollision(car, constants = CAR, track = TRACK, centerline = CENTERLINE) {
  let hit = false;

  for (let attempt = 0; attempt < 3; attempt += 1) {
    const nearest = nearestTrackPoint(car.x, car.y, centerline);
    const limit = track.halfWidth - constants.radius;
    if (nearest.distance <= limit) {
      break;
    }

    const penetration = nearest.distance - limit;
    car.x -= nearest.normalX * penetration;
    car.y -= nearest.normalY * penetration;

    const impact = car.vx * nearest.normalX + car.vy * nearest.normalY;
    if (impact > 0) {
      car.vx -= impact * (1 + constants.wallBounce) * nearest.normalX;
      car.vy -= impact * (1 + constants.wallBounce) * nearest.normalY;
    }

    hit = true;
  }

  return hit;
}

export function resolveCarCollisions(cars, constants = CAR) {
  for (let i = 0; i < cars.length; i += 1) {
    for (let j = i + 1; j < cars.length; j += 1) {
      const a = cars[i];
      const b = cars[j];
      const dx = b.x - a.x;
      const dy = b.y - a.y;
      const distance = Math.hypot(dx, dy);
      const minimum = constants.radius * 2;

      if (distance >= minimum || distance === 0) {
        continue;
      }

      const nx = dx / distance;
      const ny = dy / distance;
      const overlap = minimum - distance;
      a.x -= nx * overlap * 0.5;
      a.y -= ny * overlap * 0.5;
      b.x += nx * overlap * 0.5;
      b.y += ny * overlap * 0.5;

      const relativeNormal = (a.vx - b.vx) * nx + (a.vy - b.vy) * ny;
      if (relativeNormal <= 0) {
        continue;
      }

      const impulse = relativeNormal * constants.bumpStrength;
      a.vx -= impulse * nx;
      a.vy -= impulse * ny;
      b.vx += impulse * nx;
      b.vy += impulse * ny;
    }
  }
}

export function aiControlsForCar(car, centerline = CENTERLINE) {
  const progress = progressFromPoint(car.x, car.y, centerline);
  const speed = Math.hypot(car.vx, car.vy);
  const lookahead = clamp(0.045 + car.aiSkill * 0.04 + speed / 2400, 0.04, 0.12);
  const target = centerlinePoint((progress + lookahead) % 1, centerline);

  const desired = Math.atan2(target.y - car.y, target.x - car.x);
  const steer = clamp(normalizeAngle(desired - car.angle) / 0.75, -1, 1);

  const laneWobble = Math.sin(progress * Math.PI * 2 * 3 + car.id.length) * 0.08;
  const throttle =
    0.62 +
    car.aiSkill * 0.28 +
    car.aiAggression * 0.08 -
    Math.abs(steer) * 0.18 +
    laneWobble * 0.05;

  return {
    throttle: clamp(throttle, 0.48, 1),
    steer: clamp(steer + laneWobble * (1 - car.aiSkill), -1, 1),
  };
}

export function updateLapCounter(car, track = TRACK, race = RACE, centerline = CENTERLINE) {
  const speed = Math.hypot(car.vx, car.vy);
  car.lastProgress = car.progress;
  car.progress = progressFromPoint(car.x, car.y, centerline);

  if (car.finished || speed < race.minSpeedForLap) {
    return false;
  }

  const crossed =
    car.lastProgress > 0.82 && car.progress < 0.18 && car.lap < track.lapCount;

  if (crossed) {
    car.lap += 1;
    if (car.lap >= track.lapCount) {
      car.finished = true;
    }
    return true;
  }

  return false;
}

export function rankCars(cars) {
  const ranked = [...cars].sort((left, right) => {
    if (left.finished && right.finished) {
      return (left.finishTime ?? 0) - (right.finishTime ?? 0);
    }
    if (left.finished) {
      return -1;
    }
    if (right.finished) {
      return 1;
    }

    const leftDistance = left.lap + left.progress;
    const rightDistance = right.lap + right.progress;
    return rightDistance - leftDistance;
  });

  ranked.forEach((car, index) => {
    car.position = index + 1;
  });

  return ranked;
}

export class RCProAmGame {
  constructor(random = Math.random) {
    this.random = typeof random === "function" ? random : Math.random;
    this.phase = "ready";
    this.elapsed = 0;
    this.countdown = RACE.countdownSeconds;
    this.events = [];
    this.cars = [];
    this.playerCar = null;
    this.raceTime = 0;
  }

  start() {
    this.phase = "countdown";
    this.elapsed = 0;
    this.countdown = RACE.countdownSeconds;
    this.raceTime = 0;
    this.events.length = 0;
    this.#buildCars();
    this.events.push({ type: "started", cars: this.cars.length });
  }

  setPlayerInput(throttle, steer) {
    if (!this.playerCar || this.phase !== "racing") {
      return;
    }
    this.playerCar.throttleInput = clamp(Number.isFinite(throttle) ? throttle : 0, -1, 1);
    this.playerCar.steerInput = clamp(Number.isFinite(steer) ? steer : 0, -1, 1);
  }

  triggerBoost() {
    if (!this.playerCar || this.phase !== "racing" || this.playerCar.boostTime > 0) {
      return false;
    }
    this.playerCar.boostTime = 0.85;
    this.events.push({ type: "boost", car: this.playerCar.id });
    return true;
  }

  update(deltaSeconds) {
    if (!Number.isFinite(deltaSeconds) || deltaSeconds <= 0) {
      return;
    }

    let remaining = Math.min(deltaSeconds, 0.1);
    while (remaining > 0) {
      const step = Math.min(remaining, 1 / 120);
      this.#step(step);
      remaining -= step;
    }
  }

  consumeEvents() {
    return this.events.splice(0);
  }

  get standings() {
    return rankCars(this.cars);
  }

  #buildCars() {
    const configs = DEFAULT_RACERS.map((config) => ({ ...config }));
    const grid = createGridPositions(configs.length);
    this.cars = configs.map((config, index) =>
      createCar({
        ...config,
        x: grid[index].x,
        y: grid[index].y,
        angle: grid[index].angle,
      }),
    );
    this.playerCar = this.cars.find((car) => car.isPlayer) ?? null;
  }

  #step(deltaSeconds) {
    this.elapsed += deltaSeconds;

    if (this.phase === "countdown") {
      this.countdown -= deltaSeconds;
      if (this.countdown <= 0) {
        this.phase = "racing";
        this.events.push({ type: "go" });
      }
      return;
    }

    if (this.phase !== "racing" && this.phase !== "finished") {
      return;
    }

    this.raceTime += deltaSeconds;

    for (const car of this.cars) {
      if (car.finished) {
        continue;
      }

      if (car.isPlayer) {
        applyCarInputs(car, car.throttleInput, car.steerInput, deltaSeconds);
      } else {
        const ai = aiControlsForCar(car);
        applyCarInputs(car, ai.throttle, ai.steer, deltaSeconds);
      }

      resolveTrackCollision(car);
    }

    resolveCarCollisions(this.cars);

    for (const car of this.cars) {
      if (car.finished) {
        continue;
      }

      if (car.isPlayer) {
        resolveTrackCollision(car);
      }

      const completedLap = updateLapCounter(car);
      if (completedLap && car.lap >= TRACK.lapCount) {
        car.finishTime = this.raceTime;
        this.events.push({
          type: "finish",
          car: car.id,
          place: rankCars(this.cars).findIndex((entry) => entry.id === car.id) + 1,
          time: car.finishTime,
        });
      } else if (completedLap) {
        this.events.push({ type: "lap", car: car.id, lap: car.lap });
      }
    }

    rankCars(this.cars);

    if (this.playerCar?.finished && this.cars.every((car) => car.finished)) {
      if (this.phase !== "finished") {
        this.phase = "finished";
        this.events.push({
          type: "raceover",
          place: this.playerCar.position,
          time: this.playerCar.finishTime,
        });
      }
    } else if (this.cars.filter((car) => car.finished).length >= 1) {
      const unfinished = this.cars.filter((car) => !car.finished);
      if (unfinished.length === 1 && this.raceTime > 42) {
        const straggler = unfinished[0];
        straggler.finished = true;
        straggler.finishTime = this.raceTime;
      }
      if (this.playerCar?.finished && this.phase === "racing") {
        this.phase = "finished";
        this.events.push({
          type: "raceover",
          place: this.playerCar.position,
          time: this.playerCar.finishTime,
        });
      }
    }
  }
}
