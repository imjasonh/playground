export const WORLD = Object.freeze({
  width: 800,
  height: 600,
  cx: 400,
  cy: 300,
});

export const TRACK = Object.freeze({
  outerA: 318,
  outerB: 218,
  innerA: 168,
  innerB: 114,
  centerA: 243,
  centerB: 166,
  lapCount: 3,
  finishAngle: 0,
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
  wallBounce: 0.34,
  bumpStrength: 0.55,
});

export const RACE = Object.freeze({
  countdownSeconds: 3,
  minSpeedForLap: 28,
});

const clamp = (value, min, max) => Math.min(max, Math.max(min, value));

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

export function ellipseNorm(x, y, cx, cy, a, b) {
  const dx = (x - cx) / a;
  const dy = (y - cy) / b;
  return dx * dx + dy * dy;
}

export function isOnTrack(x, y, track = TRACK, world = WORLD) {
  const outer = ellipseNorm(
    x,
    y,
    world.cx,
    world.cy,
    track.outerA,
    track.outerB,
  );
  const inner = ellipseNorm(
    x,
    y,
    world.cx,
    world.cy,
    track.innerA,
    track.innerB,
  );
  return outer <= 1 && inner >= 1;
}

export function centerlinePoint(t, track = TRACK, world = WORLD) {
  const angle = t * Math.PI * 2;
  const tx = -Math.sin(angle);
  const ty = Math.cos(angle);
  return Object.freeze({
    x: world.cx + track.centerA * Math.cos(angle),
    y: world.cy + track.centerB * Math.sin(angle),
    angle: Math.atan2(ty, tx),
    tangentX: tx,
    tangentY: ty,
    trackAngle: angle,
  });
}

export function progressFromPoint(x, y, world = WORLD) {
  const angle = Math.atan2(y - world.cy, x - world.cx);
  return ((angle / (Math.PI * 2)) % 1 + 1) % 1;
}

export function pushOntoTrack(x, y, track = TRACK, world = WORLD) {
  const angle = Math.atan2(y - world.cy, x - world.cx);
  const cos = Math.cos(angle);
  const sin = Math.sin(angle);

  const outerDist = Math.hypot(
    (world.cx + track.outerA * cos - x),
    (world.cy + track.outerB * sin - y),
  );
  const innerDist = Math.hypot(
    (x - (world.cx + track.innerA * cos)),
    (y - (world.cy + track.innerB * sin)),
  );

  if (outerDist < innerDist) {
    const scale = 1 / Math.sqrt(
      ellipseNorm(x, y, world.cx, world.cy, track.outerA, track.outerB),
    );
    return {
      x: world.cx + track.outerA * cos * scale,
      y: world.cy + track.outerB * sin * scale,
      wall: "outer",
    };
  }

  const scale = 1 / Math.sqrt(
    ellipseNorm(x, y, world.cx, world.cy, track.innerA, track.innerB),
  );
  return {
    x: world.cx + track.innerA * cos * scale,
    y: world.cy + track.innerB * sin * scale,
    wall: "inner",
  };
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

export function createGridPositions(count, track = TRACK, world = WORLD) {
  const start = centerlinePoint(0.985, track, world);
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
  const speed = Math.hypot(car.vx, car.vy);

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

  const steerScale = clamp(speed / constants.maxSpeed, 0.22, 1);
  car.angle +=
    steerInput * constants.steerRate * steerScale * deltaSeconds;

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

export function resolveTrackCollision(car, constants = CAR, track = TRACK, world = WORLD) {
  if (isOnTrack(car.x, car.y, track, world)) {
    return false;
  }

  const corrected = pushOntoTrack(car.x, car.y, track, world);
  car.x = corrected.x;
  car.y = corrected.y;

  const normalX = Math.cos(Math.atan2(car.y - world.cy, car.x - world.cx));
  const normalY = Math.sin(Math.atan2(car.y - world.cy, car.x - world.cx));
  const impact =
    car.vx * normalX + car.vy * normalY;

  if (corrected.wall === "outer" && impact > 0) {
    car.vx -= impact * (1 + constants.wallBounce) * normalX;
    car.vy -= impact * (1 + constants.wallBounce) * normalY;
  } else if (corrected.wall === "inner" && impact < 0) {
    car.vx -= impact * (1 + constants.wallBounce) * normalX;
    car.vy -= impact * (1 + constants.wallBounce) * normalY;
  }

  return true;
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

export function aiControlsForCar(car, track = TRACK, world = WORLD) {
  const progress = progressFromPoint(car.x, car.y, world);
  const speed = Math.hypot(car.vx, car.vy);
  const lookahead = clamp(0.045 + car.aiSkill * 0.04 + speed / 2400, 0.04, 0.12);
  const target = centerlinePoint((progress + lookahead) % 1, track, world);

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

export function updateLapCounter(car, track = TRACK, race = RACE) {
  const speed = Math.hypot(car.vx, car.vy);
  car.lastProgress = car.progress;
  car.progress = progressFromPoint(car.x, car.y);

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

export function rankCars(cars, track = TRACK) {
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
