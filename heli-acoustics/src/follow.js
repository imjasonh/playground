// Follow mode: low canyon cruise with inertia, limited turn/climb rates,
// and building avoidance (climb over or steer around).

import { BUILDINGS, cityBounds } from './city.js';
import { isOccluded, rayAabb } from './occlusion.js';
import { length, sub, add, scale } from './geometry.js';

const STANDOFF = 55;
const SEARCH_RADIUS = 100;

/** Preferred cruise — well below orbit/traverse skyline flights. */
export const FOLLOW_CRUISE_Y = 42;
const FOLLOW_MIN_Y = 28;
const FOLLOW_MAX_Y = 220; // temporary climb over mid-rise blocks, then settle

const SEARCH_SPEED = 11;
const TRACK_SPEED = 17;
const HOVER_SPEED = 3;

const MAX_ACCEL = 4.5; // m/s² horizontal
const MAX_CLIMB = 6.5; // m/s up
const MAX_DESCENT = 3.5; // m/s down
const MAX_YAW_RATE = 0.9; // rad/s
const LOOKAHEAD = 70; // m
const BODY_R = 6; // m clearance radius
const ROOF_CLEAR = 14; // m above roof when climbing over
const CLIMB_BUDGET = 200; // max vertical pop for an overflight

/**
 * Low-altitude follow heli with simple rigid-body-ish flight dynamics.
 */
export class FollowFlight {
  constructor(buildings = BUILDINGS) {
    this.buildings = buildings;
    this.bounds = cityBounds(buildings);
    this.pos = [this.bounds.x0 - 50, FOLLOW_CRUISE_Y, -40];
    this.vel = [0, 0, 0];
    this.yaw = Math.PI / 2; // face +x into the city
    this.phase = 'search';
    this.angle = 0;
    this.cruiseY = FOLLOW_CRUISE_Y;
  }

  reset(listener = [0, 1.7, 0]) {
    // South-west of the district so the opening hunt is not glued to a facade.
    this.pos = [this.bounds.x0 - 50, FOLLOW_CRUISE_Y, -40];
    this.vel = [0, 0, 0];
    this.yaw = Math.PI / 2; // face +x into the city
    this.phase = 'search';
    this.angle = 0;
    this.cruiseY = FOLLOW_CRUISE_Y;
    void listener;
  }

  /**
   * @returns {{ position: number[], velocity: number[], phase: string, canSee: boolean, yaw: number }}
   */
  update(dt, listener) {
    dt = Math.max(0, Math.min(0.05, dt));
    const canSee = !isOccluded(listener, this.pos, this.buildings);
    this.phase = canSee ? 'track' : 'search';
    this.angle += dt * (this.phase === 'search' ? 0.35 : 0.06);

    let goal = pickGoal(listener, this.cruiseY, this.buildings, this.angle, this.phase, this.pos);
    goal = avoidBuildings(this.pos, this.vel, goal, this.buildings, this.cruiseY);

    const sample = integrateHeli(this, goal, dt, this.phase);
    this.pos = sample.position;
    this.vel = sample.velocity;
    this.yaw = sample.yaw;

    // Soft settle cruise altitude when clear of roofs.
    if (!buildingAt(this.pos[0], this.pos[2], this.pos[1] + 2, this.buildings)) {
      this.cruiseY += (FOLLOW_CRUISE_Y - this.cruiseY) * Math.min(1, dt * 0.25);
      this.cruiseY = clamp(this.cruiseY, FOLLOW_MIN_Y, FOLLOW_MAX_Y);
    }

    return {
      position: this.pos.slice(),
      velocity: this.vel.slice(),
      phase: this.phase,
      canSee,
      yaw: this.yaw,
    };
  }
}

/** Goal perch with LOS when possible; otherwise a slow search ring. */
export function pickGoal(listener, cruiseY, buildings, angle, phase, heliPos) {
  const clear = findClearOffset(listener, cruiseY, buildings, angle);
  if (clear) {
    if (phase === 'track') {
      const horiz = Math.hypot(heliPos[0] - listener[0], heliPos[2] - listener[2]);
      const toClear = Math.hypot(clear[0] - heliPos[0], clear[2] - heliPos[2]);
      if (horiz > STANDOFF * 0.6 && horiz < STANDOFF * 1.6 && toClear < 22) {
        return [heliPos[0], cruiseY, heliPos[2]]; // hover
      }
    }
    return [clear[0], cruiseY, clear[2]];
  }
  return [
    listener[0] + Math.cos(angle) * SEARCH_RADIUS,
    cruiseY,
    listener[2] + Math.sin(angle) * SEARCH_RADIUS,
  ];
}

/**
 * If the path to goal clips a building, climb over or steer around.
 * @returns {number[]} adjusted goal
 */
export function avoidBuildings(pos, _vel, goal, buildings, _cruiseY) {
  const toGoal = sub(goal, pos);
  const dist = length(toGoal);
  if (dist < 1) return goal;

  const dir = scale(toGoal, 1 / dist);
  let hit = firstBuildingHit(pos, dir, Math.min(dist, LOOKAHEAD), buildings);
  // Catch grazing paths that miss the ray test but would bury the next few meters.
  if (!hit) {
    const probe = add(pos, scale(dir, Math.min(28, dist)));
    const blocked = buildingAt(probe[0], probe[2], pos[1] + 1, buildings);
    if (blocked) hit = { t: 12, box: blocked };
  }
  if (!hit) return goal;

  const roof = hit.box.max[1];
  const climbTarget = Math.min(FOLLOW_MAX_Y, roof + ROOF_CLEAR);
  const climbCost = climbTarget - pos[1];
  const canClimb =
    climbCost > 0 && climbCost <= CLIMB_BUDGET && climbTarget <= FOLLOW_MAX_Y && hit.t > 5;

  const around = steerAround(pos, goal, hit.box, buildings);
  if (canClimb) {
    const over = add(pos, scale(dir, Math.max(hit.t, 8) + BODY_R + 10));
    const climbGoal = [over[0], climbTarget, over[2]];
    if (!around) return climbGoal;
    const detour =
      Math.hypot(around[0] - pos[0], around[2] - pos[2]) +
      Math.hypot(around[0] - goal[0], around[2] - goal[2]);
    const viaClimb =
      Math.hypot(climbGoal[0] - pos[0], climbGoal[2] - pos[2]) +
      Math.hypot(goal[0] - climbGoal[0], goal[2] - climbGoal[2]) +
      climbCost * 0.8;
    return viaClimb <= detour * 1.05 ? climbGoal : around;
  }
  return around || goal;
}

/** Integrate velocity with accel / climb / yaw limits (heli-like). */
export function integrateHeli(state, goal, dt, phase) {
  const pos = state.pos.slice();
  const vel = state.vel.slice();
  let yaw = state.yaw;

  const to = sub(goal, pos);
  const horizDist = Math.hypot(to[0], to[2]);
  const desiredSpeed =
    phase === 'search' ? SEARCH_SPEED : horizDist < 12 ? HOVER_SPEED : TRACK_SPEED;

  let wantYaw = yaw;
  if (horizDist > 1.5) wantYaw = Math.atan2(to[0], to[2]);
  yaw = turnToward(yaw, wantYaw, MAX_YAW_RATE * dt);

  const speed = desiredSpeed * Math.min(1, Math.max(0.2, horizDist / 35));
  const desireH = [Math.sin(yaw) * speed, Math.cos(yaw) * speed];

  let ax = desireH[0] - vel[0];
  let az = desireH[1] - vel[2];
  const aLen = Math.hypot(ax, az);
  if (aLen > MAX_ACCEL) {
    ax = (ax / aLen) * MAX_ACCEL;
    az = (az / aLen) * MAX_ACCEL;
  }
  vel[0] += ax * dt;
  vel[2] += az * dt;

  const wantY = clamp(goal[1], FOLLOW_MIN_Y, FOLLOW_MAX_Y);
  const dy = wantY - pos[1];
  let vyWant = clamp(dy * 0.7, -MAX_DESCENT, MAX_CLIMB);
  if (Math.abs(dy) < 2) vyWant *= Math.abs(dy) / 2;
  const ay = clamp(vyWant - vel[1], -3.5, 4.5);
  vel[1] += ay * dt;

  pos[0] += vel[0] * dt;
  pos[1] += vel[1] * dt;
  pos[2] += vel[2] * dt;

  const pushed = separateFromBuildings(pos, vel, state.buildings || BUILDINGS);
  return { position: pushed.pos, velocity: pushed.vel, yaw };
}

export function findClearOffset(listener, height, buildings = BUILDINGS, baseAngle = 0) {
  const radii = [STANDOFF, 80, 110, 150];
  for (let i = 0; i < 24; i++) {
    const a = baseAngle + (i / 24) * Math.PI * 2;
    for (const r of radii) {
      const p = [listener[0] + Math.cos(a) * r, height, listener[2] + Math.sin(a) * r];
      if (buildingAt(p[0], p[2], p[1], buildings)) continue;
      if (!isOccluded(listener, p, buildings)) return p;
    }
  }
  return null;
}

function firstBuildingHit(origin, dir, maxT, buildings) {
  let best = null;
  for (const b of buildings) {
    const box = {
      min: [b.min[0] - BODY_R, b.min[1], b.min[2] - BODY_R],
      max: [b.max[0] + BODY_R, b.max[1], b.max[2] + BODY_R],
    };
    const t = rayAabb(origin, dir, box);
    if (t == null || t < 0.5 || t > maxT) continue;
    const hitY = origin[1] + dir[1] * t;
    if (hitY > box.max[1] + 1) continue;
    if (hitY < box.min[1] - 1) continue;
    if (!best || t < best.t) best = { t, box: b, inflated: box };
  }
  return best;
}

function steerAround(pos, goal, box, buildings) {
  const pad = BODY_R + 22;
  const xs = [box.min[0] - pad, (box.min[0] + box.max[0]) / 2, box.max[0] + pad];
  const zs = [box.min[2] - pad, (box.min[2] + box.max[2]) / 2, box.max[2] + pad];
  const candidates = [];
  for (const x of xs) {
    for (const z of zs) {
      if (x > box.min[0] && x < box.max[0] && z > box.min[2] && z < box.max[2]) continue;
      candidates.push([x, FOLLOW_CRUISE_Y, z]);
    }
  }
  let best = null;
  let bestScore = Infinity;
  for (const c of candidates) {
    if (buildingAt(c[0], c[2], c[1], buildings)) continue;
    const score =
      Math.hypot(c[0] - pos[0], c[2] - pos[2]) + 1.1 * Math.hypot(c[0] - goal[0], c[2] - goal[2]);
    if (score < bestScore) {
      bestScore = score;
      best = c;
    }
  }
  return best;
}

function separateFromBuildings(pos, vel, buildings) {
  const p = pos.slice();
  const v = vel.slice();
  for (const b of buildings) {
    const x0 = b.min[0] - BODY_R;
    const x1 = b.max[0] + BODY_R;
    const y0 = b.min[1];
    const y1 = b.max[1] + ROOF_CLEAR * 0.25;
    const z0 = b.min[2] - BODY_R;
    const z1 = b.max[2] + BODY_R;
    if (p[0] <= x0 || p[0] >= x1 || p[1] <= y0 || p[1] >= y1 || p[2] <= z0 || p[2] >= z1) {
      continue;
    }
    const px = Math.min(p[0] - x0, x1 - p[0]);
    const py = Math.min(p[1] - y0, y1 - p[1]);
    const pz = Math.min(p[2] - z0, z1 - p[2]);
    if (px <= py && px <= pz) {
      p[0] = p[0] - x0 < x1 - p[0] ? x0 : x1;
      v[0] = 0;
    } else if (pz <= px && pz <= py) {
      p[2] = p[2] - z0 < z1 - p[2] ? z0 : z1;
      v[2] = 0;
    } else {
      p[1] = y1;
      v[1] = Math.max(v[1], 0);
    }
  }
  p[1] = clamp(p[1], FOLLOW_MIN_Y, FOLLOW_MAX_Y);
  return { pos: p, vel: v };
}

export function buildingAt(x, z, y, buildings) {
  for (const b of buildings) {
    if (
      x > b.min[0] - BODY_R &&
      x < b.max[0] + BODY_R &&
      z > b.min[2] - BODY_R &&
      z < b.max[2] + BODY_R &&
      y > b.min[1] &&
      y < b.max[1]
    ) {
      return b;
    }
  }
  return null;
}

function turnToward(yaw, want, maxStep) {
  let d = want - yaw;
  while (d > Math.PI) d -= Math.PI * 2;
  while (d < -Math.PI) d += Math.PI * 2;
  return yaw + clamp(d, -maxStep, maxStep);
}

function clamp(v, lo, hi) {
  return Math.max(lo, Math.min(hi, v));
}
