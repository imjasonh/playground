// Follow mode: hover / crawl until line-of-sight, then track the listener.

import { BUILDINGS, cityBounds } from './city.js';
import { isOccluded } from './occlusion.js';
import { length, sub } from './geometry.js';

const SEARCH_SPEED = 9; // m/s — slow hunt
const TRACK_SPEED = 18; // m/s — keep up when you move
const STANDOFF = 70; // m preferred horizontal range when tracking
const SEARCH_RADIUS = 130;
/** Cruise below the tallest towers so facade occlusion still matters. */
const FOLLOW_HEIGHT = 200;

/**
 * Stateful heli that searches for a clear sightline, then follows the player.
 * Flies over shorter blocks; tall towers can still break LOS during the hunt.
 */
export class FollowFlight {
  constructor(buildings = BUILDINGS) {
    this.buildings = buildings;
    this.bounds = cityBounds(buildings);
    this.height = FOLLOW_HEIGHT;
    this.pos = [this.bounds.x0 - 50, this.height, 90];
    this.vel = [0, 0, 0];
    this.phase = 'search'; // 'search' | 'track'
    this.angle = 0;
  }

  reset(listener = [0, 1.7, 0]) {
    this.height = FOLLOW_HEIGHT;
    // Start west of the NW tower so the avenue does not give free LOS.
    this.pos = [this.bounds.x0 - 50, this.height, 90];
    this.vel = [0, 0, 0];
    this.phase = 'search';
    this.angle = 0;
  }

  /** @returns {{ position: number[], velocity: number[], phase: string, canSee: boolean }} */
  update(dt, listener) {
    const canSee = !isOccluded(listener, this.pos, this.buildings);
    this.phase = canSee ? 'track' : 'search';
    this.angle += dt * (this.phase === 'search' ? 0.45 : 0.08);

    // Vantage is always relative to the *current* listener pose.
    let target = findClearOffset(listener, this.height, this.buildings, this.angle);
    if (!target) {
      target = [
        listener[0] + Math.cos(this.angle) * SEARCH_RADIUS,
        this.height,
        listener[2] + Math.sin(this.angle) * SEARCH_RADIUS,
      ];
    }

    if (this.phase === 'track' && canSee) {
      const horiz = Math.hypot(this.pos[0] - listener[0], this.pos[2] - listener[2]);
      const toTarget = Math.hypot(target[0] - this.pos[0], target[2] - this.pos[2]);
      // Hover on a good perch; chase when the listener walked away.
      if (horiz > STANDOFF * 0.65 && horiz < STANDOFF * 1.5 && toTarget < 28) {
        target = this.pos.slice();
      }
    }

    const speed = this.phase === 'search' ? SEARCH_SPEED : TRACK_SPEED;
    const to = sub(target, this.pos);
    const dist = length(to);
    if (dist < 0.05) {
      this.vel = [0, 0, 0];
    } else {
      const step = Math.min(dist, speed * Math.max(0, dt));
      const ux = to[0] / dist;
      const uy = to[1] / dist;
      const uz = to[2] / dist;
      this.pos = [this.pos[0] + ux * step, this.pos[1] + uy * step, this.pos[2] + uz * step];
      this.vel = [ux * speed, uy * speed, uz * speed];
      this.pos[1] = this.height;
      this.vel[1] = 0;
    }

    return {
      position: this.pos.slice(),
      velocity: this.vel.slice(),
      phase: this.phase,
      canSee,
    };
  }
}

/** Sample ring offsets; return the first with clear LOS to the listener. */
export function findClearOffset(listener, height, buildings = BUILDINGS, baseAngle = 0) {
  const radii = [STANDOFF, 90, 120, 160, 200];
  for (let i = 0; i < 24; i++) {
    const a = baseAngle + (i / 24) * Math.PI * 2;
    for (const r of radii) {
      const p = [listener[0] + Math.cos(a) * r, height, listener[2] + Math.sin(a) * r];
      if (!isOccluded(listener, p, buildings)) return p;
    }
  }
  return null;
}
