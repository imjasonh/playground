import { FACE_NEIGHBORS, nearestFcc, rhombicRadii } from "./rhombic.js";

const { inRadius } = rhombicRadii();

/**
 * First-person player with gravity, jump, and FCC soft collision.
 */
export class Player {
  constructor(spawn = { x: 0, y: 10, z: 0 }) {
    this.x = spawn.x;
    this.y = spawn.y;
    this.z = spawn.z;
    this.vx = 0;
    this.vy = 0;
    this.vz = 0;
    this.yaw = 0;
    this.pitch = -0.2;
    this.eyeHeight = 1.45;
    this.radius = inRadius * 0.72;
    this.onGround = false;
    this.speed = 6.5;
    this.jumpSpeed = 7.2;
    this.gravity = 18;
  }

  get eye() {
    return { x: this.x, y: this.y + this.eyeHeight, z: this.z };
  }

  lookDir() {
    const cp = Math.cos(this.pitch);
    return {
      x: Math.sin(this.yaw) * cp,
      y: Math.sin(this.pitch),
      z: -Math.cos(this.yaw) * cp,
    };
  }

  addLook(dx, dy, sensitivity = 0.0022) {
    this.yaw += dx * sensitivity;
    this.pitch -= dy * sensitivity;
    const lim = Math.PI / 2 - 0.05;
    this.pitch = Math.max(-lim, Math.min(lim, this.pitch));
  }

  /**
   * @param {object} input { forward, strafe, jump, sprint }
   * @param {import('./world.js').World} world
   * @param {number} dt
   */
  update(input, world, dt) {
    const dir = this.lookDir();
    const forwardX = Math.sin(this.yaw);
    const forwardZ = -Math.cos(this.yaw);
    const rightX = Math.cos(this.yaw);
    const rightZ = Math.sin(this.yaw);

    let wishX = forwardX * input.forward + rightX * input.strafe;
    let wishZ = forwardZ * input.forward + rightZ * input.strafe;
    const wishLen = Math.hypot(wishX, wishZ);
    if (wishLen > 1e-6) {
      wishX /= wishLen;
      wishZ /= wishLen;
    }

    const speed = input.sprint ? this.speed * 1.55 : this.speed;
    this.vx = wishX * speed;
    this.vz = wishZ * speed;

    if (input.jump && this.onGround) {
      this.vy = this.jumpSpeed;
      this.onGround = false;
    }

    this.vy -= this.gravity * dt;

    this.moveAxis(world, this.vx * dt, 0, 0);
    this.moveAxis(world, 0, 0, this.vz * dt);
    this.moveAxis(world, 0, this.vy * dt, 0);

    // keep above void
    if (this.y < -20) {
      const spawn = world.findSpawn();
      this.x = spawn.x;
      this.y = spawn.y;
      this.z = spawn.z;
      this.vx = this.vy = this.vz = 0;
    }

    return dir;
  }

  moveAxis(world, dx, dy, dz) {
    this.x += dx;
    this.y += dy;
    this.z += dz;

    const collided = this.resolveCollision(world);
    if (dy !== 0 && collided) {
      if (dy < 0) this.onGround = true;
      this.vy = 0;
    } else if (dy < 0) {
      this.onGround = false;
    }
  }

  /** Soft collision against nearby solid rhombic cells. */
  resolveCollision(world) {
    let hit = false;
    const samples = [
      [0, 0.2, 0],
      [0, 0.9, 0],
      [0, 1.5, 0],
    ];

    for (const [ox, oy, oz] of samples) {
      const px = this.x + ox;
      const py = this.y + oy;
      const pz = this.z + oz;
      const [cx, cy, cz] = nearestFcc(px, py, pz);
      const candidates = [[cx, cy, cz]];
      for (const [dx, dy, dz] of FACE_NEIGHBORS) {
        candidates.push([cx + dx, cy + dy, cz + dz]);
      }

      for (const [sx, sy, sz] of candidates) {
        if (!world.hasSolid(sx, sy, sz)) continue;
        const dx = px - sx;
        const dy = py - sy;
        const dz = pz - sz;
        const dist = Math.hypot(dx, dy, dz);
        const minDist = this.radius + inRadius * 0.85;
        if (dist < minDist && dist > 1e-6) {
          const push = (minDist - dist) / dist;
          this.x += dx * push;
          this.y += dy * push * 0.35; // prefer horizontal separation
          this.z += dz * push;
          hit = true;
        } else if (dist <= 1e-6) {
          this.y += 0.1;
          hit = true;
        }
      }
    }
    return hit;
  }
}
