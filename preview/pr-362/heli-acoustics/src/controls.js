// First-person look + WASD move on the street plane. Pointer lock after click.

export class FpsControls {
  constructor(canvas) {
    this.canvas = canvas;
    this.yaw = 0;
    this.pitch = 0;
    this.position = [0, 1.7, 0];
    this.keys = new Set();
    this.speed = 18;
    this._onKeyDown = (e) => this.keys.add(e.code);
    this._onKeyUp = (e) => this.keys.delete(e.code);
    this._onMove = (e) => {
      if (document.pointerLockElement !== canvas) return;
      this.yaw -= e.movementX * 0.0022;
      this.pitch -= e.movementY * 0.0022;
      this.pitch = Math.max(-1.2, Math.min(1.2, this.pitch));
    };
    window.addEventListener('keydown', this._onKeyDown);
    window.addEventListener('keyup', this._onKeyUp);
    canvas.addEventListener('mousemove', this._onMove);
    canvas.addEventListener('click', () => {
      if (document.pointerLockElement !== canvas) canvas.requestPointerLock();
    });
  }

  forward() {
    const cp = Math.cos(this.pitch);
    return [Math.sin(this.yaw) * cp, Math.sin(this.pitch), -Math.cos(this.yaw) * cp];
  }

  flatForward() {
    return [Math.sin(this.yaw), 0, -Math.cos(this.yaw)];
  }

  right() {
    return [Math.cos(this.yaw), 0, Math.sin(this.yaw)];
  }

  up() {
    const f = this.forward();
    const r = this.right();
    const u = [
      r[1] * f[2] - r[2] * f[1],
      r[2] * f[0] - r[0] * f[2],
      r[0] * f[1] - r[1] * f[0],
    ];
    const len = Math.hypot(u[0], u[1], u[2]) || 1;
    return [u[0] / len, u[1] / len, u[2] / len];
  }

  update(dt) {
    const f = this.flatForward();
    const r = this.right();
    let dx = 0;
    let dz = 0;
    if (this.keys.has('KeyW')) {
      dx += f[0];
      dz += f[2];
    }
    if (this.keys.has('KeyS')) {
      dx -= f[0];
      dz -= f[2];
    }
    if (this.keys.has('KeyD')) {
      dx += r[0];
      dz += r[2];
    }
    if (this.keys.has('KeyA')) {
      dx -= r[0];
      dz -= r[2];
    }
    const len = Math.hypot(dx, dz);
    if (len > 0) {
      dx = (dx / len) * this.speed * dt;
      dz = (dz / len) * this.speed * dt;
      this.position[0] += dx;
      this.position[2] += dz;
      // Keep the player roughly in the playable district.
      this.position[0] = Math.max(-110, Math.min(110, this.position[0]));
      this.position[2] = Math.max(-110, Math.min(120, this.position[2]));
    }
  }
}
