// First-person look + WASD move. Desktop can use pointer lock; mobile and
// unlocked desktop drag on the canvas to look. Pointer events cover mouse,
// touch, and pen so a tap starts and a drag rotates.

export class FpsControls {
  constructor(canvas) {
    this.canvas = canvas;
    this.yaw = 0;
    this.pitch = 0;
    this.position = [0, 1.7, 0];
    this.keys = new Set();
    this.speed = 18;
    this.lookSensitivity = 0.0025;
    this.dragging = false;
    this.lastX = 0;
    this.lastY = 0;

    this._onKeyDown = (e) => this.keys.add(e.code);
    this._onKeyUp = (e) => this.keys.delete(e.code);

    this._onPointerDown = (e) => {
      if (e.pointerType === 'mouse' && e.button !== 0) return;
      this.dragging = true;
      this.lastX = e.clientX;
      this.lastY = e.clientY;
      try {
        canvas.setPointerCapture(e.pointerId);
      } catch {
        /* ignore */
      }
      // Fine pointers get pointer lock for continuous look; coarse (phones)
      // keep drag-to-look because pointer lock is unreliable or absent.
      if (e.pointerType === 'mouse' && !coarsePointer()) {
        canvas.requestPointerLock?.();
      }
    };

    this._onPointerMove = (e) => {
      if (document.pointerLockElement === canvas) {
        this.#look(e.movementX, e.movementY);
        return;
      }
      if (!this.dragging) return;
      const dx = e.clientX - this.lastX;
      const dy = e.clientY - this.lastY;
      this.lastX = e.clientX;
      this.lastY = e.clientY;
      this.#look(dx, dy);
    };

    this._onPointerUp = (e) => {
      this.dragging = false;
      try {
        canvas.releasePointerCapture(e.pointerId);
      } catch {
        /* ignore */
      }
    };

    window.addEventListener('keydown', this._onKeyDown);
    window.addEventListener('keyup', this._onKeyUp);
    canvas.addEventListener('pointerdown', this._onPointerDown);
    canvas.addEventListener('pointermove', this._onPointerMove);
    canvas.addEventListener('pointerup', this._onPointerUp);
    canvas.addEventListener('pointercancel', this._onPointerUp);
    // Stop the browser from scrolling / zooming while dragging on the canvas.
    canvas.addEventListener(
      'touchmove',
      (e) => {
        e.preventDefault();
      },
      { passive: false },
    );
  }

  #look(dx, dy) {
    this.yaw -= dx * this.lookSensitivity;
    this.pitch -= dy * this.lookSensitivity;
    this.pitch = Math.max(-1.2, Math.min(1.2, this.pitch));
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
      this.position[0] = Math.max(-110, Math.min(110, this.position[0]));
      this.position[2] = Math.max(-110, Math.min(120, this.position[2]));
    }
  }
}

export function coarsePointer() {
  return typeof window !== 'undefined' && window.matchMedia('(pointer: coarse)').matches;
}
