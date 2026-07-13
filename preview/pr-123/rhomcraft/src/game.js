import { PLACEABLE } from "./blocks.js";
import { World } from "./world.js";
import { Player } from "./player.js";

/**
 * Headless game state used by the renderer and unit tests.
 */
export class Game {
  constructor(options = {}) {
    this.world = new World(options.world);
    this.world.generate();
    const spawn = options.spawn ?? this.world.findSpawn();
    this.player = new Player(spawn);
    this.hotbar = [...PLACEABLE];
    this.selected = 0;
    this.stats = { breaks: 0, places: 0 };
  }

  get selectedBlock() {
    return this.hotbar[this.selected];
  }

  selectSlot(index) {
    if (index < 0 || index >= this.hotbar.length) return this.selected;
    this.selected = index;
    return this.selected;
  }

  cycleSlot(delta) {
    const n = this.hotbar.length;
    this.selected = ((this.selected + delta) % n + n) % n;
    return this.selected;
  }

  /**
   * @param {{ forward: number, strafe: number, jump: boolean, sprint: boolean }} input
   */
  update(input, dt) {
    this.player.update(input, this.world, dt);
  }

  lookRay(maxDist = 10) {
    const eye = this.player.eye;
    const dir = this.player.lookDir();
    return this.world.raycast(eye.x, eye.y, eye.z, dir.x, dir.y, dir.z, maxDist);
  }

  breakTarget() {
    const hit = this.lookRay();
    if (!hit.hit) return null;
    const id = this.world.breakBlock(hit.x, hit.y, hit.z);
    if (id) this.stats.breaks += 1;
    return { ...hit, id };
  }

  placeTarget() {
    const hit = this.lookRay();
    if (!hit.hit) return null;
    // Don't place inside the player
    const eye = this.player.eye;
    const dx = hit.px - this.player.x;
    const dy = hit.py - this.player.y;
    const dz = hit.pz - this.player.z;
    if (Math.hypot(dx, dy, dz) < 1.6) return null;
    if (Math.hypot(hit.px - eye.x, hit.py - eye.y, hit.pz - eye.z) < 0.8) return null;

    const ok = this.world.placeBlock(hit.px, hit.py, hit.pz, this.selectedBlock);
    if (ok) this.stats.places += 1;
    return ok ? { x: hit.px, y: hit.py, z: hit.pz, id: this.selectedBlock } : null;
  }
}
