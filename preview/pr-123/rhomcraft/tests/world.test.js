import test from "node:test";
import assert from "node:assert/strict";

import { AIR, PLACEABLE } from "../src/blocks.js";
import { Game } from "../src/game.js";
import { countExposedFaces, meshWorld } from "../src/mesher.js";
import { World } from "../src/world.js";
import { isFccCell } from "../src/rhombic.js";

test("world generation fills only FCC cells", () => {
  const world = new World({ seed: 7, radius: 8, height: 12 }).generate();
  assert.ok(world.cells.size > 100);
  for (const key of world.cells.keys()) {
    const [x, y, z] = key.split(",").map(Number);
    assert.equal(isFccCell(x, y, z), true);
  }
});

test("break and place round-trip on a surface cell", () => {
  const world = new World({ seed: 3, radius: 10, height: 12 }).generate();
  const spawn = world.findSpawn();
  // dig downward from near spawn
  let target = null;
  for (let y = Math.floor(spawn.y); y >= 0; y--) {
    const x = Math.round(spawn.x);
    const z = Math.round(spawn.z);
    if (isFccCell(x, y, z) && world.hasSolid(x, y, z)) {
      target = [x, y, z];
      break;
    }
  }
  assert.ok(target);
  const [tx, ty, tz] = target;
  const before = world.get(tx, ty, tz);
  assert.notEqual(before, AIR);
  assert.equal(world.breakBlock(tx, ty, tz), before);
  assert.equal(world.get(tx, ty, tz), AIR);
  assert.equal(world.placeBlock(tx, ty, tz, 3), true);
  assert.equal(world.get(tx, ty, tz), 3);
});

test("raycast from above hits terrain", () => {
  const world = new World({ seed: 11, radius: 10, height: 14 }).generate();
  const hit = world.raycast(0, 20, 0, 0, -1, 0, 30);
  assert.equal(hit.hit, true);
  assert.ok(world.hasSolid(hit.x, hit.y, hit.z));
  assert.equal(isFccCell(hit.px, hit.py, hit.pz), true);
});

test("mesher emits vertices only for exposed faces", () => {
  const world = new World({ seed: 5, radius: 6, height: 10 }).generate();
  const faces = countExposedFaces(world);
  const mesh = meshWorld(world);
  // each face → 2 tris → 6 verts
  assert.equal(mesh.vertexCount, faces * 6);
  assert.ok(mesh.vertexCount > 0);
  assert.equal(mesh.positions.length, mesh.vertexCount * 3);
  assert.equal(mesh.colors.length, mesh.vertexCount * 3);
});

test("game hotbar selection and dig stats", () => {
  const game = new Game({ world: { seed: 9, radius: 8, height: 12 } });
  assert.equal(game.hotbar.length, PLACEABLE.length);
  game.selectSlot(2);
  assert.equal(game.selectedBlock, PLACEABLE[2]);
  game.cycleSlot(1);
  assert.equal(game.selected, 3);

  // Stand above a known solid column and look straight down
  game.player.x = 0;
  game.player.y = 10;
  game.player.z = 0;
  game.player.yaw = 0;
  game.player.pitch = -Math.PI / 2 + 0.01;
  const broken = game.breakTarget();
  assert.ok(broken);
  assert.equal(game.stats.breaks, 1);
});

test("player update moves with WASD intent", () => {
  const game = new Game({ world: { seed: 2, radius: 8, height: 10 } });
  const z0 = game.player.z;
  game.player.yaw = 0;
  game.update({ forward: 1, strafe: 0, jump: false, sprint: false }, 0.2);
  // yaw 0 ⇒ forward is −Z
  assert.ok(game.player.z < z0);
});
