import * as THREE from "three";
import { BLOCKS } from "./blocks.js";
import { Game } from "./game.js";
import { meshWorld } from "./mesher.js";
import { MESH_SCALE, RHOMBIC_FACES, RHOMBIC_VERTICES } from "./rhombic.js";

const canvas = document.getElementById("viewport");
const overlay = document.getElementById("overlay");
const hintEl = document.getElementById("hint");
const coordsEl = document.getElementById("coords");
const targetEl = document.getElementById("target");
const hotbarEl = document.getElementById("hotbar");
const fpsEl = document.getElementById("fps");

const isTouch = matchMedia("(pointer: coarse)").matches;

const game = new Game({ world: { seed: 2026, radius: isTouch ? 20 : 26, height: 18 } });

const renderer = new THREE.WebGLRenderer({
  canvas,
  antialias: true,
  powerPreference: "high-performance",
});
renderer.setPixelRatio(Math.min(devicePixelRatio, 2));
renderer.setClearColor(0x7ec8e3, 1);
renderer.outputColorSpace = THREE.SRGBColorSpace;

const scene = new THREE.Scene();
scene.fog = new THREE.Fog(0x9fd0e8, 28, 72);

const camera = new THREE.PerspectiveCamera(72, 1, 0.08, 200);
scene.add(camera);

const hemi = new THREE.HemisphereLight(0xcfefff, 0x3a4a28, 1.05);
scene.add(hemi);
const sun = new THREE.DirectionalLight(0xfff2d6, 1.15);
sun.position.set(40, 80, 20);
scene.add(sun);

const worldGroup = new THREE.Group();
scene.add(worldGroup);

const terrainMat = new THREE.MeshLambertMaterial({ vertexColors: true });
let terrainMesh = null;
let meshVersion = -1;

function rebuildMesh() {
  if (meshVersion === game.world.version) return;
  meshVersion = game.world.version;
  const data = meshWorld(game.world);
  const geo = new THREE.BufferGeometry();
  geo.setAttribute("position", new THREE.BufferAttribute(data.positions, 3));
  geo.setAttribute("normal", new THREE.BufferAttribute(data.normals, 3));
  geo.setAttribute("color", new THREE.BufferAttribute(data.colors, 3));
  if (terrainMesh) {
    worldGroup.remove(terrainMesh);
    terrainMesh.geometry.dispose();
  }
  terrainMesh = new THREE.Mesh(geo, terrainMat);
  worldGroup.add(terrainMesh);
}

const outlineMat = new THREE.LineBasicMaterial({
  color: 0xffffff,
  transparent: true,
  opacity: 0.85,
});
const outlineGeo = new THREE.BufferGeometry();
const outline = new THREE.LineSegments(outlineGeo, outlineMat);
outline.visible = false;
scene.add(outline);

function makeOutlinePositions(x, y, z) {
  const positions = [];
  const scale = MESH_SCALE;
  for (let f = 0; f < 12; f++) {
    const idx = RHOMBIC_FACES[f];
    for (let e = 0; e < 4; e++) {
      const a = RHOMBIC_VERTICES[idx[e]];
      const b = RHOMBIC_VERTICES[idx[(e + 1) % 4]];
      positions.push(
        x + a[0] * scale,
        y + a[1] * scale,
        z + a[2] * scale,
        x + b[0] * scale,
        y + b[1] * scale,
        z + b[2] * scale,
      );
    }
  }
  return new Float32Array(positions);
}

function updateOutline(hit) {
  if (!hit?.hit) {
    outline.visible = false;
    targetEl.textContent = "—";
    return;
  }
  outlineGeo.setAttribute("position", new THREE.BufferAttribute(makeOutlinePositions(hit.x, hit.y, hit.z), 3));
  outlineGeo.computeBoundingSphere();
  outline.visible = true;
  const id = game.world.get(hit.x, hit.y, hit.z);
  targetEl.textContent = `${BLOCKS[id]?.name ?? "?"} (${hit.x},${hit.y},${hit.z})`;
}

// Ghost preview for placement
const ghostMat = new THREE.MeshBasicMaterial({
  color: 0xffffff,
  transparent: true,
  opacity: 0.22,
  depthWrite: false,
});
const ghostGeo = buildUnitRhombicGeometry();
const ghost = new THREE.Mesh(ghostGeo, ghostMat);
ghost.visible = false;
scene.add(ghost);

function buildUnitRhombicGeometry() {
  const positions = [];
  const scale = MESH_SCALE * 0.98;
  for (let f = 0; f < 12; f++) {
    const [i0, i1, i2, i3] = RHOMBIC_FACES[f];
    for (const [a, b, c] of [
      [i0, i1, i2],
      [i0, i2, i3],
    ]) {
      for (const vi of [a, b, c]) {
        const [vx, vy, vz] = RHOMBIC_VERTICES[vi];
        positions.push(vx * scale, vy * scale, vz * scale);
      }
    }
  }
  const geo = new THREE.BufferGeometry();
  geo.setAttribute("position", new THREE.Float32BufferAttribute(positions, 3));
  geo.computeVertexNormals();
  return geo;
}

function resize() {
  const w = canvas.clientWidth;
  const h = canvas.clientHeight;
  renderer.setSize(w, h, false);
  camera.aspect = w / Math.max(h, 1);
  camera.updateProjectionMatrix();
}
window.addEventListener("resize", resize);
resize();

function renderHotbar() {
  hotbarEl.innerHTML = "";
  game.hotbar.forEach((id, i) => {
    const btn = document.createElement("button");
    btn.type = "button";
    btn.className = "slot" + (i === game.selected ? " selected" : "");
    btn.title = BLOCKS[id].name;
    btn.setAttribute("aria-label", BLOCKS[id].name);
    btn.dataset.index = String(i);
    const swatch = document.createElement("span");
    swatch.className = "swatch";
    const [r, g, b] = BLOCKS[id].color;
    swatch.style.background = `rgb(${Math.round(r * 255)},${Math.round(g * 255)},${Math.round(b * 255)})`;
    const label = document.createElement("span");
    label.className = "slot-key";
    label.textContent = String(i + 1);
    btn.append(swatch, label);
    btn.addEventListener("click", (e) => {
      e.stopPropagation();
      game.selectSlot(i);
      renderHotbar();
    });
    hotbarEl.append(btn);
  });
}
renderHotbar();

const keys = new Set();
const input = { forward: 0, strafe: 0, jump: false, sprint: false };
let pointerLocked = false;
let lookHit = null;

window.addEventListener("keydown", (e) => {
  keys.add(e.code);
  if (e.code >= "Digit1" && e.code <= "Digit9") {
    game.selectSlot(Number(e.code.slice(5)) - 1);
    renderHotbar();
  }
  if (e.code === "KeyE" || e.code === "KeyQ") {
    game.cycleSlot(e.code === "KeyE" ? 1 : -1);
    renderHotbar();
  }
  if (e.code === "Escape" && document.pointerLockElement) {
    document.exitPointerLock();
  }
});
window.addEventListener("keyup", (e) => keys.delete(e.code));

function syncInput() {
  input.forward = (keys.has("KeyW") || keys.has("ArrowUp") ? 1 : 0) - (keys.has("KeyS") || keys.has("ArrowDown") ? 1 : 0);
  input.strafe = (keys.has("KeyD") || keys.has("ArrowRight") ? 1 : 0) - (keys.has("KeyA") || keys.has("ArrowLeft") ? 1 : 0);
  input.jump = keys.has("Space");
  input.sprint = keys.has("ShiftLeft") || keys.has("ShiftRight");
  // touch sticks
  input.forward += touchMove.y;
  input.strafe += touchMove.x;
  if (touchJump) input.jump = true;
}

canvas.addEventListener("click", () => {
  if (isTouch) return;
  if (!pointerLocked) canvas.requestPointerLock();
});

document.addEventListener("pointerlockchange", () => {
  pointerLocked = document.pointerLockElement === canvas;
  overlay.hidden = pointerLocked;
  hintEl.textContent = pointerLocked
    ? "LMB break · RMB place · 1–9 hotbar · Esc release"
    : "Click to play";
});

document.addEventListener("mousemove", (e) => {
  if (!pointerLocked) return;
  game.player.addLook(e.movementX, e.movementY);
});

canvas.addEventListener(
  "mousedown",
  (e) => {
    if (!pointerLocked && !isTouch) return;
    if (e.button === 0) {
      game.breakTarget();
      rebuildMesh();
    } else if (e.button === 2) {
      game.placeTarget();
      rebuildMesh();
    }
  },
  { passive: true },
);
canvas.addEventListener("contextmenu", (e) => e.preventDefault());
canvas.addEventListener(
  "wheel",
  (e) => {
    game.cycleSlot(e.deltaY > 0 ? 1 : -1);
    renderHotbar();
  },
  { passive: true },
);

// --- Touch controls ---
const touchMove = { x: 0, y: 0 };
let touchJump = false;
let lookTouchId = null;
let moveTouchId = null;
let lastLook = null;

function setupTouchUi() {
  if (!isTouch) {
    document.getElementById("touch-controls").hidden = true;
    return;
  }
  overlay.querySelector(".overlay-card p").textContent =
    "Drag right side to look. Left stick moves. Tap break / place.";
  document.getElementById("btn-start").textContent = "Tap to start";
  hintEl.textContent = "Touch controls active";

  const stick = document.getElementById("stick");
  const knob = document.getElementById("stick-knob");
  const jumpBtn = document.getElementById("btn-jump");
  const breakBtn = document.getElementById("btn-break");
  const placeBtn = document.getElementById("btn-place");

  const setKnob = (x, y) => {
    knob.style.transform = `translate(${x * 28}px, ${y * 28}px)`;
  };

  stick.addEventListener("pointerdown", (e) => {
    moveTouchId = e.pointerId;
    stick.setPointerCapture(e.pointerId);
  });
  stick.addEventListener("pointermove", (e) => {
    if (e.pointerId !== moveTouchId) return;
    const rect = stick.getBoundingClientRect();
    const cx = rect.left + rect.width / 2;
    const cy = rect.top + rect.height / 2;
    let dx = (e.clientX - cx) / (rect.width / 2);
    let dy = (e.clientY - cy) / (rect.height / 2);
    const len = Math.hypot(dx, dy) || 1;
    if (len > 1) {
      dx /= len;
      dy /= len;
    }
    touchMove.x = dx;
    touchMove.y = -dy;
    setKnob(dx, dy);
  });
  const endMove = (e) => {
    if (e.pointerId !== moveTouchId) return;
    moveTouchId = null;
    touchMove.x = 0;
    touchMove.y = 0;
    setKnob(0, 0);
  };
  stick.addEventListener("pointerup", endMove);
  stick.addEventListener("pointercancel", endMove);

  jumpBtn.addEventListener("pointerdown", (e) => {
    e.preventDefault();
    touchJump = true;
  });
  jumpBtn.addEventListener("pointerup", () => {
    touchJump = false;
  });
  jumpBtn.addEventListener("pointercancel", () => {
    touchJump = false;
  });

  breakBtn.addEventListener("click", (e) => {
    e.preventDefault();
    game.breakTarget();
    rebuildMesh();
  });
  placeBtn.addEventListener("click", (e) => {
    e.preventDefault();
    game.placeTarget();
    rebuildMesh();
  });

  canvas.addEventListener("pointerdown", (e) => {
    if (e.target.closest("#touch-controls") || e.target.closest("#hotbar")) return;
    if (e.clientX < innerWidth * 0.42) return;
    lookTouchId = e.pointerId;
    lastLook = { x: e.clientX, y: e.clientY };
    overlay.hidden = true;
  });
  canvas.addEventListener("pointermove", (e) => {
    if (e.pointerId !== lookTouchId || !lastLook) return;
    game.player.addLook(e.clientX - lastLook.x, e.clientY - lastLook.y, 0.004);
    lastLook = { x: e.clientX, y: e.clientY };
  });
  const endLook = (e) => {
    if (e.pointerId !== lookTouchId) return;
    lookTouchId = null;
    lastLook = null;
  };
  canvas.addEventListener("pointerup", endLook);
  canvas.addEventListener("pointercancel", endLook);
}
setupTouchUi();

document.getElementById("btn-start").addEventListener("click", () => {
  overlay.hidden = true;
  if (!isTouch) canvas.requestPointerLock();
});

rebuildMesh();

let last = performance.now();
let frames = 0;
let fpsTimer = 0;

function frame(now) {
  const dt = Math.min(0.05, (now - last) / 1000);
  last = now;
  frames += 1;
  fpsTimer += dt;
  if (fpsTimer >= 0.5) {
    fpsEl.textContent = `${Math.round(frames / fpsTimer)} fps`;
    frames = 0;
    fpsTimer = 0;
  }

  syncInput();
  if (overlay.hidden || pointerLocked || isTouch) {
    game.update(input, dt);
  }

  const eye = game.player.eye;
  camera.position.set(eye.x, eye.y, eye.z);
  const look = game.player.lookDir();
  camera.lookAt(eye.x + look.x, eye.y + look.y, eye.z + look.z);

  lookHit = game.lookRay();
  updateOutline(lookHit);
  if (lookHit?.hit && !game.world.hasSolid(lookHit.px, lookHit.py, lookHit.pz)) {
    ghost.position.set(lookHit.px, lookHit.py, lookHit.pz);
    const [r, g, b] = BLOCKS[game.selectedBlock].color;
    ghostMat.color.setRGB(r, g, b);
    ghost.visible = true;
  } else {
    ghost.visible = false;
  }

  coordsEl.textContent = `${game.player.x.toFixed(1)}  ${game.player.y.toFixed(1)}  ${game.player.z.toFixed(1)}`;

  rebuildMesh();
  renderer.render(scene, camera);
  requestAnimationFrame(frame);
}
requestAnimationFrame(frame);
