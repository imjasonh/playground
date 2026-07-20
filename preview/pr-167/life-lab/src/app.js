// Life Lab: thin JS shim over the life-stl wasm module + three.js viewer.
import * as THREE from 'three';
import { OrbitControls } from '../vendor/OrbitControls.js';
import init, { simulate, export_stl, export_3mf, pattern_cells } from '../vendor/life_stl/life_stl.js';
import { makeCells, resizeCells, setCell, getCell, pointToCell, liveCount } from './grid.js';

// ---------- state ----------
const state = {
  width: 24,
  height: 24,
  depth: 24,
  cellMm: 4,
  cells: makeCells(24, 24),
  seed: (Math.random() * 0xffffffff) >>> 0,
};

// ---------- DOM ----------
const $ = (id) => document.getElementById(id);
const editor = $('editor');
const ectx = editor.getContext('2d');
const boardSel = $('board');
const depthInput = $('depth');
const cellMmInput = $('cellmm');
const patternSel = $('pattern');
const densityRow = $('density-row');
const densityInput = $('density');

// ---------- three.js scene ----------
const viewport = $('viewport');
const renderer = new THREE.WebGLRenderer({ antialias: true });
renderer.setPixelRatio(Math.min(devicePixelRatio, 2));
viewport.appendChild(renderer.domElement);
const scene = new THREE.Scene();
scene.background = new THREE.Color(0x0e1116);
const camera = new THREE.PerspectiveCamera(45, 1, 0.1, 2000);
const controls = new OrbitControls(camera, renderer.domElement);
controls.enableDamping = true;

scene.add(new THREE.HemisphereLight(0xcfe6ff, 0x28323d, 1.1));
const sun = new THREE.DirectionalLight(0xffffff, 1.4);
sun.position.set(1.5, -2, 3);
scene.add(sun);

let modelGroup = new THREE.Group();
scene.add(modelGroup);

function resizeViewport() {
  const w = viewport.clientWidth;
  const h = viewport.clientHeight;
  renderer.setSize(w, h, false);
  camera.aspect = w / h;
  camera.updateProjectionMatrix();
}
new ResizeObserver(resizeViewport).observe(viewport);

function frame() {
  controls.update();
  renderer.render(scene, camera);
  requestAnimationFrame(frame);
}

// ---------- editor ----------
function drawEditor() {
  const { width, height, cells } = state;
  const px = Math.max(1, Math.floor(editor.clientWidth / width));
  editor.width = width * px;
  editor.height = height * px;
  ectx.fillStyle = '#0a0d12';
  ectx.fillRect(0, 0, editor.width, editor.height);
  ectx.fillStyle = '#4ea1ff';
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      if (cells[y * width + x]) ectx.fillRect(x * px + 1, y * px + 1, px - 2, px - 2);
    }
  }
  ectx.strokeStyle = 'rgba(255,255,255,0.06)';
  for (let x = 0; x <= width; x++) {
    ectx.beginPath(); ectx.moveTo(x * px, 0); ectx.lineTo(x * px, editor.height); ectx.stroke();
  }
  for (let y = 0; y <= height; y++) {
    ectx.beginPath(); ectx.moveTo(0, y * px); ectx.lineTo(editor.width, y * px); ectx.stroke();
  }
}

let painting = null; // 1 = draw, 0 = erase
function editorCell(ev) {
  const rect = editor.getBoundingClientRect();
  return pointToCell(
    ev.clientX - rect.left, ev.clientY - rect.top,
    rect.width, rect.height, state.width, state.height,
  );
}
editor.addEventListener('contextmenu', (ev) => ev.preventDefault());
editor.addEventListener('pointerdown', (ev) => {
  ev.preventDefault();
  editor.setPointerCapture(ev.pointerId);
  const cell = editorCell(ev);
  if (!cell) return;
  painting = ev.buttons === 2 ? 0 : getCell(state.cells, state.width, cell.x, cell.y) ? 0 : 1;
  setCell(state.cells, state.width, cell.x, cell.y, painting);
  drawEditor();
  scheduleSimulate();
});
editor.addEventListener('pointermove', (ev) => {
  if (painting === null) return;
  const cell = editorCell(ev);
  if (!cell) return;
  setCell(state.cells, state.width, cell.x, cell.y, painting);
  drawEditor();
  scheduleSimulate();
});
addEventListener('pointerup', () => { painting = null; });

// ---------- simulation + viewer ----------
let simTimer = 0;
function scheduleSimulate() {
  clearTimeout(simTimer);
  simTimer = setTimeout(runSimulate, 120);
}

function runSimulate() {
  const { cells, width, height, depth } = state;
  const result = simulate(cells, width, height, depth);
  renderModel(result);
  renderStats(result);
}

function renderModel(result) {
  scene.remove(modelGroup);
  modelGroup.traverse((o) => { o.geometry?.dispose(); o.material?.dispose(); });
  modelGroup = new THREE.Group();

  const voxels = result.voxels;
  const count = voxels.length / 3;
  const depthTotal = state.depth + 1;

  if (count > 0) {
    const box = new THREE.BoxGeometry(0.96, 0.96, 0.96);
    const mat = new THREE.MeshStandardMaterial({ roughness: 0.55, metalness: 0.05 });
    const mesh = new THREE.InstancedMesh(box, mat, count);
    const m = new THREE.Matrix4();
    const color = new THREE.Color();
    for (let i = 0; i < count; i++) {
      const x = voxels[i * 3], y = voxels[i * 3 + 1], z = voxels[i * 3 + 2];
      m.setPosition(x + 0.5, y + 0.5, z + 0.5);
      mesh.setMatrixAt(i, m);
      // Height gradient: deep blue → cyan → warm amber near the top.
      color.setHSL(0.62 - 0.5 * (z / depthTotal), 0.75, 0.55);
      mesh.setColorAt(i, color);
    }
    mesh.instanceColor.needsUpdate = true;
    modelGroup.add(mesh);
  }

  const base = result.base;
  if (base.length === 5) {
    const [x0, y0, x1, y1, layers] = base;
    const geo = new THREE.BoxGeometry(x1 - x0 + 1, y1 - y0 + 1, layers);
    const mat = new THREE.MeshStandardMaterial({ color: 0x39424e, roughness: 0.8 });
    const slab = new THREE.Mesh(geo, mat);
    slab.position.set((x0 + x1 + 1) / 2, (y0 + y1 + 1) / 2, layers / 2);
    modelGroup.add(slab);
  }

  const braces = result.braces;
  if (braces.length > 0) {
    const geo = new THREE.BufferGeometry();
    geo.setAttribute('position', new THREE.Float32BufferAttribute(braces, 3));
    const mat = new THREE.LineBasicMaterial({ color: 0x8b98a9, transparent: true, opacity: 0.5 });
    modelGroup.add(new THREE.LineSegments(geo, mat));
  }

  // Z-up so towers grow upward on screen.
  modelGroup.rotation.x = -Math.PI / 2;
  modelGroup.position.set(-state.width / 2, 0, state.height / 2);
  scene.add(modelGroup);
}

function fitCamera() {
  const r = Math.max(state.width, state.height, state.depth);
  camera.position.set(r * 1.2, r * 0.9, r * 1.2);
  controls.target.set(0, state.depth / 2, 0);
  camera.near = r / 100;
  camera.far = r * 10;
  camera.updateProjectionMatrix();
}

function renderStats(result) {
  const verdict = $('verdict');
  if (result.interesting) {
    verdict.textContent = result.period === 0
      ? `✔ active through all ${state.depth} generations`
      : `✔ active until generation ${result.quiescent_generation} of ${state.depth}`;
    verdict.className = 'good';
  } else {
    const kind = result.period === 1 ? 'still life' : `period-${result.period} oscillator`;
    verdict.textContent = `⚠ settles into a ${kind} at generation ${result.quiescent_generation} — everything above is a static tower`;
    verdict.className = 'warn';
  }
  const mm = (n) => (n * state.cellMm).toFixed(0);
  $('counts').textContent =
    `${result.life_voxels} voxels · ${result.brace_count} braces · ` +
    `${liveCount(state.cells)} seed cells · ` +
    `${mm(state.width)}×${mm(state.height)}×${mm(state.depth + 1)} mm` +
    (result.one_piece ? ' · one piece' : ' · ⚠ not one piece');
}

// ---------- controls ----------
function setBoard(size) {
  state.cells = resizeCells(state.cells, state.width, state.height, size, size);
  state.width = size;
  state.height = size;
  drawEditor();
  fitCamera();
  updateSizeLabel();
  scheduleSimulate();
}

function updateSizeLabel() {
  const { width, height, depth, cellMm } = state;
  $('size-label').textContent =
    `${(width * cellMm).toFixed(0)} × ${(height * cellMm).toFixed(0)} × ${((depth + 1) * cellMm).toFixed(0)} mm`;
}

boardSel.addEventListener('change', () => setBoard(Number(boardSel.value)));
depthInput.addEventListener('input', () => {
  state.depth = Number(depthInput.value);
  $('depth-label').textContent = depthInput.value;
  updateSizeLabel();
  fitCamera();
  scheduleSimulate();
});
cellMmInput.addEventListener('change', () => {
  state.cellMm = Math.min(8, Math.max(2, Number(cellMmInput.value) || 4));
  cellMmInput.value = state.cellMm;
  updateSizeLabel();
  runSimulate();
});

function stampPattern() {
  const name = patternSel.value;
  if (!name) return;
  densityRow.hidden = name !== 'soup';
  state.cells = pattern_cells(name, state.width, state.height, state.seed, Number(densityInput.value));
  drawEditor();
  scheduleSimulate();
}
patternSel.addEventListener('change', stampPattern);
densityInput.addEventListener('input', () => {
  $('density-label').textContent = densityInput.value;
  stampPattern();
});
$('reroll').addEventListener('click', () => {
  state.seed = (Math.random() * 0xffffffff) >>> 0;
  stampPattern();
});
$('clear').addEventListener('click', () => {
  state.cells = makeCells(state.width, state.height);
  patternSel.value = '';
  densityRow.hidden = true;
  drawEditor();
  scheduleSimulate();
});

// ---------- export ----------
function download(bytes, filename, type) {
  const blob = new Blob([bytes], { type });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = filename;
  a.click();
  URL.revokeObjectURL(url);
}
const exportName = () => patternSel.value || 'life-lab';
$('dl-stl').addEventListener('click', () => {
  const bytes = export_stl(state.cells, state.width, state.height, state.depth, state.cellMm);
  download(bytes, `${exportName()}.stl`, 'model/stl');
});
$('dl-3mf').addEventListener('click', () => {
  const bytes = export_3mf(state.cells, state.width, state.height, state.depth, state.cellMm, exportName());
  download(bytes, `${exportName()}-a1mini.3mf`, 'model/3mf');
});

// ---------- boot ----------
await init();
$('loading').remove();
resizeViewport();
// Start with something alive: an acorn.
patternSel.value = 'acorn';
stampPattern();
$('depth-label').textContent = String(state.depth);
updateSizeLabel();
drawEditor();
fitCamera();
runSimulate();
frame();
