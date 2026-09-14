import { hexKey } from "./hex.js";
import {
  DEFAULT_BASE,
  cellsInBrush,
  createHistory,
  createTerrain,
  flattenTerrain,
  generateHills,
  hexMeanHeight,
  hexMinHeight,
  levelHex,
  mulberry32,
  pushUndo,
  raiseHex,
  raiseVertex,
  redo,
  sculptPreview,
  setWaterLevel,
  smoothSlopes,
  undo,
} from "./terrain.js";
import {
  clamp,
  createCamera,
  drawTerrain,
  nearestVertex,
  pickCell,
  resizeCanvas,
} from "./render.js";

const canvas = document.querySelector("#map");
const context = canvas.getContext("2d");
const readout = document.querySelector("#readout");
const waterInput = document.querySelector("#water");
const waterOutput = document.querySelector("#water-output");
const toolButtons = [...document.querySelectorAll("[data-tool]")];
const brushButtons = [...document.querySelectorAll("[data-brush]")];
const smoothButton = document.querySelector("#smooth");
const undoButton = document.querySelector("#undo");
const redoButton = document.querySelector("#redo");
const hillsButton = document.querySelector("#hills");
const flattenButton = document.querySelector("#flatten");
const spinLeftButton = document.querySelector("#spin-left");
const spinRightButton = document.querySelector("#spin-right");

const terrain = createTerrain();
sculptPreview(terrain);
const history = createHistory();
const camera = createCamera();
const pointers = new Map();

let view = { width: 1, height: 1 };
let tool = "raise";
let brush = 0;
let smooth = true;
let hover = null;
let stroke = null;
let panning = false;
let pinch = null;
let spaceHeld = false;
let drawQueued = false;

function brushCells(hex) {
  if (!hex) {
    return [];
  }
  if (tool === "corner") {
    return [{ q: hex.q, r: hex.r }];
  }
  return cellsInBrush(terrain, hex, brush);
}

function syncTools() {
  for (const button of toolButtons) {
    button.setAttribute("aria-pressed", String(button.dataset.tool === tool));
  }
  for (const button of brushButtons) {
    button.setAttribute("aria-pressed", String(Number(button.dataset.brush) === brush));
  }
  smoothButton.setAttribute("aria-pressed", String(smooth));
  undoButton.disabled = history.past.length === 0;
  redoButton.disabled = history.future.length === 0;
  waterInput.value = String(terrain.waterLevel);
  waterOutput.textContent = String(terrain.waterLevel);
}

function formatReadout() {
  if (!hover) {
    readout.textContent = `Water ${terrain.waterLevel}`;
    return;
  }
  const height = hexMeanHeight(terrain, hover.q, hover.r);
  const low = hexMinHeight(terrain, hover.q, hover.r);
  let text = `${hover.q}, ${hover.r} · height ${height.toFixed(1)} · water ${terrain.waterLevel}`;
  if (tool === "corner" && hover.vertex !== null && hover.vertex !== undefined) {
    text += ` · corner ${hover.vertex} (${low}–${Math.round(height)})`;
  }
  readout.textContent = text;
}

function highlightState() {
  return {
    hex: hover,
    vertex: tool === "corner" && hover ? hover.vertex : null,
    brush: brushCells(hover),
  };
}

function requestDraw() {
  if (drawQueued) {
    return;
  }
  drawQueued = true;
  requestAnimationFrame(() => {
    drawQueued = false;
    drawTerrain(context, terrain, camera, view, highlightState());
  });
}

function canvasPoint(event) {
  const bounds = canvas.getBoundingClientRect();
  return {
    x: event.clientX - bounds.left,
    y: event.clientY - bounds.top,
  };
}

function hitFromEvent(event) {
  const point = canvasPoint(event);
  const cell = pickCell(terrain, camera, point.x, point.y, view);
  if (!cell) {
    return null;
  }
  const vertex = nearestVertex(terrain, camera, cell.q, cell.r, point.x, point.y, view);
  return { q: cell.q, r: cell.r, vertex, part: cell.part };
}

function updateHover(event) {
  hover = hitFromEvent(event);
  formatReadout();
  requestDraw();
}

function wantsLower(event) {
  const invert = event.button === 2 || event.shiftKey;
  if (tool === "lower") {
    return !invert;
  }
  return invert;
}

function applyPaint(target, lower) {
  if (!target) {
    return false;
  }
  if (tool === "corner") {
    const key = `${hexKey(target.q, target.r)}:${target.vertex}`;
    if (stroke.applied.has(key)) {
      return false;
    }
    const changed = raiseVertex(terrain, target.q, target.r, target.vertex, lower ? -1 : 1);
    if (changed && smooth) {
      smoothSlopes(terrain, !lower);
    }
    stroke.applied.add(key);
    return changed;
  }

  if (tool === "level") {
    if (stroke.levelTarget === null) {
      stroke.levelTarget = Math.round(hexMeanHeight(terrain, target.q, target.r));
    }
    let changed = false;
    for (const cell of brushCells(target)) {
      const key = hexKey(cell.q, cell.r);
      if (stroke.applied.has(key)) {
        continue;
      }
      if (levelHex(terrain, cell.q, cell.r, stroke.levelTarget)) {
        changed = true;
      }
      stroke.applied.add(key);
    }
    return changed;
  }

  const delta = lower ? -1 : 1;
  let changed = false;
  for (const cell of brushCells(target)) {
    const key = hexKey(cell.q, cell.r);
    if (stroke.applied.has(key)) {
      continue;
    }
    if (raiseHex(terrain, cell.q, cell.r, delta)) {
      changed = true;
    }
    stroke.applied.add(key);
  }
  if (changed && smooth) {
    smoothSlopes(terrain, delta > 0);
  }
  return changed;
}

function beginStroke(event) {
  pushUndo(history, terrain);
  stroke = {
    lower: wantsLower(event),
    applied: new Set(),
    levelTarget: null,
  };
  applyPaint(hitFromEvent(event), stroke.lower);
  syncTools();
  formatReadout();
  requestDraw();
}

function endStroke() {
  stroke = null;
  if (history.past.length > 0) {
    const last = history.past[history.past.length - 1];
    let same = last.size === terrain.heights.size;
    if (same) {
      for (const [id, value] of last) {
        if (terrain.heights.get(id) !== value) {
          same = false;
          break;
        }
      }
    }
    if (same) {
      history.past.pop();
    }
  }
  syncTools();
}

function handlePinch() {
  const pts = [...pointers.values()];
  if (pts.length !== 2) {
    return;
  }
  const dist = Math.hypot(pts[0].x - pts[1].x, pts[0].y - pts[1].y);
  const midX = (pts[0].x + pts[1].x) / 2;
  const midY = (pts[0].y + pts[1].y) / 2;
  const angle = Math.atan2(pts[1].y - pts[0].y, pts[1].x - pts[0].x);
  if (pinch) {
    camera.zoom = clamp(camera.zoom * (dist / pinch.dist), 0.45, 2.8);
    camera.panX += midX - pinch.midX;
    camera.panY += midY - pinch.midY;
    camera.yaw += angle - pinch.angle;
    requestDraw();
  }
  pinch = { dist, midX, midY, angle };
}

function onPointerDown(event) {
  canvas.setPointerCapture(event.pointerId);
  pointers.set(event.pointerId, {
    x: event.clientX,
    y: event.clientY,
    button: event.button,
  });
  if (pointers.size === 2) {
    stroke = null;
    panning = false;
    return;
  }
  if (event.button === 1 || spaceHeld || event.altKey) {
    panning = true;
    return;
  }
  beginStroke(event);
}

function onPointerMove(event) {
  const prev = pointers.get(event.pointerId);
  if (!prev) {
    updateHover(event);
    return;
  }
  pointers.set(event.pointerId, {
    x: event.clientX,
    y: event.clientY,
    button: prev.button,
  });
  if (pointers.size === 2) {
    handlePinch();
    return;
  }
  if (panning) {
    camera.panX += event.clientX - prev.x;
    camera.panY += event.clientY - prev.y;
    requestDraw();
    return;
  }
  if (stroke) {
    applyPaint(hitFromEvent(event), stroke.lower);
    syncTools();
  }
  updateHover(event);
}

function onPointerUp(event) {
  pointers.delete(event.pointerId);
  if (pointers.size < 2) {
    pinch = null;
  }
  if (pointers.size === 0) {
    panning = false;
    if (stroke) {
      endStroke();
    }
  }
}

function onWheel(event) {
  event.preventDefault();
  if (event.shiftKey) {
    camera.yaw += event.deltaY * 0.003;
  } else {
    const factor = event.ctrlKey ? 0.01 : 0.0014;
    camera.zoom = clamp(camera.zoom * (1 - event.deltaY * factor), 0.45, 2.8);
  }
  requestDraw();
}

function setTool(next) {
  tool = next;
  syncTools();
  requestDraw();
}

function setBrush(next) {
  brush = next;
  syncTools();
  requestDraw();
}

function mutateMap(fn) {
  pushUndo(history, terrain);
  fn();
  syncTools();
  formatReadout();
  requestDraw();
}

function onKeyDown(event) {
  if (event.target instanceof HTMLInputElement) {
    return;
  }
  if (event.code === "Space") {
    spaceHeld = true;
    event.preventDefault();
    return;
  }
  const key = event.key.toLowerCase();
  if ((event.metaKey || event.ctrlKey) && key === "z") {
    event.preventDefault();
    if (event.shiftKey) {
      if (redo(history, terrain)) {
        syncTools();
        requestDraw();
      }
      return;
    }
    if (undo(history, terrain)) {
      syncTools();
      requestDraw();
    }
    return;
  }
  if (key === "1") setTool("raise");
  if (key === "2") setTool("lower");
  if (key === "3") setTool("level");
  if (key === "4") setTool("corner");
  if (key === "[") setBrush(0);
  if (key === "]") setBrush(1);
  if (key === "s") {
    smooth = !smooth;
    syncTools();
  }
  if (key === "h") {
    mutateMap(() => generateHills(terrain, mulberry32(Date.now())));
  }
  if (key === "q") {
    camera.yaw -= 0.12;
    requestDraw();
  }
  if (key === "e") {
    camera.yaw += 0.12;
    requestDraw();
  }
  if (key === "-" || key === "_") {
    camera.zoom = clamp(camera.zoom / 1.08, 0.45, 2.8);
    requestDraw();
  }
  if (key === "=" || key === "+") {
    camera.zoom = clamp(camera.zoom * 1.08, 0.45, 2.8);
    requestDraw();
  }
  const pan = 18;
  if (key === "arrowleft" || key === "a") {
    camera.panX += pan;
    requestDraw();
  }
  if (key === "arrowright" || key === "d") {
    camera.panX -= pan;
    requestDraw();
  }
  if (key === "arrowup" || key === "w") {
    camera.panY += pan;
    requestDraw();
  }
  if (key === "arrowdown") {
    camera.panY -= pan;
    requestDraw();
  }
}

function onKeyUp(event) {
  if (event.code === "Space") {
    spaceHeld = false;
  }
}

function fit() {
  view = resizeCanvas(canvas, context);
  requestDraw();
}

for (const button of toolButtons) {
  button.addEventListener("click", () => setTool(button.dataset.tool));
}
for (const button of brushButtons) {
  button.addEventListener("click", () => setBrush(Number(button.dataset.brush)));
}
smoothButton.addEventListener("click", () => {
  smooth = !smooth;
  syncTools();
});
undoButton.addEventListener("click", () => {
  if (undo(history, terrain)) {
    syncTools();
    formatReadout();
    requestDraw();
  }
});
redoButton.addEventListener("click", () => {
  if (redo(history, terrain)) {
    syncTools();
    formatReadout();
    requestDraw();
  }
});
hillsButton.addEventListener("click", () => {
  mutateMap(() => generateHills(terrain, mulberry32(Date.now())));
});
flattenButton.addEventListener("click", () => {
  mutateMap(() => flattenTerrain(terrain, DEFAULT_BASE));
});
spinLeftButton.addEventListener("click", () => {
  camera.yaw -= 0.18;
  requestDraw();
});
spinRightButton.addEventListener("click", () => {
  camera.yaw += 0.18;
  requestDraw();
});
waterInput.addEventListener("input", () => {
  setWaterLevel(terrain, Number(waterInput.value));
  syncTools();
  formatReadout();
  requestDraw();
});

canvas.addEventListener("pointerdown", onPointerDown);
canvas.addEventListener("pointermove", onPointerMove);
canvas.addEventListener("pointerup", onPointerUp);
canvas.addEventListener("pointercancel", onPointerUp);
canvas.addEventListener("wheel", onWheel, { passive: false });
canvas.addEventListener("contextmenu", (event) => event.preventDefault());
window.addEventListener("keydown", onKeyDown);
window.addEventListener("keyup", onKeyUp);
window.addEventListener("resize", fit);
new ResizeObserver(fit).observe(canvas);

syncTools();
formatReadout();
fit();
