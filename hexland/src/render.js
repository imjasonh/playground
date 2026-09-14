import { axialToWorld, hexCornerWorld, hexKey } from "./hex.js";
import {
  getVertexHeight,
  hasRoad,
  hexIsUnderwater,
  hexMaxHeight,
  hexMeanHeight,
  hexMinHeight,
  hexSlope,
  hexVertexHeights,
  isSkirtEdge,
  roadNeighbors,
} from "./terrain.js";

export const LIGHT = normalize(-0.46, 0.82, 0.32);
export const ZOOM_MIN = 0.22;
export const ZOOM_MAX = 3.2;
export const ELEVATION_MIN = 0.22;
export const ELEVATION_MAX = 1.18;

export function createCamera() {
  return {
    yaw: 0.38,
    elevation: 0.54,
    zoom: 0.62,
    panX: 0,
    panY: 0,
    hexSize: 20,
    heightScale: 12,
  };
}

export function clamp(value, min, max) {
  return Math.max(min, Math.min(max, value));
}

export function normalize(x, y, z) {
  const length = Math.hypot(x, y, z) || 1;
  return { x: x / length, y: y / length, z: z / length };
}

export function rotateY(x, z, yaw) {
  const cos = Math.cos(yaw);
  const sin = Math.sin(yaw);
  return {
    x: x * cos - z * sin,
    z: x * sin + z * cos,
  };
}

export function viewOrigin(width, height) {
  return {
    x: width / 2,
    y: height * 0.58,
  };
}

export function project(wx, wy, wz, camera, origin) {
  const rotated = rotateY(wx, wz, camera.yaw);
  const zoom = camera.zoom;
  const sinE = Math.sin(camera.elevation);
  const cosE = Math.cos(camera.elevation);
  return {
    x: origin.x + camera.panX + rotated.x * zoom,
    y: origin.y + camera.panY + rotated.z * sinE * zoom - wy * cosE * zoom,
    depth: rotated.z * cosE + wy * sinE,
  };
}

export function cellGroundDepth(q, r, camera) {
  const world = axialToWorld(q, r, camera.hexSize);
  const rotated = rotateY(world.x, world.z, camera.yaw);
  return rotated.z;
}

export function hexTopPoints(terrain, q, r, camera, origin) {
  const points = [];
  for (let i = 0; i < 6; i += 1) {
    const corner = hexCornerWorld(q, r, i, camera.hexSize);
    const y = getVertexHeight(terrain, q, r, i) * camera.heightScale;
    points.push(project(corner.x, y, corner.z, camera, origin));
  }
  return points;
}

export function hexBasePoints(q, r, camera, origin) {
  const points = [];
  for (let i = 0; i < 6; i += 1) {
    const corner = hexCornerWorld(q, r, i, camera.hexSize);
    points.push(project(corner.x, 0, corner.z, camera, origin));
  }
  return points;
}

export function pointInPolygon(x, y, points) {
  let inside = false;
  for (let i = 0, j = points.length - 1; i < points.length; j = i, i += 1) {
    const xi = points[i].x;
    const yi = points[i].y;
    const xj = points[j].x;
    const yj = points[j].y;
    const denom = yj - yi === 0 ? 1 : yj - yi;
    const intersect = yi > y !== yj > y && x < ((xj - xi) * (y - yi)) / denom + xi;
    if (intersect) {
      inside = !inside;
    }
  }
  return inside;
}

function hexScreenRadius(camera) {
  return camera.hexSize * camera.zoom * 1.35 + 10;
}

export function pickCell(terrain, camera, x, y, view) {
  const origin = viewOrigin(view.width, view.height);
  const ordered = [...terrain.cells].sort(
    (a, b) => cellGroundDepth(b.q, b.r, camera) - cellGroundDepth(a.q, a.r, camera),
  );
  const reach = hexScreenRadius(camera);
  for (const cell of ordered) {
    const world = axialToWorld(cell.q, cell.r, camera.hexSize);
    const meanY = hexMeanHeight(terrain, cell.q, cell.r) * camera.heightScale;
    const center = project(world.x, meanY, world.z, camera, origin);
    if (Math.hypot(center.x - x, center.y - y) > reach + 28) {
      continue;
    }
    const top = hexTopPoints(terrain, cell.q, cell.r, camera, origin);
    if (pointInPolygon(x, y, top)) {
      return { q: cell.q, r: cell.r, part: "top" };
    }
    const base = hexBasePoints(cell.q, cell.r, camera, origin);
    for (let i = 0; i < 6; i += 1) {
      if (!isSkirtEdge(terrain, cell.q, cell.r, i)) {
        continue;
      }
      const next = (i + 1) % 6;
      const side = [top[i], top[next], base[next], base[i]];
      if (pointInPolygon(x, y, side)) {
        return { q: cell.q, r: cell.r, part: "side" };
      }
    }
  }
  return null;
}

export function nearestVertex(terrain, camera, q, r, x, y, view) {
  const origin = viewOrigin(view.width, view.height);
  const top = hexTopPoints(terrain, q, r, camera, origin);
  let best = 0;
  let bestDist = Infinity;
  for (let i = 0; i < 6; i += 1) {
    const dist = Math.hypot(top[i].x - x, top[i].y - y);
    if (dist < bestDist) {
      bestDist = dist;
      best = i;
    }
  }
  return best;
}

export function resizeCanvas(canvas, context) {
  const bounds = canvas.getBoundingClientRect();
  const dpr = Math.min(window.devicePixelRatio || 1, 2);
  const cssWidth = Math.max(1, Math.round(bounds.width));
  const cssHeight = Math.max(1, Math.round(bounds.height));
  const width = Math.round(cssWidth * dpr);
  const height = Math.round(cssHeight * dpr);
  if (canvas.width !== width || canvas.height !== height) {
    canvas.width = width;
    canvas.height = height;
  }
  context.setTransform(dpr, 0, 0, dpr, 0, 0);
  return { width: cssWidth, height: cssHeight, dpr };
}

export function fitZoom(terrain, camera, view) {
  const span = (terrain.radius * 2 + 1) * camera.hexSize * 1.55;
  const next = Math.min(view.width / span, view.height / span) * 1.08;
  camera.zoom = clamp(next, ZOOM_MIN, ZOOM_MAX);
}

function mix(a, b, t) {
  const u = clamp(t, 0, 1);
  return [
    a[0] + (b[0] - a[0]) * u,
    a[1] + (b[1] - a[1]) * u,
    a[2] + (b[2] - a[2]) * u,
  ];
}

function rgb(color, alpha = 1) {
  const r = Math.round(color[0]);
  const g = Math.round(color[1]);
  const b = Math.round(color[2]);
  if (alpha < 1) {
    return `rgba(${r}, ${g}, ${b}, ${alpha})`;
  }
  return `rgb(${r}, ${g}, ${b})`;
}

function faceNormal(a, b, c) {
  const ux = b.x - a.x;
  const uy = b.y - a.y;
  const uz = b.z - a.z;
  const vx = c.x - a.x;
  const vy = c.y - a.y;
  const vz = c.z - a.z;
  return normalize(uy * vz - uz * vy, uz * vx - ux * vz, ux * vy - uy * vx);
}

function newellNormal(points) {
  let x = 0;
  let y = 0;
  let z = 0;
  for (let i = 0; i < points.length; i += 1) {
    const a = points[i];
    const b = points[(i + 1) % points.length];
    x += (a.y - b.y) * (a.z + b.z);
    y += (a.z - b.z) * (a.x + b.x);
    z += (a.x - b.x) * (a.y + b.y);
  }
  return normalize(x, y, z);
}

function flipToward(normal, x, y, z) {
  if (normal.x * x + normal.y * y + normal.z * z < 0) {
    return { x: -normal.x, y: -normal.y, z: -normal.z };
  }
  return normal;
}

function shade(color, normal) {
  const lit = clamp(normal.x * LIGHT.x + normal.y * LIGHT.y + normal.z * LIGHT.z, 0, 1);
  const ambient = 0.42 + 0.58 * lit;
  return [color[0] * ambient, color[1] * ambient, color[2] * ambient];
}

function grassColor(height, slope, wet) {
  const t = clamp(height / 10, 0, 1);
  let color = mix([62, 122, 48], [196, 196, 118], t);
  if (height >= 9) {
    color = mix(color, [214, 216, 208], clamp((height - 9) / 3, 0, 1));
  }
  if (slope >= 2) {
    color = mix(color, [128, 96, 62], 0.45);
  }
  if (wet) {
    color = mix(color, [58, 78, 52], 0.35);
  }
  return color;
}

function dirtColor(steep) {
  if (steep) {
    return [110, 100, 88];
  }
  return [145, 104, 64];
}

function worldCorner(q, r, i, y, size) {
  const corner = hexCornerWorld(q, r, i, size);
  return { x: corner.x, y, z: corner.z };
}

function hexCenterWorld(terrain, q, r, camera) {
  const center = axialToWorld(q, r, camera.hexSize);
  return {
    x: center.x,
    y: hexMeanHeight(terrain, q, r) * camera.heightScale,
    z: center.z,
  };
}

function fillPoly(context, points) {
  context.beginPath();
  context.moveTo(points[0].x, points[0].y);
  for (let i = 1; i < points.length; i += 1) {
    context.lineTo(points[i].x, points[i].y);
  }
  context.closePath();
}

function drawSky(context, width, height) {
  const sky = context.createLinearGradient(0, 0, 0, height);
  sky.addColorStop(0, "#8ec4e0");
  sky.addColorStop(0.55, "#c5dce3");
  sky.addColorStop(1, "#d9e4c8");
  context.fillStyle = sky;
  context.fillRect(0, 0, width, height);
}

function drawShadow(context, terrain, camera, origin) {
  const center = project(0, 0, 0, camera, origin);
  const radius = terrain.radius * camera.hexSize * camera.zoom * 1.18;
  context.save();
  context.fillStyle = "rgba(28, 38, 24, 0.16)";
  context.beginPath();
  context.ellipse(
    center.x,
    center.y + 10,
    radius,
    radius * Math.sin(camera.elevation) * 0.92,
    0,
    0,
    Math.PI * 2,
  );
  context.fill();
  context.restore();
}

const SCREEN_PAD = 80;

function cellOnScreen(q, r, camera, origin, view) {
  const world = axialToWorld(q, r, camera.hexSize);
  const mid = project(world.x, 4 * camera.heightScale, world.z, camera, origin);
  const pad = camera.hexSize * camera.zoom * 3 + SCREEN_PAD;
  return mid.x >= -pad && mid.x <= view.width + pad && mid.y >= -pad && mid.y <= view.height + pad;
}

function drawRoad(context, terrain, q, r, camera, origin, topNormal) {
  const here = hexCenterWorld(terrain, q, r, camera);
  const hereScreen = project(here.x, here.y + 0.8, here.z, camera, origin);
  const width = camera.hexSize * camera.zoom * 0.4;
  const color = rgb(shade([166, 140, 98], topNormal));
  const edge = rgb(shade([122, 98, 68], topNormal));
  context.lineCap = "round";
  context.lineJoin = "round";
  const links = roadNeighbors(terrain, q, r);
  if (links.length === 0) {
    context.beginPath();
    context.fillStyle = color;
    context.strokeStyle = edge;
    context.lineWidth = Math.max(1, width * 0.18);
    context.arc(hereScreen.x, hereScreen.y, width * 0.42, 0, Math.PI * 2);
    context.fill();
    context.stroke();
    return;
  }
  context.strokeStyle = color;
  context.lineWidth = width;
  context.beginPath();
  context.moveTo(hereScreen.x, hereScreen.y);
  for (const next of links) {
    const there = hexCenterWorld(terrain, next.q, next.r, camera);
    const midX = (here.x + there.x) / 2;
    const midY = (here.y + there.y) / 2 + 0.8;
    const midZ = (here.z + there.z) / 2;
    const mid = project(midX, midY, midZ, camera, origin);
    context.lineTo(mid.x, mid.y);
    context.moveTo(hereScreen.x, hereScreen.y);
  }
  context.stroke();
  context.beginPath();
  context.fillStyle = color;
  context.arc(hereScreen.x, hereScreen.y, width * 0.36, 0, Math.PI * 2);
  context.fill();
}

function drawHex(context, terrain, cell, camera, origin, hoverKey, brushKeys) {
  const { q, r } = cell;
  const size = camera.hexSize;
  const heights = hexVertexHeights(terrain, q, r);
  const topWorld = heights.map((h, i) => worldCorner(q, r, i, h * camera.heightScale, size));
  const baseWorld = heights.map((_, i) => worldCorner(q, r, i, 0, size));
  const top = topWorld.map((p) => project(p.x, p.y, p.z, camera, origin));
  const base = baseWorld.map((p) => project(p.x, p.y, p.z, camera, origin));
  const mean = hexMeanHeight(terrain, q, r);
  const slope = hexSlope(terrain, q, r);
  const wet = hexMaxHeight(terrain, q, r) < terrain.waterLevel;
  const key = hexKey(q, r);
  const hovered = key === hoverKey;
  const inBrush = brushKeys.has(key);
  const hexCenter = axialToWorld(q, r, size);
  const center = project(hexCenter.x, mean * camera.heightScale, hexCenter.z, camera, origin);

  for (let i = 0; i < 6; i += 1) {
    if (!isSkirtEdge(terrain, q, r, i)) {
      continue;
    }
    const next = (i + 1) % 6;
    const a = topWorld[i];
    const b = topWorld[next];
    const c = baseWorld[next];
    const screen = [top[i], top[next], base[next], base[i]];
    const midY = (screen[0].y + screen[1].y + screen[2].y + screen[3].y) / 4;
    if (midY < center.y - 2) {
      continue;
    }
    const rise = Math.abs(heights[i] - heights[next]);
    const drop = Math.max(heights[i], heights[next]);
    const steep = rise >= 2 || drop >= 7;
    const mid = {
      x: (a.x + b.x) / 2,
      y: (a.y + c.y) / 2,
      z: (a.z + b.z) / 2,
    };
    const normal = flipToward(
      faceNormal(a, b, c),
      mid.x - hexCenter.x,
      0,
      mid.z - hexCenter.z,
    );
    context.fillStyle = rgb(shade(dirtColor(steep), normal));
    fillPoly(context, screen);
    context.fill();
  }

  const topNormal = flipToward(newellNormal(topWorld), 0, 1, 0);
  const color = shade(grassColor(mean, slope, wet), topNormal);
  context.fillStyle = rgb(hovered || inBrush ? mix(color, [255, 236, 160], 0.28) : color);
  fillPoly(context, top);
  context.fill();

  if (hasRoad(terrain, q, r)) {
    drawRoad(context, terrain, q, r, camera, origin, topNormal);
  }

  if (hovered || inBrush) {
    context.strokeStyle = hovered ? "rgba(48, 36, 14, 0.7)" : "rgba(48, 36, 14, 0.35)";
    context.lineWidth = hovered ? 1.6 : 1.1;
    fillPoly(context, top);
    context.stroke();
  }

  if (hexIsUnderwater(terrain, q, r)) {
    const waterY = terrain.waterLevel * camera.heightScale;
    const water = [];
    for (let i = 0; i < 6; i += 1) {
      const corner = hexCornerWorld(q, r, i, size);
      water.push(project(corner.x, waterY, corner.z, camera, origin));
    }
    context.fillStyle = hexMinHeight(terrain, q, r) + 1 < terrain.waterLevel
      ? "rgba(46, 112, 150, 0.55)"
      : "rgba(72, 148, 176, 0.42)";
    fillPoly(context, water);
    context.fill();
  }
}

export function drawTerrain(context, terrain, camera, view, highlight) {
  const origin = viewOrigin(view.width, view.height);
  drawSky(context, view.width, view.height);
  drawShadow(context, terrain, camera, origin);

  const hoverKey = highlight?.hex ? hexKey(highlight.hex.q, highlight.hex.r) : "";
  const brushKeys = new Set((highlight?.brush ?? []).map((cell) => hexKey(cell.q, cell.r)));
  const ordered = [...terrain.cells].sort(
    (a, b) => cellGroundDepth(a.q, a.r, camera) - cellGroundDepth(b.q, b.r, camera),
  );
  for (const cell of ordered) {
    if (!cellOnScreen(cell.q, cell.r, camera, origin, view)) {
      continue;
    }
    drawHex(context, terrain, cell, camera, origin, hoverKey, brushKeys);
  }

  if (highlight?.hex && highlight.vertex !== null && highlight.vertex !== undefined) {
    const top = hexTopPoints(terrain, highlight.hex.q, highlight.hex.r, camera, origin);
    const point = top[highlight.vertex];
    context.beginPath();
    context.fillStyle = "#f4d35e";
    context.strokeStyle = "#3b2f12";
    context.lineWidth = 1.4;
    context.arc(point.x, point.y, 5.2, 0, Math.PI * 2);
    context.fill();
    context.stroke();
  }
}
