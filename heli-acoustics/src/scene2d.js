// Top-down debug view: you (the listener) sit at the centre facing up the
// screen by default; drag to turn. The helicopter orbits. This is deliberately
// a flat 2D map for M0 — the real 3D urban scene arrives in M1.

import { forwardVector, rightVector } from './geometry.js';

export function drawScene(c2d, { width, height, sourcePos, yaw, worldRadius }) {
  c2d.clearRect(0, 0, width, height);
  const cx = width / 2;
  const cy = height / 2;
  // Fit the orbit comfortably inside the smaller canvas dimension.
  const pxPerMeter = (Math.min(width, height) * 0.36) / worldRadius;

  // World +x is screen right, world -z is screen up (into the distance).
  const toScreen = (p) => [cx + p[0] * pxPerMeter, cy + p[2] * pxPerMeter];

  // Range rings.
  c2d.strokeStyle = 'rgba(120,180,255,0.15)';
  c2d.lineWidth = 1;
  for (let r = 1; r <= 3; r++) {
    c2d.beginPath();
    c2d.arc(cx, cy, (worldRadius * pxPerMeter * r) / 3, 0, Math.PI * 2);
    c2d.stroke();
  }

  // Listener facing wedge.
  const f = forwardVector(yaw);
  const r = rightVector(yaw);
  const reach = worldRadius * pxPerMeter * 1.15;
  const spread = 0.32;
  const tip = [cx + f[0] * reach, cy + f[2] * reach];
  const leftEdge = [
    cx + (f[0] - r[0] * spread) * reach,
    cy + (f[2] - r[2] * spread) * reach,
  ];
  const rightEdge = [
    cx + (f[0] + r[0] * spread) * reach,
    cy + (f[2] + r[2] * spread) * reach,
  ];
  const grad = c2d.createLinearGradient(cx, cy, tip[0], tip[1]);
  grad.addColorStop(0, 'rgba(120,180,255,0.30)');
  grad.addColorStop(1, 'rgba(120,180,255,0)');
  c2d.fillStyle = grad;
  c2d.beginPath();
  c2d.moveTo(cx, cy);
  c2d.lineTo(leftEdge[0], leftEdge[1]);
  c2d.lineTo(tip[0], tip[1]);
  c2d.lineTo(rightEdge[0], rightEdge[1]);
  c2d.closePath();
  c2d.fill();

  // Listener head.
  c2d.fillStyle = '#7fb4ff';
  c2d.beginPath();
  c2d.arc(cx, cy, 7, 0, Math.PI * 2);
  c2d.fill();
  // Nose marker so the facing direction is unambiguous.
  c2d.strokeStyle = '#cfe4ff';
  c2d.lineWidth = 2;
  c2d.beginPath();
  c2d.moveTo(cx, cy);
  c2d.lineTo(cx + f[0] * 16, cy + f[2] * 16);
  c2d.stroke();

  // Helicopter.
  const [hx, hy] = toScreen(sourcePos);
  c2d.fillStyle = '#ff5a5a';
  c2d.beginPath();
  c2d.arc(hx, hy, 6, 0, Math.PI * 2);
  c2d.fill();
  c2d.strokeStyle = 'rgba(255,90,90,0.4)';
  c2d.lineWidth = 1;
  c2d.beginPath();
  c2d.moveTo(cx, cy);
  c2d.lineTo(hx, hy);
  c2d.stroke();
}
