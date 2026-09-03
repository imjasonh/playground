import { HeliAudio } from './audio.js';
import { drawScene } from './scene2d.js';
import {
  orbitPosition,
  forwardVector,
  upVector,
  relativeAzimuthDeg,
  elevationDeg,
  distance,
} from './geometry.js';

const ORBIT = { radius: 40, height: 18, angularSpeed: (2 * Math.PI) / 9, phase: 0 };

const canvas = document.getElementById('scene');
const c2d = canvas.getContext('2d');
const overlay = document.getElementById('overlay');
const azEl = document.getElementById('az');
const elEl = document.getElementById('el');
const distEl = document.getElementById('dist');
const compassEl = document.getElementById('compass');

let audio = null;
let running = false;
let yaw = 0;
let startTime = 0;

function resize() {
  const dpr = window.devicePixelRatio || 1;
  canvas.width = canvas.clientWidth * dpr;
  canvas.height = canvas.clientHeight * dpr;
  c2d.setTransform(dpr, 0, 0, dpr, 0, 0);
}
window.addEventListener('resize', resize);
resize();

// Drag left/right to turn your head; arrow keys nudge it too.
let dragging = false;
let lastX = 0;
canvas.addEventListener('pointerdown', (e) => {
  dragging = true;
  lastX = e.clientX;
  canvas.setPointerCapture(e.pointerId);
});
canvas.addEventListener('pointermove', (e) => {
  if (!dragging) return;
  yaw += (e.clientX - lastX) * 0.006;
  lastX = e.clientX;
});
canvas.addEventListener('pointerup', () => {
  dragging = false;
});
window.addEventListener('keydown', (e) => {
  if (e.key === 'ArrowLeft') yaw -= 0.08;
  if (e.key === 'ArrowRight') yaw += 0.08;
});

function frame() {
  if (!running) return;
  const t = (performance.now() - startTime) / 1000;
  const pos = orbitPosition(ORBIT, t);
  const forward = forwardVector(yaw);
  const up = upVector();

  audio.update(pos, forward, up);

  drawScene(c2d, {
    width: canvas.clientWidth,
    height: canvas.clientHeight,
    sourcePos: pos,
    yaw,
    worldRadius: ORBIT.radius,
  });

  const az = relativeAzimuthDeg(pos, [0, 0, 0], yaw);
  azEl.textContent = `${az >= 0 ? '+' : ''}${az.toFixed(0)}\u00b0 ${az > 4 ? 'right' : az < -4 ? 'left' : 'ahead'}`;
  elEl.textContent = `${elevationDeg(pos, [0, 0, 0]).toFixed(0)}\u00b0`;
  distEl.textContent = `${distance(pos, [0, 0, 0]).toFixed(0)} m`;
  compassEl.style.transform = `rotate(${-yaw}rad)`;

  requestAnimationFrame(frame);
}

async function start() {
  if (running) return;
  audio = new HeliAudio();
  await audio.resume();
  audio.fadeIn();
  running = true;
  startTime = performance.now();
  overlay.classList.add('hidden');
  requestAnimationFrame(frame);
}

overlay.addEventListener('click', start);
