import { HeliAudio } from './audio.js';
import { drawScene } from './scene2d.js';
import { proveHrtfBinaural } from './hrtfProof.js';
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
const ctxEl = document.getElementById('ctx');
const leftBar = document.getElementById('left-bar');
const rightBar = document.getElementById('right-bar');
const leftN = document.getElementById('left-n');
const rightN = document.getElementById('right-n');
const balEl = document.getElementById('bal');
const proofEl = document.getElementById('proof');
const compassEl = document.getElementById('compass');

let audio = null;
let running = false;
let yaw = 0;
let startTime = 0;

// Rolling samples of measured ear balance vs bearing, exposed for automated
// audio verification (see scripts/sample-live-ears.mjs).
const earSamples = [];
window.__heliEarSamples = earSamples;
window.__heliGetAudio = () => audio;

function resize() {
  const dpr = window.devicePixelRatio || 1;
  canvas.width = canvas.clientWidth * dpr;
  canvas.height = canvas.clientHeight * dpr;
  c2d.setTransform(dpr, 0, 0, dpr, 0, 0);
}
window.addEventListener('resize', resize);
resize();

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

function paintMeters(levels) {
  const scale = 8; // RMS of the heli synth sits well under 0.2
  const lPct = Math.min(100, levels.left * scale * 100);
  const rPct = Math.min(100, levels.right * scale * 100);
  leftBar.style.width = `${lPct}%`;
  rightBar.style.width = `${rPct}%`;
  leftN.textContent = levels.left.toFixed(3);
  rightN.textContent = levels.right.toFixed(3);
  const side =
    levels.balance > 0.05 ? 'R louder' : levels.balance < -0.05 ? 'L louder' : 'even';
  balEl.textContent = `${levels.balance >= 0 ? '+' : ''}${levels.balance.toFixed(2)} (${side})`;
  ctxEl.textContent = levels.contextState;
}

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

  const levels = audio.earLevels();
  paintMeters(levels);
  if (levels.left + levels.right > 0.001) {
    earSamples.push({ t, az, balance: levels.balance, left: levels.left, right: levels.right });
    if (earSamples.length > 600) earSamples.shift();
  }

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

  // Offline HRTF proof runs once at start; result lands in the HUD.
  proofEl.textContent = 'running\u2026';
  try {
    const verdict = await proveHrtfBinaural();
    window.__heliHrtfProof = verdict;
    proofEl.textContent = verdict.pass ? 'PASS' : 'FAIL';
    proofEl.className = `val ${verdict.pass ? 'pass' : 'fail'}`;
  } catch (err) {
    window.__heliHrtfProof = { pass: false, reason: String(err) };
    proofEl.textContent = 'ERROR';
    proofEl.className = 'val fail';
  }
}

overlay.addEventListener('click', start);
