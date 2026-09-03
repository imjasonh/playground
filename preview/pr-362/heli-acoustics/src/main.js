import { HeliAudio } from './audio.js';
import { FpsControls, coarsePointer } from './controls.js';
import { createCityScene, createRenderer, createCamera } from './scene3d.js';
import { DebugRays } from './debugRays.js';
import { BUILDINGS, helicopterPath } from './city.js';
import { occlusionAmount } from './occlusion.js';
import { computeReflections } from './reflections.js';
import { proveHrtfBinaural } from './hrtfProof.js';
import { relativeAzimuthDeg, distance } from './geometry.js';

const canvas = document.getElementById('scene');
const overlay = document.getElementById('overlay');
const azEl = document.getElementById('az');
const distEl = document.getElementById('dist');
const ctxEl = document.getElementById('ctx');
const occEl = document.getElementById('occ');
const refEl = document.getElementById('refn');
const balEl = document.getElementById('bal');
const proofEl = document.getElementById('proof');
const leftBar = document.getElementById('left-bar');
const rightBar = document.getElementById('right-bar');
const leftN = document.getElementById('left-n');
const rightN = document.getElementById('right-n');
const togOcclusion = document.getElementById('tog-occlusion');
const togReflections = document.getElementById('tog-reflections');
const togRays = document.getElementById('tog-rays');

const { scene, heli, rotor } = createCityScene();
const renderer = createRenderer(canvas);
const camera = createCamera(canvas.clientWidth / Math.max(1, canvas.clientHeight));
const controls = new FpsControls(canvas);
const debugRays = new DebugRays(scene);

let audio = null;
let running = false;
let startTime = 0;
let lastFrame = 0;
let occlusionOn = true;
let reflectionsOn = true;
let raysOn = true;

const earSamples = [];
window.__heliEarSamples = earSamples;
window.__heliGetAudio = () => audio;

function resize() {
  const w = canvas.clientWidth;
  const h = canvas.clientHeight;
  renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
  renderer.setSize(w, h, false);
  camera.aspect = w / Math.max(1, h);
  camera.updateProjectionMatrix();
}
window.addEventListener('resize', resize);
resize();

function setOcclusion(on) {
  occlusionOn = on;
  togOcclusion.checked = on;
  audio?.setOcclusionEnabled(on);
}

function setReflections(on) {
  reflectionsOn = on;
  togReflections.checked = on;
  audio?.setReflectionsEnabled(on);
}

function setRays(on) {
  raysOn = on;
  togRays.checked = on;
  debugRays.setVisible(on);
}

togOcclusion.addEventListener('change', () => setOcclusion(togOcclusion.checked));
togReflections.addEventListener('change', () => setReflections(togReflections.checked));
togRays.addEventListener('change', () => setRays(togRays.checked));

// Keep pointer-lock clicks on the canvas; when using the control panel, exit
// pointer lock so the checkboxes are clickable without hunting for Esc.
document.getElementById('controls').addEventListener('pointerdown', (e) => {
  e.stopPropagation();
  if (document.pointerLockElement) document.exitPointerLock();
});

window.addEventListener('keydown', (e) => {
  if (e.code === 'KeyO') setOcclusion(!occlusionOn);
  if (e.code === 'KeyR') setReflections(!reflectionsOn);
  if (e.code === 'KeyG') setRays(!raysOn);
});

function paintMeters(levels) {
  const scale = 8;
  leftBar.style.width = `${Math.min(100, levels.left * scale * 100)}%`;
  rightBar.style.width = `${Math.min(100, levels.right * scale * 100)}%`;
  leftN.textContent = levels.left.toFixed(3);
  rightN.textContent = levels.right.toFixed(3);
  const side =
    levels.balance > 0.05 ? 'R louder' : levels.balance < -0.05 ? 'L louder' : 'even';
  balEl.textContent = `${levels.balance >= 0 ? '+' : ''}${levels.balance.toFixed(2)} (${side})`;
  ctxEl.textContent = levels.contextState;
}

function frame(now) {
  if (!running) return;
  const dt = Math.min(0.05, (now - lastFrame) / 1000 || 0.016);
  lastFrame = now;
  const t = (now - startTime) / 1000;

  controls.update(dt);
  const listenerPos = controls.position;
  const forward = controls.forward();
  const up = controls.up();
  camera.position.set(listenerPos[0], listenerPos[1], listenerPos[2]);
  camera.lookAt(
    listenerPos[0] + forward[0],
    listenerPos[1] + forward[1],
    listenerPos[2] + forward[2],
  );

  const sourcePos = helicopterPath(t);
  heli.position.set(sourcePos[0], sourcePos[1], sourcePos[2]);
  rotor.rotation.y = t * 40;

  const occ = occlusionAmount(listenerPos, sourcePos, BUILDINGS);
  const reflections = computeReflections(listenerPos, sourcePos, BUILDINGS, { limit: 8 });

  audio.update(sourcePos, listenerPos, forward, up, {
    occlusion: occ,
    reflections,
  });

  debugRays.update(listenerPos, sourcePos, occ > 0, reflectionsOn ? reflections : []);

  const az = relativeAzimuthDeg(sourcePos, listenerPos, controls.yaw);
  azEl.textContent = `${az >= 0 ? '+' : ''}${az.toFixed(0)}\u00b0`;
  distEl.textContent = `${distance(sourcePos, listenerPos).toFixed(0)} m`;
  occEl.textContent = `${occlusionOn ? (occ > 0 ? 'blocked' : 'clear') : 'off'}`;
  refEl.textContent = reflectionsOn ? `${reflections.length} taps` : 'off';

  const levels = audio.earLevels();
  paintMeters(levels);
  if (levels.left + levels.right > 0.001) {
    earSamples.push({ t, az, balance: levels.balance, left: levels.left, right: levels.right, occ });
    if (earSamples.length > 600) earSamples.shift();
  }

  renderer.render(scene, camera);
  requestAnimationFrame(frame);
}

async function start() {
  if (running) return;
  audio = new HeliAudio();
  audio.setOcclusionEnabled(occlusionOn);
  audio.setReflectionsEnabled(reflectionsOn);
  await audio.resume();
  audio.fadeIn();
  running = true;
  startTime = performance.now();
  lastFrame = startTime;
  overlay.classList.add('hidden');
  // Pointer lock is a desktop convenience; phones use drag-to-look instead.
  if (!coarsePointer()) canvas.requestPointerLock?.();
  requestAnimationFrame(frame);

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

overlay.addEventListener('pointerup', (e) => {
  // Treat a tap or click on the start screen as start. Ignore non-primary mouse.
  if (e.pointerType === 'mouse' && e.button !== 0) return;
  start();
});
// Keep click as a fallback for older browsers that synthesize it from taps.
overlay.addEventListener('click', start);
