import { HeliAudio } from './audio.js';
import { FpsControls, coarsePointer } from './controls.js';
import { createCityScene, createRenderer, createCamera } from './scene3d.js';
import { DebugRays } from './debugRays.js';
import { BUILDINGS, helicopterPath, helicopterVelocity } from './city.js';
import { GpuAcoustics } from './acousticsGpu.js';
import { proveHrtfBinaural } from './hrtfProof.js';
import { relativeAzimuthDeg, distance } from './geometry.js';

const canvas = document.getElementById('scene');
const overlay = document.getElementById('overlay');
const azEl = document.getElementById('az');
const distEl = document.getElementById('dist');
const ctxEl = document.getElementById('ctx');
const occEl = document.getElementById('occ');
const refEl = document.getElementById('refn');
const revEl = document.getElementById('rev');
const gpuEl = document.getElementById('gpu');
const balEl = document.getElementById('bal');
const proofEl = document.getElementById('proof');
const leftBar = document.getElementById('left-bar');
const rightBar = document.getElementById('right-bar');
const leftN = document.getElementById('left-n');
const rightN = document.getElementById('right-n');
const togOcclusion = document.getElementById('tog-occlusion');
const togReflections = document.getElementById('tog-reflections');
const togReverb = document.getElementById('tog-reverb');
const togRays = document.getElementById('tog-rays');

const { scene, heli, rotor } = createCityScene();
const renderer = createRenderer(canvas);
const camera = createCamera(canvas.clientWidth / Math.max(1, canvas.clientHeight));
const controls = new FpsControls(canvas);
const debugRays = new DebugRays(scene, { maxTaps: 16 });
const gpuAcoustics = new GpuAcoustics({ buildings: BUILDINGS, limit: 16 });

let audio = null;
let running = false;
let startTime = 0;
let lastFrame = 0;
let occlusionOn = true;
let reflectionsOn = true;
let reverbOn = true;
let raysOn = true;
let acousticsBusy = false;
let latestAcoustics = {
  occlusion: 0,
  reflections: [],
  enclosure: { amount: 0, rt60Sec: 0.3 },
  backend: 'init',
};

const earSamples = [];
window.__heliEarSamples = earSamples;
window.__heliGetAudio = () => audio;
window.__heliGetAcoustics = () => latestAcoustics;
window.__heliGpuAcoustics = gpuAcoustics;

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

function setReverb(on) {
  reverbOn = on;
  togReverb.checked = on;
  audio?.setReverbEnabled(on);
}

function setRays(on) {
  raysOn = on;
  togRays.checked = on;
  debugRays.setVisible(on);
}

togOcclusion.addEventListener('change', () => setOcclusion(togOcclusion.checked));
togReflections.addEventListener('change', () => setReflections(togReflections.checked));
togReverb.addEventListener('change', () => setReverb(togReverb.checked));
togRays.addEventListener('change', () => setRays(togRays.checked));

document.getElementById('controls').addEventListener('pointerdown', (e) => {
  e.stopPropagation();
  if (document.pointerLockElement) document.exitPointerLock();
});

window.addEventListener('keydown', (e) => {
  if (e.code === 'KeyO') setOcclusion(!occlusionOn);
  if (e.code === 'KeyR') setReflections(!reflectionsOn);
  if (e.code === 'KeyV') setReverb(!reverbOn);
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

function kickAcoustics(listenerPos, sourcePos) {
  if (acousticsBusy) return;
  acousticsBusy = true;
  gpuAcoustics
    .compute(listenerPos, sourcePos)
    .then((result) => {
      latestAcoustics = result;
      acousticsBusy = false;
    })
    .catch((err) => {
      console.error('acoustics compute failed (WebGPU required):', err);
      latestAcoustics = {
        ...latestAcoustics,
        backend: gpuAcoustics.backend === 'lost' ? 'lost' : 'unavailable',
        reflections: [],
        occlusion: 0,
      };
      acousticsBusy = false;
    });
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
  const sourceVelocity = helicopterVelocity(t);
  heli.position.set(sourcePos[0], sourcePos[1], sourcePos[2]);
  rotor.rotation.y = t * 40;

  kickAcoustics(listenerPos.slice(), sourcePos.slice());
  const { occlusion: occ, reflections, enclosure, backend } = latestAcoustics;
  if (backend === 'unavailable' || backend === 'lost') {
    if (gpuEl) {
      gpuEl.textContent = backend;
      gpuEl.className = 'val fail';
    }
    renderer.render(scene, camera);
    requestAnimationFrame(frame);
    return;
  }

  audio.update(sourcePos, listenerPos, forward, up, {
    occlusion: occ,
    reflections,
    enclosure,
    irBins: latestAcoustics.irBins,
    sourceVelocity,
  });

  debugRays.update(listenerPos, sourcePos, occ > 0.15, reflectionsOn ? reflections : []);

  const az = relativeAzimuthDeg(sourcePos, listenerPos, controls.yaw);
  azEl.textContent = `${az >= 0 ? '+' : ''}${az.toFixed(0)}\u00b0`;
  distEl.textContent = `${distance(sourcePos, listenerPos).toFixed(0)} m`;
  occEl.textContent = `${occlusionOn ? (occ > 0.15 ? `shadow ${(occ * 100).toFixed(0)}%` : 'clear') : 'off'}`;
  const o1 = reflections.filter((r) => r.order === 1).length;
  const o2 = reflections.filter((r) => r.order === 2).length;
  const o3 = reflections.filter((r) => r.order === 3).length;
  const dif = reflections.filter((r) => r.kind === 'diffraction').length;
  refEl.textContent = reflectionsOn
    ? `${reflections.length} (${o1}+${o2}+${o3}/d${dif})`
    : 'off';
  revEl.textContent = reverbOn
    ? `${(enclosure.amount * 100).toFixed(0)}% / ${enclosure.rt60Sec.toFixed(2)}s${latestAcoustics.irBins ? ' sto' : ''}`
    : 'off';
  if (gpuEl) gpuEl.textContent = backend;

  const levels = audio.earLevels();
  paintMeters(levels);
  if (levels.left + levels.right > 0.001) {
    earSamples.push({
      t,
      az,
      balance: levels.balance,
      left: levels.left,
      right: levels.right,
      occ,
      enclosure: enclosure.amount,
      backend,
    });
    if (earSamples.length > 600) earSamples.shift();
  }

  renderer.render(scene, camera);
  requestAnimationFrame(frame);
}

async function start() {
  if (running) return;
  try {
    await gpuAcoustics.init();
  } catch (err) {
    latestAcoustics.backend = 'unavailable';
    if (gpuEl) {
      gpuEl.textContent = 'unavailable';
      gpuEl.className = 'val fail';
    }
    const msg = document.createElement('p');
    msg.className = 'phones';
    msg.textContent = `WebGPU is required for acoustics. ${err?.message || err}`;
    overlay.querySelector('.go')?.replaceWith(msg);
    return;
  }
  latestAcoustics.backend = gpuAcoustics.backend;
  if (gpuEl) gpuEl.textContent = gpuAcoustics.backend;

  audio = new HeliAudio();
  audio.setOcclusionEnabled(occlusionOn);
  audio.setReflectionsEnabled(reflectionsOn);
  audio.setReverbEnabled(reverbOn);
  await audio.resume();
  audio.fadeIn();
  running = true;
  startTime = performance.now();
  lastFrame = startTime;
  overlay.classList.add('hidden');
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
  if (e.pointerType === 'mouse' && e.button !== 0) return;
  start();
});
overlay.addEventListener('click', start);
