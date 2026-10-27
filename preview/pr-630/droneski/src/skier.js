import * as THREE from "three";
import { getTerrainHeight } from "./utils.js";
const SAMPLE_COUNT = 200;
const MAX_OFFSET = 4;
const LOOKAHEAD = 20;
const CURVATURE_GAIN = 120;
const TURN_THRESHOLD = 3e-3;
const SMOOTH_PASSES = 4;
const SMOOTH_RADIUS = 6;
const TURN_SPEED_GAIN = 300;
const MAX_TURN_PENALTY = 0.3;
const GRAVITY = 9.8;
const MAX_LEAN = 0.7;
const LEAN_SMOOTHING = 10;
function computeCurvature(curve) {
  const curvature = [];
  const step = 1 / SAMPLE_COUNT;
  for (let i = 0; i <= SAMPLE_COUNT; i++) {
    const t = i / SAMPLE_COUNT;
    const t0 = Math.max(0, t - step);
    const t1 = Math.min(1, t + step);
    const p0 = curve.getPointAt(t0);
    const p1 = curve.getPointAt(t1);
    const pm = curve.getPointAt(t);
    const ax = pm.x - p0.x, az = pm.z - p0.z;
    const bx = p1.x - pm.x, bz = p1.z - pm.z;
    const cross = ax * bz - az * bx;
    const lenA = Math.sqrt(ax * ax + az * az) || 1e-8;
    const lenB = Math.sqrt(bx * bx + bz * bz) || 1e-8;
    curvature.push(cross / (lenA * lenB));
  }
  return curvature;
}
function racingLineOffsets(curvature) {
  const n = curvature.length;
  const offsets = new Array(n);
  for (let i = 0; i < n; i++) {
    let sum = 0, wSum = 0;
    for (let j = 0; j < LOOKAHEAD && i + j < n; j++) {
      const w = LOOKAHEAD - j;
      sum += curvature[i + j] * w;
      wSum += w;
    }
    offsets[i] = -(sum / wSum) * CURVATURE_GAIN;
  }
  return offsets;
}
function addTurnError(offsets, curvature) {
  const n = curvature.length;
  let inTurn = false;
  let error = 0;
  for (let i = 0; i < n; i++) {
    const mag = Math.abs(curvature[i]);
    if (mag > TURN_THRESHOLD && !inTurn) {
      inTurn = true;
      error = (Math.random() - 0.5) * 3;
    } else if (mag <= TURN_THRESHOLD * 0.5) {
      inTurn = false;
      error = 0;
    }
    if (inTurn) offsets[i] += error;
  }
}
function clampAndSmooth(offsets) {
  const n = offsets.length;
  for (let i = 0; i < n; i++) {
    offsets[i] = Math.max(-MAX_OFFSET, Math.min(MAX_OFFSET, offsets[i]));
  }
  const fade = 15;
  for (let i = 0; i < fade && i < n; i++) {
    const f = i / fade;
    offsets[i] *= f;
    offsets[n - 1 - i] *= f;
  }
  for (let pass = 0; pass < SMOOTH_PASSES; pass++) {
    const copy = offsets.slice();
    for (let i = 0; i < n; i++) {
      let sum = 0, count = 0;
      const lo = Math.max(0, i - SMOOTH_RADIUS);
      const hi = Math.min(n - 1, i + SMOOTH_RADIUS);
      for (let j = lo; j <= hi; j++) {
        sum += copy[j];
        count++;
      }
      offsets[i] = sum / count;
    }
  }
}
function buildRacingLine(curve) {
  const curvature = computeCurvature(curve);
  const offsets = racingLineOffsets(curvature);
  addTurnError(offsets, curvature);
  clampAndSmooth(offsets);
  return { offsets, curvature };
}
function sampleArray(arr, t) {
  const idx = t * (arr.length - 1);
  const i0 = Math.floor(idx);
  const i1 = Math.min(i0 + 1, arr.length - 1);
  const frac = idx - i0;
  return arr[i0] * (1 - frac) + arr[i1] * frac;
}
class Skier {
  mesh;
  progress = 0;
  // 0..1 along the course
  speed = 0;
  baseSpeed = 0.036;
  // units per second in t-space (~28s run)
  finished = false;
  curve;
  terrain;
  prevPosition = new THREE.Vector3();
  elapsed = 0;
  WARMUP_DURATION = 1.5;
  offsets;
  curvature;
  leanAngle = 0;
  prevHeading = 0;
  constructor(curve, terrain) {
    this.curve = curve;
    this.terrain = terrain;
    this.mesh = this.createMesh();
    const racingLine = buildRacingLine(curve);
    this.offsets = racingLine.offsets;
    this.curvature = racingLine.curvature;
    const startPos = curve.getPointAt(0);
    this.mesh.position.copy(startPos);
    this.prevPosition.copy(startPos);
    const startTangent = curve.getTangentAt(0);
    this.prevHeading = Math.atan2(startTangent.x, startTangent.z);
  }
  createMesh() {
    const group = new THREE.Group();
    const bodyGeo = new THREE.ConeGeometry(0.4, 1.5, 6);
    const bodyMat = new THREE.MeshLambertMaterial({ color: 16729156 });
    const body = new THREE.Mesh(bodyGeo, bodyMat);
    body.position.y = 1.2;
    const headGeo = new THREE.SphereGeometry(0.25, 6, 4);
    const headMat = new THREE.MeshLambertMaterial({ color: 16764040 });
    const head = new THREE.Mesh(headGeo, headMat);
    head.position.y = 2.2;
    const skiGeo = new THREE.BoxGeometry(0.12, 0.05, 1.8);
    const skiMat = new THREE.MeshLambertMaterial({ color: 2236962 });
    const leftSki = new THREE.Mesh(skiGeo, skiMat);
    leftSki.position.set(-0.2, 0.05, 0);
    const rightSki = new THREE.Mesh(skiGeo, skiMat);
    rightSki.position.set(0.2, 0.05, 0);
    group.add(body, head, leftSki, rightSki);
    return group;
  }
  getOffsetPosition(t) {
    const pos = this.curve.getPointAt(t);
    const tangent = this.curve.getTangentAt(t);
    const perp = new THREE.Vector3(-tangent.z, 0, tangent.x).normalize();
    const offset = sampleArray(this.offsets, t);
    pos.add(perp.multiplyScalar(offset));
    const terrainY = getTerrainHeight(this.terrain, pos.x, pos.z);
    pos.y = terrainY + 0.5;
    return pos;
  }
  update(dt) {
    if (this.finished) return;
    this.elapsed += dt;
    const warmup = Math.min(this.elapsed / this.WARMUP_DURATION, 1);
    const warmupFactor = 0.3 + 0.7 * warmup * warmup;
    const t = this.progress;
    const ahead = Math.min(t + 0.01, 1);
    const posNow = this.curve.getPointAt(t);
    const posAhead = this.curve.getPointAt(ahead);
    const dy = posAhead.y - posNow.y;
    const slopeFactor = 1 + -dy * 0.5;
    this.speed = this.baseSpeed * Math.max(0.5, Math.min(1.6, slopeFactor)) * warmupFactor;
    const curv = sampleArray(this.curvature, t);
    const turnPenalty = Math.min(Math.abs(curv) * TURN_SPEED_GAIN, MAX_TURN_PENALTY);
    this.speed *= 1 - turnPenalty;
    this.progress += this.speed * dt;
    if (this.progress >= 1) {
      this.progress = 1;
      this.finished = true;
    }
    this.prevPosition.copy(this.mesh.position);
    const newPos = this.getOffsetPosition(this.progress);
    this.mesh.position.copy(newPos);
    const moveDir = newPos.clone().sub(this.prevPosition);
    let targetLean = 0;
    if (moveDir.lengthSq() > 1e-4) {
      const lookTarget = newPos.clone().add(moveDir.normalize());
      this.mesh.lookAt(lookTarget);
      if (dt > 1e-3) {
        const worldSpeed = this.prevPosition.distanceTo(this.mesh.position) / dt;
        const heading = Math.atan2(moveDir.x, moveDir.z);
        let dHeading = heading - this.prevHeading;
        if (dHeading > Math.PI) dHeading -= 2 * Math.PI;
        if (dHeading < -Math.PI) dHeading += 2 * Math.PI;
        this.prevHeading = heading;
        const centripetalAccel = worldSpeed * dHeading / dt;
        targetLean = Math.atan2(centripetalAccel, GRAVITY);
        targetLean = Math.max(-MAX_LEAN, Math.min(MAX_LEAN, targetLean));
      }
    }
    this.leanAngle += (targetLean - this.leanAngle) * Math.min(1, LEAN_SMOOTHING * dt);
    this.mesh.rotateOnAxis(new THREE.Vector3(0, 0, 1), this.leanAngle);
  }
  getPosition() {
    return this.mesh.position.clone();
  }
  getWorldSpeed() {
    return this.prevPosition.distanceTo(this.mesh.position);
  }
}
export {
  Skier
};
