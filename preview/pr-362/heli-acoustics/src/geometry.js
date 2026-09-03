// Pure vector and listener-geometry math, kept free of Web Audio and the DOM so
// it runs under `node --test`. The rest of the app (audio graph, canvas) wires
// these results into browser APIs.
//
// Coordinate frame matches the Web Audio API: right-handed, +x right, +y up,
// +z toward the viewer. A listener facing yaw=0 looks down -z. Positive yaw
// turns the head to the right (clockwise seen from above).

export function sub(a, b) {
  return [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
}

export function add(a, b) {
  return [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
}

export function scale(a, s) {
  return [a[0] * s, a[1] * s, a[2] * s];
}

export function dot(a, b) {
  return a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
}

export function cross(a, b) {
  return [
    a[1] * b[2] - a[2] * b[1],
    a[2] * b[0] - a[0] * b[2],
    a[0] * b[1] - a[1] * b[0],
  ];
}

export function length(a) {
  return Math.hypot(a[0], a[1], a[2]);
}

export function normalize(a) {
  const len = length(a);
  if (len === 0) return [0, 0, 0];
  return [a[0] / len, a[1] / len, a[2] / len];
}

// Position of a source orbiting the origin in the horizontal (xz) plane at a
// fixed height. angularSpeed is radians/second; phase is the starting angle.
// angle 0 places the source on -z (straight ahead of a yaw=0 listener).
export function orbitPosition({ radius, height, angularSpeed, phase = 0 }, t) {
  const a = phase + angularSpeed * t;
  return [radius * Math.sin(a), height, -radius * Math.cos(a)];
}

// Listener basis vectors for a head rotated by yaw about the +y (up) axis.
export function forwardVector(yaw) {
  return [Math.sin(yaw), 0, -Math.cos(yaw)];
}

export function upVector() {
  return [0, 1, 0];
}

export function rightVector(yaw) {
  return normalize(cross(forwardVector(yaw), upVector()));
}

const RAD2DEG = 180 / Math.PI;

// Signed horizontal bearing from the listener's facing direction to the source:
// 0 straight ahead, +90 hard right, -90 hard left, ±180 behind. Elevation is
// ignored so this drives a top-down compass readout.
export function relativeAzimuthDeg(sourcePos, listenerPos, yaw) {
  const dir = sub(sourcePos, listenerPos);
  const flat = [dir[0], 0, dir[2]];
  if (length(flat) === 0) return 0;
  const f = forwardVector(yaw);
  const r = rightVector(yaw);
  return Math.atan2(dot(flat, r), dot(flat, f)) * RAD2DEG;
}

// Angle above (+) or below (-) the listener's horizontal plane.
export function elevationDeg(sourcePos, listenerPos) {
  const dir = sub(sourcePos, listenerPos);
  const horiz = Math.hypot(dir[0], dir[2]);
  return Math.atan2(dir[1], horiz) * RAD2DEG;
}

export function horizontalDistance(sourcePos, listenerPos) {
  const dir = sub(sourcePos, listenerPos);
  return Math.hypot(dir[0], dir[2]);
}

export function distance(sourcePos, listenerPos) {
  return length(sub(sourcePos, listenerPos));
}

// Inverse-distance attenuation matching the Web Audio "inverse" distance model,
// exposed so the HUD and tests can predict the gain the PannerNode applies.
export function inverseDistanceGain(dist, { refDistance = 1, rolloffFactor = 1 } = {}) {
  const d = Math.max(dist, refDistance);
  return refDistance / (refDistance + rolloffFactor * (d - refDistance));
}
