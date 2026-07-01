// Pure geometry for turning device-orientation readings into a bubble level.
//
// A DeviceOrientationEvent reports three angles in degrees:
//   alpha - rotation about the vertical axis (compass); irrelevant to tilt
//   beta  - front/back tilt about the device X axis; 0 when flat, +90 upright
//   gamma - left/right tilt about the device Y axis; 0 when flat
//
// Only beta and gamma change the surface's tilt relative to level, so the math
// here ignores alpha. Everything is framed so a phone lying flat on its back
// reads {0, 0} and the "bubble" floats to the raised (high) side, exactly like
// the air bubble in a carpenter's spirit level.

export const DEG = Math.PI / 180;

// Tilt angle (from level) at which the bubble reaches the edge of the vial.
export const DEFAULT_SENSITIVITY_DEG = 30;

// Total tilt at or below which the surface is reported as level.
export const DEFAULT_TOLERANCE_DEG = 1;

export function clamp(value, min, max) {
  if (!Number.isFinite(value)) {
    return min;
  }
  return Math.min(max, Math.max(min, value));
}

// Wrap an angle in degrees into the [-180, 180) range.
export function normalizeAngle(deg) {
  if (!Number.isFinite(deg)) {
    return 0;
  }
  let wrapped = ((deg + 180) % 360 + 360) % 360;
  return wrapped - 180;
}

// Gravity's component in the plane of the screen, expressed in CSS-pixel axes
// (x grows to the right, y grows downward) and pointing toward the HIGH side of
// the surface — i.e. where the bubble floats. Magnitude is sin(totalTilt), so it
// is 0 when flat and 1 when the screen is vertical.
//
// Derived from the device-frame gravity vector
//   g = (cosβ·sinγ, -sinβ, -cosβ·cosγ)
// whose in-plane part (cosβ·sinγ, -sinβ) points downhill in device axes
// (x right, y up). The bubble floats uphill (negated) and screen-up maps to
// CSS-up (negated again for the y axis), giving the signs below.
export function bubbleVector(beta, gamma) {
  const b = (Number.isFinite(beta) ? beta : 0) * DEG;
  const g = (Number.isFinite(gamma) ? gamma : 0) * DEG;
  return {
    x: -Math.cos(b) * Math.sin(g),
    y: -Math.sin(b),
  };
}

// Total tilt away from level, in degrees (0 = flat, 90 = screen vertical).
export function tiltAngle(beta, gamma) {
  const { x, y } = bubbleVector(beta, gamma);
  return Math.asin(clamp(Math.hypot(x, y), 0, 1)) / DEG;
}

// Signed per-axis tilt angles (degrees) that match the bubble's direction:
//   x > 0  the right edge is raised (bubble drifts right)
//   y > 0  the top/far edge is raised (bubble drifts up the screen)
// `total` is the combined tilt from level and is always >= 0.
export function tiltComponents(beta, gamma) {
  const { x, y } = bubbleVector(beta, gamma);
  return {
    x: Math.asin(clamp(x, -1, 1)) / DEG,
    y: Math.asin(clamp(-y, -1, 1)) / DEG,
    total: tiltAngle(beta, gamma),
  };
}

// Normalized bubble position inside a circular (bullseye) vial. Both components
// live in [-1, 1] and the pair is clamped to the unit disk so the bubble never
// leaves the ring. x is rightward, y is downward (CSS axes).
export function bubbleOffset(beta, gamma, sensitivityDeg = DEFAULT_SENSITIVITY_DEG) {
  const scale = Math.sin(clamp(sensitivityDeg, 1, 89) * DEG) || 1;
  const v = bubbleVector(beta, gamma);
  let x = v.x / scale;
  let y = v.y / scale;
  const magnitude = Math.hypot(x, y);
  if (magnitude > 1) {
    x /= magnitude;
    y /= magnitude;
  }
  return { x, y };
}

// Normalized bubble positions for the two single-axis (tube) vials. Each axis is
// clamped independently to [-1, 1] so a horizontal tube reads left/right tilt and
// a vertical tube reads front/back tilt without one starving the other.
export function axisOffsets(beta, gamma, sensitivityDeg = DEFAULT_SENSITIVITY_DEG) {
  const scale = Math.sin(clamp(sensitivityDeg, 1, 89) * DEG) || 1;
  const v = bubbleVector(beta, gamma);
  return {
    x: clamp(v.x / scale, -1, 1),
    y: clamp(v.y / scale, -1, 1),
  };
}

// Whether the surface is level within `toleranceDeg` of true horizontal.
export function isLevel(beta, gamma, toleranceDeg = DEFAULT_TOLERANCE_DEG) {
  return tiltAngle(beta, gamma) <= toleranceDeg;
}

// Subtract a stored zero-offset (from calibrating against a reference surface)
// from a fresh reading, keeping the result in [-180, 180).
export function applyCalibration(reading, offset) {
  const base = reading || {};
  const zero = offset || {};
  return {
    beta: normalizeAngle((base.beta || 0) - (zero.beta || 0)),
    gamma: normalizeAngle((base.gamma || 0) - (zero.gamma || 0)),
  };
}
