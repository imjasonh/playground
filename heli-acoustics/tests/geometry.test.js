import { test } from 'node:test';
import assert from 'node:assert/strict';
import {
  orbitPosition,
  forwardVector,
  rightVector,
  relativeAzimuthDeg,
  elevationDeg,
  horizontalDistance,
  distance,
  inverseDistanceGain,
} from '../src/geometry.js';

const close = (a, b, eps = 1e-9) => assert.ok(Math.abs(a - b) <= eps, `${a} !== ${b}`);
const closeVec = (a, b, eps = 1e-9) => a.forEach((v, i) => close(v, b[i], eps));

test('orbit angle 0 is straight ahead on -z', () => {
  const p = orbitPosition({ radius: 10, height: 3, angularSpeed: 1, phase: 0 }, 0);
  closeVec(p, [0, 3, -10]);
});

test('orbit quarter turn moves to +x (listener right)', () => {
  const p = orbitPosition({ radius: 10, height: 3, angularSpeed: Math.PI / 2, phase: 0 }, 1);
  closeVec(p, [10, 3, 0], 1e-9);
});

test('forward vector faces -z at yaw 0 and +x at yaw +90', () => {
  closeVec(forwardVector(0), [0, 0, -1]);
  closeVec(forwardVector(Math.PI / 2), [1, 0, 0], 1e-12);
});

test('right vector is +x at yaw 0', () => {
  closeVec(rightVector(0), [1, 0, 0], 1e-12);
});

test('azimuth is 0 straight ahead, +90 to the right, -90 to the left', () => {
  close(relativeAzimuthDeg([0, 0, -10], [0, 0, 0], 0), 0);
  close(relativeAzimuthDeg([10, 0, 0], [0, 0, 0], 0), 90, 1e-9);
  close(relativeAzimuthDeg([-10, 0, 0], [0, 0, 0], 0), -90, 1e-9);
  close(Math.abs(relativeAzimuthDeg([0, 0, 10], [0, 0, 0], 0)), 180, 1e-9);
});

test('turning the head re-references azimuth', () => {
  // Source dead ahead, then the listener turns 90 deg right: source is now left.
  close(relativeAzimuthDeg([0, 0, -10], [0, 0, 0], 0), 0);
  close(relativeAzimuthDeg([0, 0, -10], [0, 0, 0], Math.PI / 2), -90, 1e-9);
});

test('elevation is positive above the listener', () => {
  close(elevationDeg([0, 10, 0], [0, 0, 0]), 90, 1e-9);
  close(elevationDeg([10, 10, 0], [0, 0, 0]), 45, 1e-9);
  close(elevationDeg([10, 0, 0], [0, 0, 0]), 0);
});

test('distance helpers', () => {
  close(horizontalDistance([3, 100, 4], [0, 0, 0]), 5);
  close(distance([3, 4, 12], [0, 0, 0]), 13);
});

test('inverse-distance gain falls off and is clamped inside refDistance', () => {
  close(inverseDistanceGain(1, { refDistance: 1, rolloffFactor: 1 }), 1);
  close(inverseDistanceGain(0.2, { refDistance: 1, rolloffFactor: 1 }), 1);
  close(inverseDistanceGain(11, { refDistance: 1, rolloffFactor: 1 }), 1 / 11, 1e-12);
});
