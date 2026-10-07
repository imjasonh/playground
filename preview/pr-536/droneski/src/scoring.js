import * as THREE from "three";
import { clamp } from "./utils.js";
function createScoreState() {
  return {
    total: 0,
    frameCount: 0,
    centeringSum: 0,
    visibilitySum: 0,
    distanceSum: 0,
    smoothnessSum: 0
  };
}
const IDEAL_DISTANCE = 30;
const MAX_DISTANCE = 80;
function scoreFrame(camera, skierWorldPos, droneWorldPos, angularJerk) {
  const screenPos = skierWorldPos.clone().project(camera);
  const inFront = screenPos.z < 1 && screenPos.z > 0;
  const onScreen = Math.abs(screenPos.x) < 1 && Math.abs(screenPos.y) < 1;
  const visibility = inFront && onScreen ? 1 : 0;
  const centerDist = Math.sqrt(screenPos.x * screenPos.x + screenPos.y * screenPos.y);
  const centering = visibility * clamp(1 - centerDist / 1.2, 0, 1);
  const dist = droneWorldPos.distanceTo(skierWorldPos);
  const distNorm = Math.abs(dist - IDEAL_DISTANCE) / MAX_DISTANCE;
  const distance = clamp(1 - distNorm * 2, 0, 1);
  const jerkPenalty = clamp(angularJerk * 50, 0, 1);
  const smoothness = 1 - jerkPenalty;
  const frameTotal = centering * 0.35 + visibility * 0.25 + distance * 0.2 + smoothness * 0.2;
  return { centering, visibility, distance, smoothness, frameTotal };
}
function updateScoreState(state, frame) {
  state.frameCount++;
  state.centeringSum += frame.centering;
  state.visibilitySum += frame.visibility;
  state.distanceSum += frame.distance;
  state.smoothnessSum += frame.smoothness;
  state.total += frame.frameTotal * 10;
}
function getRatingColor(frameTotal) {
  if (frameTotal > 0.85) return "#ffdd00";
  if (frameTotal > 0.7) return "#44ff44";
  if (frameTotal > 0.5) return "#88ccff";
  if (frameTotal > 0.3) return "#ffaa44";
  return "#ff4444";
}
export {
  createScoreState,
  getRatingColor,
  scoreFrame,
  updateScoreState
};
