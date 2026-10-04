import { getRatingColor } from "./scoring.js";
const altitudeEl = document.getElementById("altitude-info");
const distanceEl = document.getElementById("distance-info");
const speedEl = document.getElementById("speed-info");
const progressEl = document.getElementById("progress-info");
const reticleEl = document.getElementById("reticle");
const reticleCorners = document.querySelectorAll(".reticle-corner");
const recEl = document.getElementById("rec");
const warningsEl = document.getElementById("warnings");
const muteEl = document.getElementById("mute-indicator");
const ALT_DANGER = 3;
const ALT_CAUTION = 6;
const SKIER_TOO_CLOSE = 8;
const SKIER_CLOSE_CAUTION = 14;
const SKIER_FAR_CAUTION = 50;
const SKIER_TOO_FAR = 70;
const TREE_DANGER = 5;
const TREE_CAUTION = 10;
const BOUNDARY_DANGER = 15;
const BOUNDARY_CAUTION = 30;
function getWarnings(prox) {
  const warnings = [];
  if (prox.altitude < ALT_DANGER) {
    warnings.push({ text: "PULL UP", level: "danger" });
  } else if (prox.altitude < ALT_CAUTION) {
    warnings.push({ text: "LOW ALT", level: "caution" });
  }
  if (prox.distToSkier < SKIER_TOO_CLOSE) {
    warnings.push({ text: "TOO CLOSE", level: "danger" });
  } else if (prox.distToSkier < SKIER_CLOSE_CAUTION) {
    warnings.push({ text: "CLOSE", level: "caution" });
  } else if (prox.distToSkier > SKIER_TOO_FAR) {
    warnings.push({ text: "LOSING SKIER", level: "danger" });
  } else if (prox.distToSkier > SKIER_FAR_CAUTION) {
    warnings.push({ text: "TOO FAR", level: "caution" });
  }
  if (prox.nearestTreeDist < TREE_DANGER) {
    warnings.push({ text: "OBSTACLE", level: "danger" });
  } else if (prox.nearestTreeDist < TREE_CAUTION) {
    warnings.push({ text: "TREES NEARBY", level: "caution" });
  }
  if (prox.boundaryDist < BOUNDARY_DANGER) {
    warnings.push({ text: "BOUNDARY", level: "danger" });
  } else if (prox.boundaryDist < BOUNDARY_CAUTION) {
    warnings.push({ text: "NEAR EDGE", level: "caution" });
  }
  return warnings;
}
function showRec(visible) {
  recEl.classList.toggle("active", visible);
}
function updateHUD(frame, altitude, distToSkier, skierSpeed, progress, proximity) {
  altitudeEl.textContent = `ALT: ${altitude.toFixed(0)}m`;
  distanceEl.textContent = `DIST: ${distToSkier.toFixed(0)}m`;
  speedEl.textContent = `SPD: ${(skierSpeed * 3.6).toFixed(0)} km/h`;
  progressEl.textContent = `PROGRESS: ${(progress * 100).toFixed(0)}%`;
  const color = getRatingColor(frame.frameTotal);
  reticleEl.style.borderColor = color;
  reticleCorners.forEach((c) => c.style.borderColor = color);
  const warnings = getWarnings(proximity);
  if (warnings.length === 0) {
    warningsEl.innerHTML = "";
  } else {
    warningsEl.innerHTML = warnings.map((w) => `<div class="warning ${w.level}">${w.text}</div>`).join("");
  }
}
function showEndScreen(state, crashReason) {
  const endScreen = document.getElementById("end-screen");
  const heading = endScreen.querySelector("h2");
  const breakdown = document.getElementById("score-breakdown");
  if (crashReason) {
    heading.textContent = `CRASH \u2014 ${crashReason}`;
    heading.style.color = "#ff4444";
  } else {
    heading.textContent = "RUN COMPLETE";
    heading.style.color = "#fff";
  }
  const n = state.frameCount || 1;
  const avgCenter = (state.centeringSum / n * 100).toFixed(0);
  const avgVis = (state.visibilitySum / n * 100).toFixed(0);
  const avgDist = (state.distanceSum / n * 100).toFixed(0);
  const avgSmooth = (state.smoothnessSum / n * 100).toFixed(0);
  breakdown.innerHTML = [
    `Centering ........ ${avgCenter}%`,
    `Visibility ....... ${avgVis}%`,
    `Distance ......... ${avgDist}%`,
    `Smoothness ....... ${avgSmooth}%`
  ].join("<br>");
  endScreen.style.display = "flex";
  reticleEl.style.borderColor = "";
  reticleCorners.forEach((c) => c.style.borderColor = "");
  warningsEl.innerHTML = "";
}
function updateMuteIndicator(muted, visible) {
  muteEl.classList.toggle("visible", visible);
  muteEl.classList.toggle("muted", muted);
  muteEl.textContent = muted ? "MUTED [Tab]" : "SOUND [Tab]";
}
function hideEndScreen() {
  document.getElementById("end-screen").style.display = "none";
}
export {
  hideEndScreen,
  showEndScreen,
  showRec,
  updateHUD,
  updateMuteIndicator
};
