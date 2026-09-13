import * as THREE from "three";
import { createTerrain, createTrees, BOUNDS } from "./terrain.js";
import {
  createCoursePath,
  snapCurveToTerrain,
  createGates,
  createStartLine,
  createFinishGate
} from "./course.js";
import { Skier } from "./skier.js";
import { Drone } from "./drone.js";
import { scoreFrame, updateScoreState, createScoreState } from "./scoring.js";
import { updateHUD, showRec, showEndScreen, hideEndScreen, updateMuteIndicator } from "./hud.js";
import { Minimap } from "./minimap.js";
import { DroneAudio } from "./audio.js";
let state = "start";
let scoreState;
const renderer = new THREE.WebGLRenderer({ antialias: true });
renderer.setSize(window.innerWidth, window.innerHeight);
renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
renderer.shadowMap.enabled = true;
renderer.shadowMap.type = THREE.PCFSoftShadowMap;
document.body.prepend(renderer.domElement);
const scene = new THREE.Scene();
scene.background = new THREE.Color(11197934);
scene.fog = new THREE.Fog(11197934, 150, 500);
const camera = new THREE.PerspectiveCamera(70, window.innerWidth / window.innerHeight, 0.5, 600);
const ambient = new THREE.AmbientLight(8952251, 0.6);
scene.add(ambient);
const sun = new THREE.DirectionalLight(16777198, 1.2);
sun.position.set(50, 100, -50);
sun.castShadow = true;
sun.shadow.mapSize.set(2048, 2048);
sun.shadow.camera.left = -200;
sun.shadow.camera.right = 200;
sun.shadow.camera.top = 200;
sun.shadow.camera.bottom = -200;
sun.shadow.camera.far = 500;
scene.add(sun);
const hemi = new THREE.HemisphereLight(8961023, 4478259, 0.4);
scene.add(hemi);
const terrain = createTerrain();
scene.add(terrain);
const { group: treeGroup, positions: treePositions } = createTrees(terrain);
scene.add(treeGroup);
let courseCurve;
let courseGroup;
let allCollisionPositions;
let gatePositions;
let skier;
let minimap;
const drone = new Drone(camera, terrain);
let droneAudio = null;
function buildCourse() {
  if (courseGroup) {
    scene.remove(courseGroup);
    courseGroup.traverse((obj) => {
      if (obj instanceof THREE.Mesh) {
        obj.geometry.dispose();
        if (Array.isArray(obj.material)) {
          obj.material.forEach((m) => m.dispose());
        } else {
          obj.material.dispose();
        }
      }
    });
  }
  courseGroup = new THREE.Group();
  courseCurve = createCoursePath();
  snapCurveToTerrain(courseCurve, terrain);
  const gates = createGates(courseCurve, terrain);
  for (const gate of gates) {
    courseGroup.add(gate.left);
    courseGroup.add(gate.right);
  }
  gatePositions = gates.map((g) => g.position);
  courseGroup.add(createStartLine(courseCurve, terrain));
  const finishGate = createFinishGate(courseCurve, terrain);
  courseGroup.add(finishGate.group);
  allCollisionPositions = [...treePositions, ...finishGate.collisionPositions];
  scene.add(courseGroup);
  const coursePoints = courseCurve.getPoints(100);
  minimap = new Minimap(coursePoints);
}
function resetGame() {
  scoreState = createScoreState();
  if (skier) skier.mesh.removeFromParent();
  buildCourse();
  skier = new Skier(courseCurve, terrain);
  scene.add(skier.mesh);
  drone.reset();
  const startPos = courseCurve.getPointAt(0);
  drone.setPosition(new THREE.Vector3(startPos.x + 10, startPos.y + 20, startPos.z - 15));
  const dx = startPos.x - drone.getPosition().x;
  const dz = startPos.z - drone.getPosition().z;
  const yaw = Math.atan2(-dx, -dz);
  drone.setLookDirection(yaw, -0.2);
  showRec(false);
  hideEndScreen();
  updateMuteIndicator(droneAudio?.isMuted() ?? false, false);
}
resetGame();
window.addEventListener("resize", () => {
  camera.aspect = window.innerWidth / window.innerHeight;
  camera.updateProjectionMatrix();
  renderer.setSize(window.innerWidth, window.innerHeight);
});
const startScreen = document.getElementById("start-screen");
const countdownEl = document.getElementById("countdown");
const countdownNumber = document.getElementById("countdown-number");
const endScreen = document.getElementById("end-screen");
startScreen.addEventListener("click", () => {
  if (state !== "start") return;
  if (!droneAudio) {
    droneAudio = new DroneAudio();
  }
  droneAudio.resume();
  startScreen.style.display = "none";
  drone.lockPointer();
  startCountdown();
});
endScreen.addEventListener("click", () => {
  if (state !== "ended") return;
  resetGame();
  if (droneAudio) droneAudio.resume();
  drone.lockPointer();
  startCountdown();
});
document.addEventListener("click", () => {
  if (state === "playing" || state === "countdown") {
    if (!document.pointerLockElement) {
      drone.lockPointer();
    }
  }
});
document.addEventListener("keydown", (e) => {
  if (e.code === "Tab") {
    e.preventDefault();
    if (droneAudio) {
      droneAudio.setMuted(!droneAudio.isMuted());
      updateMuteIndicator(droneAudio.isMuted(), state === "playing");
    }
  }
});
function startCountdown() {
  state = "countdown";
  countdownEl.style.display = "flex";
  let count = 3;
  countdownNumber.textContent = count.toString();
  const interval = setInterval(() => {
    count--;
    if (count > 0) {
      countdownNumber.textContent = count.toString();
    } else if (count === 0) {
      countdownNumber.textContent = "GO!";
    } else {
      clearInterval(interval);
      countdownEl.style.display = "none";
      state = "playing";
      showRec(true);
      if (droneAudio) droneAudio.fadeIn();
      updateMuteIndicator(droneAudio?.isMuted() ?? false, true);
    }
  }, 1e3);
}
function checkOutOfBounds() {
  const pos = drone.getPosition();
  if (pos.x < BOUNDS.minX || pos.x > BOUNDS.maxX || pos.z < BOUNDS.minZ || pos.z > BOUNDS.maxZ) {
    drone.triggerCrash("OUT OF BOUNDS");
  }
}
const clock = new THREE.Clock();
function animate() {
  requestAnimationFrame(animate);
  const dt = Math.min(clock.getDelta(), 0.05);
  drone.update(dt, allCollisionPositions);
  if (state === "playing") {
    checkOutOfBounds();
    if (droneAudio) droneAudio.update(drone.getAudioState());
    if (drone.crashed) {
      state = "ended";
      showRec(false);
      if (droneAudio) droneAudio.fadeOut();
      document.exitPointerLock();
      showEndScreen(scoreState, drone.crashReason);
    }
    skier.update(dt);
    const skierPos = skier.getPosition();
    const dronePos = drone.getPosition();
    const dist = dronePos.distanceTo(skierPos);
    const frame = scoreFrame(camera, skierPos, dronePos, drone.angularJerk);
    updateScoreState(scoreState, frame);
    let nearestTreeDist = Infinity;
    for (const tp of treePositions) {
      const d = Math.sqrt(
        (dronePos.x - tp.x) ** 2 + (dronePos.y - tp.y) ** 2 + (dronePos.z - tp.z) ** 2
      );
      if (d < nearestTreeDist) nearestTreeDist = d;
    }
    const boundaryDist = Math.min(
      dronePos.x - BOUNDS.minX,
      BOUNDS.maxX - dronePos.x,
      dronePos.z - BOUNDS.minZ,
      BOUNDS.maxZ - dronePos.z
    );
    const proximity = {
      altitude: drone.getAltitudeAboveTerrain(),
      distToSkier: dist,
      nearestTreeDist,
      boundaryDist
    };
    updateHUD(
      frame,
      drone.getAltitudeAboveTerrain(),
      dist,
      skier.getWorldSpeed() / dt,
      skier.progress,
      proximity
    );
    minimap.update(skierPos, dronePos, gatePositions);
    if (skier.finished) {
      state = "ended";
      showRec(false);
      if (droneAudio) droneAudio.fadeOut();
      document.exitPointerLock();
      showEndScreen(scoreState);
    }
  } else {
    minimap.update(
      skier.getPosition(),
      drone.getPosition(),
      gatePositions
    );
  }
  renderer.render(scene, camera);
}
animate();
