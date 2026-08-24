import * as THREE from "three";
import { COURSE_LENGTH } from "./terrain.js";
import { getTerrainHeight } from "./utils.js";
const GATE_COUNT = 20;
const GATE_WIDTH = 8;
const MAX_X = 25;
const NUM_POINTS = 25;
const MIN_BENDINESS = 80;
function generatePoints() {
  const points = [];
  let x = 0;
  let xVel = 0;
  for (let i = 0; i < NUM_POINTS; i++) {
    const t = i / (NUM_POINTS - 1);
    const z = -COURSE_LENGTH / 2 + t * COURSE_LENGTH;
    if (i === 0 || i === NUM_POINTS - 1) {
      x = 0;
      xVel = 0;
    } else {
      const accel = (Math.random() - 0.5) * 18;
      xVel += accel;
      xVel *= 0.7;
      const edgeFade = Math.min(i / 4, (NUM_POINTS - 1 - i) / 4, 1);
      const centerPull = -x * 0.15 * (1 - edgeFade * 0.7);
      xVel += centerPull;
      x += xVel;
      x = Math.max(-MAX_X, Math.min(MAX_X, x));
    }
    points.push(new THREE.Vector3(x, 0, z));
  }
  return points;
}
function createCoursePath() {
  let points;
  do {
    points = generatePoints();
  } while (bendiness(points) < MIN_BENDINESS);
  return new THREE.CatmullRomCurve3(points, false, "catmullrom", 0.5);
}
function bendiness(points) {
  let total = 0;
  for (let i = 1; i < points.length; i++) {
    total += Math.abs(points[i].x - points[i - 1].x);
  }
  return total;
}
function snapCurveToTerrain(curve, terrain) {
  for (const point of curve.points) {
    const h = getTerrainHeight(terrain, point.x, point.z);
    point.y = h + 0.5;
  }
}
function createGates(curve, terrain) {
  const gates = [];
  const poleGeo = new THREE.CylinderGeometry(0.15, 0.15, 3, 6);
  for (let i = 0; i < GATE_COUNT; i++) {
    const t = (i + 1) / (GATE_COUNT + 1);
    const pos = curve.getPointAt(t);
    const tangent = curve.getTangentAt(t);
    const perp = new THREE.Vector3(-tangent.z, 0, tangent.x).normalize();
    const isRed = i % 2 === 0;
    const color = isRed ? 16724787 : 3368703;
    const poleMat = new THREE.MeshLambertMaterial({ color });
    const leftPos = pos.clone().add(perp.clone().multiplyScalar(GATE_WIDTH / 2));
    const rightPos = pos.clone().add(perp.clone().multiplyScalar(-GATE_WIDTH / 2));
    leftPos.y = getTerrainHeight(terrain, leftPos.x, leftPos.z) + 1.5;
    rightPos.y = getTerrainHeight(terrain, rightPos.x, rightPos.z) + 1.5;
    const leftPole = new THREE.Mesh(poleGeo, poleMat);
    leftPole.position.copy(leftPos);
    const rightPole = new THREE.Mesh(poleGeo, poleMat);
    rightPole.position.copy(rightPos);
    gates.push({
      position: pos.clone(),
      left: leftPole,
      right: rightPole,
      index: i
    });
  }
  return gates;
}
function buildArch(center, perp, span, legHeight, tubeRadius, color, groundY) {
  const halfSpan = span / 2;
  const archRise = span * 0.12;
  const path = new THREE.CatmullRomCurve3([
    center.clone().add(perp.clone().multiplyScalar(-halfSpan)).setY(groundY),
    center.clone().add(perp.clone().multiplyScalar(-halfSpan)).setY(groundY + legHeight),
    center.clone().setY(groundY + legHeight + archRise),
    center.clone().add(perp.clone().multiplyScalar(halfSpan)).setY(groundY + legHeight),
    center.clone().add(perp.clone().multiplyScalar(halfSpan)).setY(groundY)
  ], false, "catmullrom", 0.3);
  const geo = new THREE.TubeGeometry(path, 40, tubeRadius, 8, false);
  const mat = new THREE.MeshLambertMaterial({ color });
  return new THREE.Mesh(geo, mat);
}
function createStartLine(curve, terrain) {
  const group = new THREE.Group();
  const pos = curve.getPointAt(0);
  const tangent = curve.getTangentAt(0);
  const perp = new THREE.Vector3(-tangent.z, 0, tangent.x).normalize();
  const groundY = getTerrainHeight(terrain, pos.x, pos.z);
  const span = 14;
  const legHeight = 7;
  group.add(buildArch(pos, perp, span, legHeight, 0.25, 15658734, groundY));
  const bannerGeo = new THREE.PlaneGeometry(span * 0.7, 1.4);
  const bannerMat = new THREE.MeshLambertMaterial({
    color: 2254540,
    side: THREE.DoubleSide
  });
  const banner = new THREE.Mesh(bannerGeo, bannerMat);
  banner.position.copy(pos);
  banner.position.y = groundY + legHeight - 0.3;
  const bannerTarget = banner.position.clone().add(tangent);
  banner.lookAt(bannerTarget);
  group.add(banner);
  return group;
}
function createFinishGate(curve, terrain) {
  const group = new THREE.Group();
  const collisionPositions = [];
  const pos = curve.getPointAt(1);
  const tangent = curve.getTangentAt(1);
  const perp = new THREE.Vector3(-tangent.z, 0, tangent.x).normalize();
  const groundY = getTerrainHeight(terrain, pos.x, pos.z);
  const span = 16;
  const legHeight = 8;
  const tubeRadius = 0.4;
  group.add(buildArch(pos, perp, span, legHeight, tubeRadius, 13378082, groundY));
  const halfSpan = span / 2;
  collisionPositions.push(
    pos.clone().add(perp.clone().multiplyScalar(-halfSpan)).setY(groundY),
    pos.clone().add(perp.clone().multiplyScalar(halfSpan)).setY(groundY),
    pos.clone().setY(groundY + legHeight)
  );
  const bannerGeo = new THREE.PlaneGeometry(span * 0.6, 1.6);
  const bannerMat = new THREE.MeshLambertMaterial({
    color: 16768256,
    side: THREE.DoubleSide
  });
  const banner = new THREE.Mesh(bannerGeo, bannerMat);
  banner.position.copy(pos);
  banner.position.y = groundY + legHeight - 0.5;
  const bannerTarget = banner.position.clone().add(tangent);
  banner.lookAt(bannerTarget);
  group.add(banner);
  return { group, collisionPositions };
}
export {
  createCoursePath,
  createFinishGate,
  createGates,
  createStartLine,
  snapCurveToTerrain
};
