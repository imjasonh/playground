import * as THREE from "three";
const TERRAIN_WIDTH = 600;
const TERRAIN_DEPTH = 1400;
const SEGMENTS_X = 120;
const SEGMENTS_Z = 280;
const COURSE_LENGTH = 600;
const SLOPE_HEIGHT = 160;
const BOUNDS = {
  minX: -130,
  maxX: 130,
  minZ: -370,
  maxZ: 370
};
function pseudoNoise(x, z) {
  const s = Math.sin(x * 0.05 + z * 0.03) * 0.5 + Math.sin(x * 0.12 - z * 0.07) * 0.3 + Math.sin(x * 0.03 + z * 0.11) * 0.2;
  return s;
}
function heightAt(x, z) {
  const courseHalf = COURSE_LENGTH / 2;
  let baseY;
  if (z < -courseHalf) {
    const extra = (-courseHalf - z) / 400;
    baseY = SLOPE_HEIGHT + extra * 40 + extra * extra * 50;
  } else if (z > courseHalf) {
    const extra = (z - courseHalf) / 400;
    baseY = Math.max(-5, -extra * 12);
  } else {
    const t = (z + courseHalf) / COURSE_LENGTH;
    baseY = SLOPE_HEIGHT * (1 - t);
  }
  const absX = Math.abs(x);
  if (absX > 40) {
    const ridgeT = (absX - 40) / 120;
    baseY += ridgeT * ridgeT * 60;
  }
  const centerDist = absX / (TERRAIN_WIDTH / 2);
  baseY += centerDist * centerDist * 6;
  baseY += pseudoNoise(x, z) * 4;
  return baseY;
}
function createTerrain() {
  const geo = new THREE.PlaneGeometry(
    TERRAIN_WIDTH,
    TERRAIN_DEPTH,
    SEGMENTS_X,
    SEGMENTS_Z
  );
  geo.rotateX(-Math.PI / 2);
  const pos = geo.attributes.position;
  const colors = [];
  for (let i = 0; i < pos.count; i++) {
    const x = pos.getX(i);
    const z = pos.getZ(i);
    const y = heightAt(x, z);
    pos.setY(i, y);
    const centerDist = Math.abs(x) / (TERRAIN_WIDTH / 2);
    const rockFactor = Math.max(0, Math.min(1, (y - 170) / 50));
    let r = 0.91 - centerDist * centerDist * 0.08;
    let g = 0.93 - centerDist * centerDist * 0.06;
    let b = 0.96 - centerDist * centerDist * 0.03;
    r -= rockFactor * 0.18;
    g -= rockFactor * 0.18;
    b -= rockFactor * 0.14;
    colors.push(
      Math.max(0, Math.min(1, r)),
      Math.max(0, Math.min(1, g)),
      Math.max(0, Math.min(1, b))
    );
  }
  geo.setAttribute("color", new THREE.Float32BufferAttribute(colors, 3));
  geo.computeVertexNormals();
  const mat = new THREE.MeshLambertMaterial({
    vertexColors: true,
    flatShading: true
  });
  const mesh = new THREE.Mesh(geo, mat);
  mesh.receiveShadow = true;
  return mesh;
}
function createTrees(terrain) {
  const group = new THREE.Group();
  const positions = [];
  const trunkGeo = new THREE.CylinderGeometry(0.3, 0.4, 3, 5);
  const trunkMat = new THREE.MeshLambertMaterial({ color: 6044190 });
  const leafGeo = new THREE.ConeGeometry(2.5, 5, 6);
  const leafMat = new THREE.MeshLambertMaterial({ color: 2972199 });
  const raycaster = new THREE.Raycaster();
  const down = new THREE.Vector3(0, -1, 0);
  const origin = new THREE.Vector3();
  for (let i = 0; i < 600; i++) {
    let x;
    const z = (Math.random() - 0.5) * TERRAIN_DEPTH * 0.85;
    if (Math.random() < 0.6) {
      const side = Math.random() > 0.5 ? 1 : -1;
      x = side * (30 + Math.random() * 50);
    } else {
      const side = Math.random() > 0.5 ? 1 : -1;
      x = side * (60 + Math.random() * 160);
    }
    origin.set(x, 500, z);
    raycaster.set(origin, down);
    const hits = raycaster.intersectObject(terrain);
    if (hits.length === 0) continue;
    const y = hits[0].point.y;
    if (y > 160) continue;
    const scale = 0.7 + Math.random() * 0.8;
    const trunk = new THREE.Mesh(trunkGeo, trunkMat);
    trunk.position.set(x, y + 1.5 * scale, z);
    trunk.scale.setScalar(scale);
    const leaves = new THREE.Mesh(leafGeo, leafMat);
    leaves.position.set(x, y + 4.5 * scale, z);
    leaves.scale.setScalar(scale);
    group.add(trunk, leaves);
    positions.push(new THREE.Vector3(x, y, z));
  }
  return { group, positions };
}
export {
  BOUNDS,
  COURSE_LENGTH,
  TERRAIN_DEPTH,
  TERRAIN_WIDTH,
  createTerrain,
  createTrees
};
