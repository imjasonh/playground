import * as THREE from "three";
function clamp(v, min, max) {
  return Math.max(min, Math.min(max, v));
}
function lerp(a, b, t) {
  return a + (b - a) * t;
}
function lerpV3(out, target, t) {
  out.x = lerp(out.x, target.x, t);
  out.y = lerp(out.y, target.y, t);
  out.z = lerp(out.z, target.z, t);
}
const _raycaster = new THREE.Raycaster();
const _down = new THREE.Vector3(0, -1, 0);
const _origin = new THREE.Vector3();
function getTerrainHeight(terrain, x, z) {
  _origin.set(x, 500, z);
  _raycaster.set(_origin, _down);
  const hits = _raycaster.intersectObject(terrain);
  if (hits.length > 0) {
    return hits[0].point.y;
  }
  return 0;
}
export {
  clamp,
  getTerrainHeight,
  lerp,
  lerpV3
};
