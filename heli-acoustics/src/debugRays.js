import * as THREE from 'three';

// Debug overlays: direct path (green/red by occlusion) and reflection polylines
// (cyan) so you can see what the image-source solver is feeding the wet taps.
export class DebugRays {
  constructor(scene) {
    this.scene = scene;
    this.direct = makeLine(0x7dffa0);
    this.refLines = [];
    for (let i = 0; i < 8; i++) {
      const line = makeLine(0x6ec8ff);
      this.refLines.push(line);
      scene.add(line);
    }
    scene.add(this.direct);
    this.visible = true;
  }

  setVisible(v) {
    this.visible = v;
    this.direct.visible = v;
    for (const l of this.refLines) l.visible = v;
  }

  update(listener, source, occluded, reflections) {
    setLine(this.direct, listener, source);
    this.direct.material.color.setHex(occluded ? 0xff5a5a : 0x7dffa0);
    this.direct.visible = this.visible;
    for (let i = 0; i < this.refLines.length; i++) {
      const line = this.refLines[i];
      const r = reflections[i];
      if (!r || !this.visible) {
        line.visible = false;
        continue;
      }
      setPolyline(line, [listener, r.hit, source]);
      line.visible = true;
    }
  }
}

function makeLine(color) {
  const geo = new THREE.BufferGeometry();
  geo.setAttribute('position', new THREE.BufferAttribute(new Float32Array(9), 3));
  const mat = new THREE.LineBasicMaterial({ color, depthTest: false });
  const line = new THREE.Line(geo, mat);
  line.renderOrder = 10;
  line.frustumCulled = false;
  return line;
}

function setLine(line, a, b) {
  const arr = line.geometry.attributes.position.array;
  arr[0] = a[0];
  arr[1] = a[1];
  arr[2] = a[2];
  arr[3] = b[0];
  arr[4] = b[1];
  arr[5] = b[2];
  arr[6] = b[0];
  arr[7] = b[1];
  arr[8] = b[2];
  line.geometry.attributes.position.needsUpdate = true;
  line.geometry.setDrawRange(0, 2);
}

function setPolyline(line, points) {
  const arr = line.geometry.attributes.position.array;
  for (let i = 0; i < 3; i++) {
    const p = points[Math.min(i, points.length - 1)];
    arr[i * 3] = p[0];
    arr[i * 3 + 1] = p[1];
    arr[i * 3 + 2] = p[2];
  }
  line.geometry.attributes.position.needsUpdate = true;
  line.geometry.setDrawRange(0, points.length);
}
