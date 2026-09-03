import * as THREE from 'three';

// Debug overlays: direct path (green/red by occlusion) and reflection polylines.
// Order-1 draws listener → hit → source. Order-2 draws listener → hitB → hitA → source.
export class DebugRays {
  constructor(scene, { maxTaps = 12 } = {}) {
    this.scene = scene;
    this.direct = makeLine(0x7dffa0, 4);
    this.refLines = [];
    for (let i = 0; i < maxTaps; i++) {
      const line = makeLine(0x6ec8ff, 4);
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
      const hits = r.hits && r.hits.length ? r.hits : [r.hit];
      // Path in travel order from the listener: last bounce first, then earlier.
      const points = [listener, ...hits.slice().reverse(), source];
      setPolyline(line, points);
      line.material.color.setHex(r.order > 1 ? 0xc9a0ff : 0x6ec8ff);
      line.visible = true;
    }
  }
}

function makeLine(color, maxPoints) {
  const geo = new THREE.BufferGeometry();
  geo.setAttribute('position', new THREE.BufferAttribute(new Float32Array(maxPoints * 3), 3));
  const mat = new THREE.LineBasicMaterial({ color, depthTest: false });
  const line = new THREE.Line(geo, mat);
  line.renderOrder = 10;
  line.frustumCulled = false;
  return line;
}

function setLine(line, a, b) {
  setPolyline(line, [a, b]);
}

function setPolyline(line, points) {
  const arr = line.geometry.attributes.position.array;
  const cap = arr.length / 3;
  const n = Math.min(points.length, cap);
  for (let i = 0; i < n; i++) {
    const p = points[i];
    arr[i * 3] = p[0];
    arr[i * 3 + 1] = p[1];
    arr[i * 3 + 2] = p[2];
  }
  // Pad remaining slots with the last point so unused verts don't flash.
  const last = points[n - 1] || [0, 0, 0];
  for (let i = n; i < cap; i++) {
    arr[i * 3] = last[0];
    arr[i * 3 + 1] = last[1];
    arr[i * 3 + 2] = last[2];
  }
  line.geometry.attributes.position.needsUpdate = true;
  line.geometry.setDrawRange(0, n);
}
