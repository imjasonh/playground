import * as THREE from 'three';
import { BUILDINGS } from './city.js';

export function createCityScene() {
  const scene = new THREE.Scene();
  scene.background = new THREE.Color(0x87a0b8);
  scene.fog = new THREE.Fog(0x87a0b8, 100, 420);

  const hemi = new THREE.HemisphereLight(0xddeeff, 0x445566, 0.85);
  scene.add(hemi);
  const sun = new THREE.DirectionalLight(0xfff2dd, 0.9);
  sun.position.set(60, 180, 40);
  scene.add(sun);

  // Ground / street.
  const ground = new THREE.Mesh(
    new THREE.PlaneGeometry(400, 400),
    new THREE.MeshStandardMaterial({ color: 0x3a3f46, roughness: 0.9, metalness: 0.05 }),
  );
  ground.rotation.x = -Math.PI / 2;
  ground.receiveShadow = true;
  scene.add(ground);

  // Avenue paint.
  const stripeMat = new THREE.MeshBasicMaterial({ color: 0xd8c96a });
  for (let z = -120; z <= 120; z += 8) {
    const stripe = new THREE.Mesh(new THREE.PlaneGeometry(0.4, 4), stripeMat);
    stripe.rotation.x = -Math.PI / 2;
    stripe.position.set(0, 0.02, z);
    scene.add(stripe);
  }

  const buildings = [];
  const facadeColors = [0x8a9098, 0x6e7884, 0x9aa3ab, 0x7a8490, 0x5c6570];
  BUILDINGS.forEach((b, i) => {
    const sx = b.max[0] - b.min[0];
    const sy = b.max[1] - b.min[1];
    const sz = b.max[2] - b.min[2];
    const mesh = new THREE.Mesh(
      new THREE.BoxGeometry(sx, sy, sz),
      new THREE.MeshStandardMaterial({
        color: facadeColors[i % facadeColors.length],
        roughness: 0.85,
        metalness: 0.05,
      }),
    );
    mesh.position.set((b.min[0] + b.max[0]) / 2, sy / 2, (b.min[2] + b.max[2]) / 2);
    mesh.userData.buildingId = b.id;
    scene.add(mesh);
    buildings.push(mesh);

    // Roof accent so silhouettes read clearly against the sky.
    const roof = new THREE.Mesh(
      new THREE.BoxGeometry(sx * 0.92, 0.6, sz * 0.92),
      new THREE.MeshStandardMaterial({ color: 0x2c333b, roughness: 1 }),
    );
    roof.position.set(mesh.position.x, sy + 0.3, mesh.position.z);
    scene.add(roof);
  });

  // Helicopter marker (simple cross).
  const heli = new THREE.Group();
  const body = new THREE.Mesh(
    new THREE.SphereGeometry(1.2, 12, 10),
    new THREE.MeshStandardMaterial({ color: 0xc23b22, roughness: 0.5, metalness: 0.2 }),
  );
  const rotor = new THREE.Mesh(
    new THREE.BoxGeometry(6, 0.15, 0.4),
    new THREE.MeshStandardMaterial({ color: 0x222222 }),
  );
  rotor.position.y = 1.3;
  heli.add(body);
  heli.add(rotor);
  scene.add(heli);

  return { scene, heli, buildings, rotor };
}

export function createRenderer(canvas) {
  const renderer = new THREE.WebGLRenderer({ canvas, antialias: true });
  renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
  renderer.setSize(canvas.clientWidth, canvas.clientHeight, false);
  return renderer;
}

export function createCamera(aspect) {
  const camera = new THREE.PerspectiveCamera(70, aspect, 0.1, 800);
  camera.position.set(0, 1.7, 0);
  return camera;
}
