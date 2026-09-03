import * as THREE from 'three';
import { BUILDINGS, cityBounds } from './city.js';

export function createCityScene() {
  const bounds = cityBounds(BUILDINGS);
  const groundSize = Math.max(bounds.spanX, bounds.spanZ) + 200;
  const fogFar = Math.max(bounds.spanX, bounds.spanZ) * 1.4;

  const scene = new THREE.Scene();
  scene.background = new THREE.Color(0x87a0b8);
  scene.fog = new THREE.Fog(0x87a0b8, fogFar * 0.35, fogFar);

  const hemi = new THREE.HemisphereLight(0xddeeff, 0x445566, 0.85);
  scene.add(hemi);
  const sun = new THREE.DirectionalLight(0xfff2dd, 0.95);
  sun.position.set(120, 320, 80);
  scene.add(sun);

  const ground = new THREE.Mesh(
    new THREE.PlaneGeometry(groundSize, groundSize),
    new THREE.MeshStandardMaterial({
      color: 0x3a3f46,
      roughness: 0.9,
      metalness: 0.05,
      depthWrite: true,
      depthTest: true,
    }),
  );
  ground.rotation.x = -Math.PI / 2;
  ground.receiveShadow = true;
  scene.add(ground);

  // Avenue centerline paint along the N–S corridor.
  const stripeMat = new THREE.MeshBasicMaterial({
    color: 0xd8c96a,
    depthTest: true,
    depthWrite: true,
  });
  for (let z = bounds.z0 - 40; z <= bounds.z1 + 40; z += 10) {
    const stripe = new THREE.Mesh(new THREE.PlaneGeometry(0.5, 5), stripeMat);
    stripe.rotation.x = -Math.PI / 2;
    stripe.position.set(0, 0.03, z);
    scene.add(stripe);
  }

  const buildings = [];
  const facadeColors = [0x8a9098, 0x6e7884, 0x9aa3ab, 0x7a8490, 0x5c6570, 0x74808c];
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
        depthWrite: true,
        depthTest: true,
      }),
    );
    mesh.position.set((b.min[0] + b.max[0]) / 2, sy / 2, (b.min[2] + b.max[2]) / 2);
    mesh.userData.buildingId = b.id;
    // Buildings must win depth against overlays; keep default renderOrder 0.
    mesh.renderOrder = 0;
    scene.add(mesh);
    buildings.push(mesh);

    const roof = new THREE.Mesh(
      new THREE.BoxGeometry(sx * 0.92, 0.8, sz * 0.92),
      new THREE.MeshStandardMaterial({
        color: 0x2c333b,
        roughness: 1,
        depthWrite: true,
        depthTest: true,
      }),
    );
    roof.position.set(mesh.position.x, sy + 0.4, mesh.position.z);
    scene.add(roof);
  });

  // Helicopter: opaque materials with depth testing so facades can hide it.
  const heli = new THREE.Group();
  heli.renderOrder = 0;
  const bodyMat = new THREE.MeshStandardMaterial({
    color: 0xc23b22,
    roughness: 0.5,
    metalness: 0.2,
    depthTest: true,
    depthWrite: true,
  });
  const rotorMat = new THREE.MeshStandardMaterial({
    color: 0x222222,
    roughness: 0.8,
    depthTest: true,
    depthWrite: true,
  });
  const body = new THREE.Mesh(new THREE.SphereGeometry(2.2, 14, 12), bodyMat);
  const boom = new THREE.Mesh(new THREE.BoxGeometry(1.2, 0.7, 5.5), bodyMat);
  boom.position.set(0, 0.2, 3.2);
  const rotor = new THREE.Mesh(new THREE.BoxGeometry(10, 0.2, 0.55), rotorMat);
  rotor.position.y = 2.4;
  heli.add(body);
  heli.add(boom);
  heli.add(rotor);
  scene.add(heli);

  return { scene, heli, buildings, rotor, bounds };
}

export function createRenderer(canvas) {
  // Logarithmic depth fixes distant occlusion failures in large outdoor scenes
  // (heli otherwise appears to draw in front of far facades).
  const renderer = new THREE.WebGLRenderer({
    canvas,
    antialias: true,
    logarithmicDepthBuffer: true,
  });
  renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
  renderer.setSize(canvas.clientWidth, canvas.clientHeight, false);
  renderer.sortObjects = true;
  return renderer;
}

export function createCamera(aspect, bounds = cityBounds()) {
  const far = Math.max(bounds.spanX, bounds.spanZ) * 2.5;
  const camera = new THREE.PerspectiveCamera(70, aspect, 0.2, far);
  camera.position.set(0, 1.7, 0);
  return camera;
}
