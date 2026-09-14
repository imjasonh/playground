import * as THREE from "three";
import { clamp, getTerrainHeight } from "./utils.js";
const GRAVITY = 18;
const MAX_THRUST = 34;
const IDLE_THRUST_RATIO = 1;
const LINEAR_DRAG = 1;
const THRUST_TILT = 30 * Math.PI / 180;
const MOUSE_SENSITIVITY = 6e-3;
const MOUSE_RESPONSE = 10;
const ROLL_TORQUE = 6;
const ANGULAR_DRAG = 4.5;
const ROLL_RETURN = 3;
const CRASH_ALTITUDE = 1;
const TREE_COLLISION_RADIUS = 2.5;
class Drone {
  camera;
  crashed = false;
  crashReason = "";
  terrain;
  velocity = new THREE.Vector3();
  // Orientation as euler angles
  pitch = 0;
  yaw = 0;
  roll = 0;
  // Angular velocity (rad/s)
  angVelPitch = 0;
  angVelYaw = 0;
  angVelRoll = 0;
  // Mouse accumulator (pixels per frame)
  mouseAccumX = 0;
  mouseAccumY = 0;
  // Pending angular velocity from mouse input, drains over time
  pendingYaw = 0;
  pendingPitch = 0;
  // Input state
  keys = {};
  pointerLocked = false;
  // Smoothness tracking for scoring
  prevPitch = 0;
  prevYaw = 0;
  angularJerk = 0;
  constructor(camera, terrain) {
    this.camera = camera;
    this.terrain = terrain;
    this.setupInput();
  }
  setupInput() {
    document.addEventListener("keydown", (e) => {
      this.keys[e.code] = true;
    });
    document.addEventListener("keyup", (e) => {
      this.keys[e.code] = false;
    });
    document.addEventListener("mousemove", (e) => {
      if (!this.pointerLocked) return;
      this.mouseAccumX += e.movementX;
      this.mouseAccumY += e.movementY;
    });
    document.addEventListener("pointerlockchange", () => {
      this.pointerLocked = document.pointerLockElement !== null;
    });
  }
  lockPointer() {
    document.body.requestPointerLock();
  }
  setPosition(pos) {
    this.camera.position.copy(pos);
    this.velocity.set(0, 0, 0);
  }
  setLookDirection(yaw, pitch) {
    this.yaw = yaw;
    this.pitch = pitch;
    this.roll = 0;
    this.angVelPitch = 0;
    this.angVelYaw = 0;
    this.angVelRoll = 0;
  }
  reset() {
    this.crashed = false;
    this.crashReason = "";
    this.velocity.set(0, 0, 0);
    this.roll = 0;
    this.angVelPitch = 0;
    this.angVelYaw = 0;
    this.angVelRoll = 0;
    this.mouseAccumX = 0;
    this.mouseAccumY = 0;
    this.pendingYaw = 0;
    this.pendingPitch = 0;
  }
  triggerCrash(reason) {
    if (this.crashed) return;
    this.crashed = true;
    this.crashReason = reason;
  }
  update(dt, treePositions) {
    if (this.crashed) return;
    this.pendingYaw += this.mouseAccumX * MOUSE_SENSITIVITY;
    this.pendingPitch += this.mouseAccumY * MOUSE_SENSITIVITY;
    this.mouseAccumX = 0;
    this.mouseAccumY = 0;
    const blend = 1 - Math.exp(-MOUSE_RESPONSE * dt);
    this.angVelYaw -= this.pendingYaw * blend;
    this.angVelPitch -= this.pendingPitch * blend;
    this.pendingYaw *= 1 - blend;
    this.pendingPitch *= 1 - blend;
    if (this.keys["KeyA"]) this.angVelRoll += ROLL_TORQUE * dt;
    if (this.keys["KeyD"]) this.angVelRoll -= ROLL_TORQUE * dt;
    this.angVelRoll -= this.roll * ROLL_RETURN * dt;
    const angDrag = Math.max(0, 1 - ANGULAR_DRAG * dt);
    this.angVelPitch *= angDrag;
    this.angVelYaw *= angDrag;
    this.angVelRoll *= angDrag;
    this.pitch += this.angVelPitch * dt;
    this.yaw += this.angVelYaw * dt;
    this.roll += this.angVelRoll * dt;
    this.pitch = clamp(this.pitch, -Math.PI / 2 + 0.1, Math.PI / 2 - 0.1);
    const euler = new THREE.Euler(this.pitch, this.yaw, this.roll, "YXZ");
    this.camera.quaternion.setFromEuler(euler);
    if (this.keys["KeyW"]) {
      const thrustDir = new THREE.Vector3(
        0,
        Math.cos(THRUST_TILT),
        -Math.sin(THRUST_TILT)
      ).applyQuaternion(this.camera.quaternion);
      this.velocity.x += thrustDir.x * MAX_THRUST * dt;
      this.velocity.y += thrustDir.y * MAX_THRUST * dt;
      this.velocity.z += thrustDir.z * MAX_THRUST * dt;
    } else if (!this.keys["KeyS"]) {
      this.velocity.y += GRAVITY * IDLE_THRUST_RATIO * dt;
    }
    this.velocity.y -= GRAVITY * dt;
    const dragFactor = Math.max(0, 1 - LINEAR_DRAG * dt);
    this.velocity.multiplyScalar(dragFactor);
    this.camera.position.x += this.velocity.x * dt;
    this.camera.position.y += this.velocity.y * dt;
    this.camera.position.z += this.velocity.z * dt;
    const terrainH = getTerrainHeight(
      this.terrain,
      this.camera.position.x,
      this.camera.position.z
    );
    if (this.camera.position.y < terrainH + CRASH_ALTITUDE) {
      this.crashed = true;
      this.crashReason = "TERRAIN";
      this.camera.position.y = terrainH + CRASH_ALTITUDE;
      return;
    }
    const pos = this.camera.position;
    for (const treePos of treePositions) {
      const dx = pos.x - treePos.x;
      const dz = pos.z - treePos.z;
      const horizDist = Math.sqrt(dx * dx + dz * dz);
      const dy = pos.y - treePos.y;
      if (horizDist < TREE_COLLISION_RADIUS && dy > -1 && dy < 8) {
        this.crashed = true;
        this.crashReason = "TREE";
        return;
      }
    }
    const angularDelta = Math.sqrt(
      (this.pitch - this.prevPitch) ** 2 + (this.yaw - this.prevYaw) ** 2
    );
    this.angularJerk = angularDelta;
    this.prevPitch = this.pitch;
    this.prevYaw = this.yaw;
  }
  getPosition() {
    return this.camera.position.clone();
  }
  getAudioState() {
    const throttle = this.keys["KeyW"] ? "full" : this.keys["KeyS"] ? "cut" : "idle";
    const speed = this.velocity.length();
    return { throttle, speed, rollAngVel: this.angVelRoll };
  }
  getAltitudeAboveTerrain() {
    const terrainH = getTerrainHeight(
      this.terrain,
      this.camera.position.x,
      this.camera.position.z
    );
    return this.camera.position.y - terrainH;
  }
}
export {
  Drone
};
