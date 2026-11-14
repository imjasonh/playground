import * as THREE from "three";
import { BOUNDS } from "./terrain.js";
const MINIMAP_W = 160;
const MINIMAP_H = 200;
const VIEW_WIDTH = BOUNDS.maxX - BOUNDS.minX;
const VIEW_DEPTH = BOUNDS.maxZ - BOUNDS.minZ;
class Minimap {
  canvas;
  ctx;
  coursePoints;
  constructor(coursePoints) {
    this.canvas = document.getElementById("minimap-canvas");
    this.canvas.width = MINIMAP_W;
    this.canvas.height = MINIMAP_H;
    this.ctx = this.canvas.getContext("2d");
    this.coursePoints = coursePoints;
  }
  worldToMinimap(x, z) {
    const px = (x - BOUNDS.minX) / VIEW_WIDTH * MINIMAP_W;
    const py = (z - BOUNDS.minZ) / VIEW_DEPTH * MINIMAP_H;
    return [px, py];
  }
  update(skierPos, dronePos, gatePositions) {
    const ctx = this.ctx;
    ctx.clearRect(0, 0, MINIMAP_W, MINIMAP_H);
    ctx.fillStyle = "rgba(20, 30, 40, 0.6)";
    ctx.fillRect(0, 0, MINIMAP_W, MINIMAP_H);
    ctx.strokeStyle = "rgba(255, 100, 100, 0.3)";
    ctx.lineWidth = 1;
    ctx.strokeRect(1, 1, MINIMAP_W - 2, MINIMAP_H - 2);
    ctx.strokeStyle = "rgba(255, 150, 0, 0.5)";
    ctx.lineWidth = 1.5;
    ctx.beginPath();
    for (let i = 0; i < this.coursePoints.length; i++) {
      const [px, py] = this.worldToMinimap(this.coursePoints[i].x, this.coursePoints[i].z);
      if (i === 0) ctx.moveTo(px, py);
      else ctx.lineTo(px, py);
    }
    ctx.stroke();
    for (const gp of gatePositions) {
      const [gx, gy] = this.worldToMinimap(gp.x, gp.z);
      ctx.fillStyle = "rgba(255, 255, 255, 0.4)";
      ctx.fillRect(gx - 1.5, gy - 1.5, 3, 3);
    }
    if (this.coursePoints.length > 0) {
      const sp = this.coursePoints[0];
      const [sx, sy] = this.worldToMinimap(sp.x, sp.z);
      ctx.strokeStyle = "rgba(255, 255, 255, 0.6)";
      ctx.lineWidth = 1;
      ctx.beginPath();
      ctx.moveTo(sx - 8, sy);
      ctx.lineTo(sx + 8, sy);
      ctx.stroke();
    }
    if (this.coursePoints.length > 1) {
      const fp = this.coursePoints[this.coursePoints.length - 1];
      const [fx, fy] = this.worldToMinimap(fp.x, fp.z);
      ctx.strokeStyle = "rgba(255, 50, 50, 0.8)";
      ctx.lineWidth = 2;
      ctx.beginPath();
      ctx.moveTo(fx - 8, fy);
      ctx.lineTo(fx + 8, fy);
      ctx.stroke();
    }
    const [skx, sky] = this.worldToMinimap(skierPos.x, skierPos.z);
    ctx.fillStyle = "#ff3333";
    ctx.beginPath();
    ctx.arc(skx, sky, 4, 0, Math.PI * 2);
    ctx.fill();
    const [dx, dy] = this.worldToMinimap(dronePos.x, dronePos.z);
    ctx.fillStyle = "#3388ff";
    ctx.beginPath();
    ctx.arc(dx, dy, 4, 0, Math.PI * 2);
    ctx.fill();
  }
}
export {
  Minimap
};
