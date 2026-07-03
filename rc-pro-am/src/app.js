import {
  CAR,
  CENTERLINE,
  RCProAmGame,
  TRACK,
  WORLD,
  centerlinePoint,
  steerAxisFromDrag,
  trackEdges,
} from "./game.js";

const canvas = document.querySelector("#game-canvas");
const context = canvas.getContext("2d");
const overlay = document.querySelector("#screen-overlay");
const overlayCopy = document.querySelector("#overlay-copy");
const startButton = document.querySelector("#start-button");
const lapValue = document.querySelector("#lap-value");
const placeValue = document.querySelector("#place-value");
const timeValue = document.querySelector("#time-value");
const leftControl = document.querySelector("#left-control");
const rightControl = document.querySelector("#right-control");

const game = new RCProAmGame();
const pressedKeys = new Set();
const skids = [];
let lastFrame = performance.now();

const TRACK_SHAPE = trackEdges();

class TouchSteer {
  constructor(element) {
    this.element = element;
    this.pointerId = null;
    this.startX = 0;
    this.axis = 0;

    element.addEventListener("pointerdown", (event) => this.#start(event));
    element.addEventListener("pointermove", (event) => this.#move(event));
    element.addEventListener("pointerup", (event) => this.#finish(event));
    element.addEventListener("pointercancel", (event) => this.#finish(event));
    element.addEventListener("lostpointercapture", () => this.reset());
  }

  #start(event) {
    if (this.pointerId !== null || game.phase === "ready") {
      return;
    }
    event.preventDefault();
    this.pointerId = event.pointerId;
    this.startX = event.clientX;
    this.element.setPointerCapture(event.pointerId);
    this.element.classList.add("is-active");
  }

  #move(event) {
    if (event.pointerId !== this.pointerId) {
      return;
    }
    event.preventDefault();
    this.axis = steerAxisFromDrag(this.startX, event.clientX);
  }

  #finish(event) {
    if (event.pointerId !== this.pointerId) {
      return;
    }
    this.reset();
  }

  reset() {
    if (this.pointerId !== null && this.element.hasPointerCapture(this.pointerId)) {
      this.element.releasePointerCapture(this.pointerId);
    }
    this.pointerId = null;
    this.axis = 0;
    this.element.classList.remove("is-active");
  }
}

class TouchThrottle {
  constructor(element) {
    this.element = element;
    this.pointerId = null;
    this.active = false;

    element.addEventListener("pointerdown", (event) => this.#start(event));
    element.addEventListener("pointerup", (event) => this.#finish(event));
    element.addEventListener("pointercancel", (event) => this.#finish(event));
    element.addEventListener("lostpointercapture", () => this.reset());
  }

  #start(event) {
    if (this.pointerId !== null || game.phase === "ready") {
      return;
    }
    event.preventDefault();
    this.pointerId = event.pointerId;
    this.active = true;
    this.element.setPointerCapture(event.pointerId);
    this.element.classList.add("is-active");
  }

  #finish(event) {
    if (event.pointerId !== this.pointerId) {
      return;
    }
    this.reset();
  }

  reset() {
    if (this.pointerId !== null && this.element.hasPointerCapture(this.pointerId)) {
      this.element.releasePointerCapture(this.pointerId);
    }
    this.pointerId = null;
    this.active = false;
    this.element.classList.remove("is-active");
  }
}

const steerControl = new TouchSteer(leftControl);
const throttleControl = new TouchThrottle(rightControl);

function resetInputs() {
  steerControl.reset();
  throttleControl.reset();
  pressedKeys.clear();
  game.setPlayerInput(0, 0);
}

function formatTime(seconds) {
  const whole = Math.floor(seconds);
  const millis = Math.floor((seconds - whole) * 100);
  return `${whole}:${String(millis).padStart(2, "0")}`;
}

function beginGame() {
  resetInputs();
  skids.length = 0;
  game.start();
  overlay.hidden = true;
  updateHud();
}

function showEndScreen() {
  resetInputs();
  const place = game.playerCar?.position ?? 5;
  overlayCopy.textContent =
    place === 1
      ? `Winner in ${formatTime(game.playerCar.finishTime ?? game.raceTime)}`
      : `Finished ${place}${place === 2 ? "nd" : place === 3 ? "rd" : "th"} in ${formatTime(game.playerCar?.finishTime ?? game.raceTime)}`;
  startButton.textContent = "Again";
  overlay.hidden = false;
  updateHud();
}

function updateHud() {
  const player = game.playerCar;
  lapValue.textContent = `Lap ${player ? Math.min(player.lap + 1, TRACK.lapCount) : 1}/${TRACK.lapCount}`;
  placeValue.textContent = player ? `P${player.position}` : "P—";
  timeValue.textContent = formatTime(game.raceTime);
}

function controlFromKeys(negativeKey, positiveKey) {
  return Math.max(
    -1,
    Math.min(
      1,
      Number(pressedKeys.has(positiveKey)) - Number(pressedKeys.has(negativeKey)),
    ),
  );
}

function updateControls() {
  if (game.phase !== "racing") {
    game.setPlayerInput(0, 0);
    return;
  }

  const throttle = Math.max(
    -1,
    Math.min(
      1,
      controlFromKeys("ArrowDown", "ArrowUp") +
        controlFromKeys("KeyS", "KeyW") +
        (throttleControl.active ? 1 : 0),
    ),
  );
  const steer = Math.max(
    -1,
    Math.min(
      1,
      controlFromKeys("ArrowLeft", "ArrowRight") +
        controlFromKeys("KeyA", "KeyD") +
        steerControl.axis,
    ),
  );

  game.setPlayerInput(throttle, steer);
}

function processGameEvents() {
  for (const event of game.consumeEvents()) {
    if (event.type === "raceover") {
      showEndScreen();
    }
  }
}

function resizeCanvas() {
  const bounds = canvas.getBoundingClientRect();
  const pixelRatio = Math.min(window.devicePixelRatio || 1, 2);
  const width = Math.max(1, Math.round(bounds.width * pixelRatio));
  const height = Math.max(1, Math.round(bounds.height * pixelRatio));
  if (canvas.width !== width || canvas.height !== height) {
    canvas.width = width;
    canvas.height = height;
  }
}

function recordSkids() {
  if (game.phase !== "racing") {
    return;
  }
  for (const car of game.cars) {
    if (car.skid > 0.35 && Math.hypot(car.vx, car.vy) > 40) {
      skids.push({
        x: car.x - Math.cos(car.angle) * 4,
        y: car.y - Math.sin(car.angle) * 4,
        angle: car.angle,
        alpha: car.skid * 0.35,
        life: 1.4,
      });
    }
  }
  while (skids.length > 140) {
    skids.shift();
  }
}

function drawPlayfield(now, deltaSeconds) {
  const scaleX = canvas.width / WORLD.width;
  const scaleY = canvas.height / WORLD.height;
  context.setTransform(scaleX, 0, 0, scaleY, 0, 0);
  context.clearRect(0, 0, WORLD.width, WORLD.height);

  drawFloor();
  drawTrack();
  drawObstacle();
  drawSkids(deltaSeconds);
  drawFinishLine();
  drawCars(now);

  if (game.phase === "countdown") {
    drawCountdown();
  }
}

function drawFloor() {
  context.fillStyle = "#243021";
  context.fillRect(0, 0, WORLD.width, WORLD.height);
}

function strokeLoop(points, close = true) {
  if (points.length === 0) {
    return;
  }
  context.beginPath();
  context.moveTo(points[0].x, points[0].y);
  for (let index = 1; index < points.length; index += 1) {
    context.lineTo(points[index].x, points[index].y);
  }
  if (close) {
    context.closePath();
  }
}

function appendLoop(points) {
  context.moveTo(points[0].x, points[0].y);
  for (let index = 1; index < points.length; index += 1) {
    context.lineTo(points[index].x, points[index].y);
  }
  context.closePath();
}

function drawTrack() {
  const { inner, outer } = TRACK_SHAPE;

  context.beginPath();
  appendLoop(outer);
  appendLoop(inner);
  context.fillStyle = "#6f5234";
  context.fill("evenodd");

  context.strokeStyle = "#e2c88e";
  context.lineWidth = 4;
  strokeLoop(outer);
  context.stroke();
  context.strokeStyle = "#c7ad78";
  context.lineWidth = 3;
  strokeLoop(inner);
  context.stroke();

  context.setLineDash([8, 10]);
  context.strokeStyle = "rgba(255, 240, 200, 0.35)";
  context.lineWidth = 2;
  context.beginPath();
  context.moveTo(CENTERLINE.points[0].x, CENTERLINE.points[0].y);
  for (const point of CENTERLINE.points) {
    context.lineTo(point.x, point.y);
  }
  context.closePath();
  context.stroke();
  context.setLineDash([]);
}

function drawObstacle() {
  context.fillStyle = "#3d3225";
  context.strokeStyle = "#6d5a43";
  context.lineWidth = 3;
  context.beginPath();
  context.roundRect(318, 210, 164, 130, 18);
  context.fill();
  context.stroke();

  context.fillStyle = "rgba(255, 220, 150, 0.12)";
  context.font = "600 13px ui-monospace, monospace";
  context.textAlign = "center";
  context.fillText("CARPET", 400, 282);
}

function drawFinishLine() {
  const start = centerlinePoint(0);
  const nx = -start.tangentY;
  const ny = start.tangentX;
  context.save();
  context.translate(start.x, start.y);
  context.rotate(Math.atan2(ny, nx));
  for (let stripe = -4; stripe < 4; stripe += 1) {
    context.fillStyle = stripe % 2 === 0 ? "#f4f4f4" : "#111";
    context.fillRect(stripe * 8, -TRACK.halfWidth + 4, 8, TRACK.halfWidth * 2 - 8);
  }
  context.restore();
}

function drawSkids(deltaSeconds) {
  context.save();
  context.lineCap = "round";
  for (let index = skids.length - 1; index >= 0; index -= 1) {
    const mark = skids[index];
    mark.life -= deltaSeconds;
    if (mark.life <= 0) {
      skids.splice(index, 1);
      continue;
    }
    context.strokeStyle = `rgba(20, 14, 8, ${mark.alpha * mark.life})`;
    context.lineWidth = 2;
    context.beginPath();
    context.moveTo(mark.x, mark.y);
    context.lineTo(
      mark.x - Math.cos(mark.angle) * 10,
      mark.y - Math.sin(mark.angle) * 10,
    );
    context.stroke();
  }
  context.restore();
}

function drawCar(car, now) {
  context.save();
  context.translate(car.x + 2, car.y + 3);
  context.rotate(car.angle);
  context.fillStyle = "rgba(0, 0, 0, 0.28)";
  context.beginPath();
  context.roundRect(-CAR.length / 2, -CAR.width / 2, CAR.length, CAR.width, 3);
  context.fill();
  context.restore();

  context.save();
  context.translate(car.x, car.y);
  context.rotate(car.angle);
  context.fillStyle = car.color;
  context.beginPath();
  context.roundRect(-CAR.length / 2, -CAR.width / 2, CAR.length, CAR.width, 3);
  context.fill();

  context.fillStyle = car.accent;
  context.fillRect(CAR.length / 2 - 4, -2, 3, 4);
  context.fillStyle = "#111";
  context.fillRect(-3, -CAR.width / 2 + 1, 6, 2);
  context.fillRect(-3, CAR.width / 2 - 3, 6, 2);

  if (car.boostTime > 0) {
    const flicker = 0.5 + Math.sin(now / 30) * 0.5;
    context.fillStyle = `rgba(255, 170, 40, ${0.4 + flicker * 0.3})`;
    context.beginPath();
    context.moveTo(-CAR.length / 2 - 2, 0);
    context.lineTo(-CAR.length / 2 - 9, -3);
    context.lineTo(-CAR.length / 2 - 9, 3);
    context.closePath();
    context.fill();
  }

  if (car.isPlayer) {
    context.fillStyle = "#fff";
    context.beginPath();
    context.arc(0, 0, 2, 0, Math.PI * 2);
    context.fill();
  }

  context.restore();
}

function drawCars(now) {
  const drawOrder = [...game.cars].sort(
    (left, right) => left.y - right.y || left.x - right.x,
  );
  for (const car of drawOrder) {
    drawCar(car, now);
  }
}

function drawCountdown() {
  const count = Math.ceil(Math.max(0, game.countdown));
  context.fillStyle = "rgba(0, 0, 0, 0.35)";
  context.fillRect(0, 0, WORLD.width, WORLD.height);
  context.fillStyle = count > 0 ? "#fff1bf" : "#8fd26a";
  context.font = "900 88px system-ui, sans-serif";
  context.textAlign = "center";
  context.textBaseline = "middle";
  context.fillText(count > 0 ? String(count) : "GO", WORLD.width / 2, WORLD.height / 2);
}

function animationFrame(now) {
  const deltaSeconds = Math.min(0.1, (now - lastFrame) / 1000);
  lastFrame = now;

  updateControls();
  game.update(deltaSeconds);
  recordSkids();
  processGameEvents();
  updateHud();
  drawPlayfield(now, deltaSeconds);
  requestAnimationFrame(animationFrame);
}

startButton.addEventListener("click", beginGame);

window.addEventListener("keydown", (event) => {
  const controlKeys = new Set([
    "ArrowUp",
    "ArrowDown",
    "ArrowLeft",
    "ArrowRight",
    "KeyW",
    "KeyA",
    "KeyS",
    "KeyD",
    "Space",
    "ShiftLeft",
    "ShiftRight",
    "KeyR",
  ]);
  if (!controlKeys.has(event.code)) {
    return;
  }

  event.preventDefault();
  if (event.code === "Space" && (game.phase === "ready" || overlay.hidden === false)) {
    beginGame();
    return;
  }
  if (event.code === "KeyR") {
    beginGame();
    return;
  }
  if (
    (event.code === "ShiftLeft" || event.code === "ShiftRight") &&
    game.phase === "racing"
  ) {
    game.triggerBoost();
    return;
  }
  pressedKeys.add(event.code);
});

window.addEventListener("keyup", (event) => {
  pressedKeys.delete(event.code);
});

window.addEventListener("blur", resetInputs);
document.addEventListener("visibilitychange", () => {
  resetInputs();
  lastFrame = performance.now();
});

new ResizeObserver(resizeCanvas).observe(canvas);
window.addEventListener("resize", resizeCanvas);

updateHud();
resizeCanvas();
drawPlayfield(performance.now(), 0);
requestAnimationFrame(animationFrame);
