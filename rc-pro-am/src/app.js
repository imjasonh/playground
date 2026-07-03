import {
  CAR,
  RCProAmGame,
  TRACK,
  WORLD,
  centerlinePoint,
  steerAxisFromDrag,
} from "./game.js";

const canvas = document.querySelector("#game-canvas");
const context = canvas.getContext("2d");
const overlay = document.querySelector("#screen-overlay");
const overlayKicker = document.querySelector("#overlay-kicker");
const overlayTitle = document.querySelector("#overlay-title");
const overlayCopy = document.querySelector("#overlay-copy");
const startButton = document.querySelector("#start-button");
const resetButton = document.querySelector("#reset-button");
const soundButton = document.querySelector("#sound-button");
const message = document.querySelector("#message");
const lapValue = document.querySelector("#lap-value");
const placeValue = document.querySelector("#place-value");
const timeValue = document.querySelector("#time-value");
const bestValue = document.querySelector("#best-value");
const leftControl = document.querySelector("#left-control");
const rightControl = document.querySelector("#right-control");

const game = new RCProAmGame();
const pressedKeys = new Set();
const HIGH_SCORE_KEY = "rc-pro-am-best-place";
const skids = [];
let bestPlace = readBestPlace();
let soundEnabled = true;
let audioContext = null;
let lastFrame = performance.now();

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
    element.addEventListener("lostpointercapture", (event) => this.#finish(event));
  }

  #start(event) {
    if (this.pointerId !== null || game.phase === "ready") {
      return;
    }
    event.preventDefault();
    ensureAudio();
    this.pointerId = event.pointerId;
    this.startX = event.clientX;
    this.element.setPointerCapture(event.pointerId);
    this.element.classList.add("is-active");
    this.#setAxis(0);
  }

  #move(event) {
    if (event.pointerId !== this.pointerId) {
      return;
    }
    event.preventDefault();
    this.#setAxis(steerAxisFromDrag(this.startX, event.clientX));
  }

  #finish(event) {
    if (event.pointerId !== this.pointerId) {
      return;
    }
    this.pointerId = null;
    this.element.classList.remove("is-active");
    this.#setAxis(0);
  }

  #setAxis(axis) {
    this.axis = axis;
    this.element.style.setProperty("--axis", axis.toFixed(3));
    this.element.style.setProperty("--knob-x", `${Math.round(axis * 22)}px`);
    this.element.setAttribute("aria-pressed", String(Math.abs(axis) > 0.08));
  }

  reset() {
    if (
      this.pointerId !== null &&
      this.element.hasPointerCapture(this.pointerId)
    ) {
      this.element.releasePointerCapture(this.pointerId);
    }
    this.pointerId = null;
    this.element.classList.remove("is-active");
    this.#setAxis(0);
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
    element.addEventListener("lostpointercapture", (event) => this.#finish(event));
  }

  #start(event) {
    if (this.pointerId !== null || game.phase === "ready") {
      return;
    }
    event.preventDefault();
    ensureAudio();
    this.pointerId = event.pointerId;
    this.active = true;
    this.element.setPointerCapture(event.pointerId);
    this.element.classList.add("is-active");
    this.element.setAttribute("aria-pressed", "true");
  }

  #finish(event) {
    if (event.pointerId !== this.pointerId) {
      return;
    }
    this.pointerId = null;
    this.active = false;
    this.element.classList.remove("is-active");
    this.element.setAttribute("aria-pressed", "false");
  }

  reset() {
    if (
      this.pointerId !== null &&
      this.element.hasPointerCapture(this.pointerId)
    ) {
      this.element.releasePointerCapture(this.pointerId);
    }
    this.pointerId = null;
    this.active = false;
    this.element.classList.remove("is-active");
    this.element.setAttribute("aria-pressed", "false");
  }
}

const steerControl = new TouchSteer(leftControl);
const throttleControl = new TouchThrottle(rightControl);

function readBestPlace() {
  try {
    const value = Number.parseInt(localStorage.getItem(HIGH_SCORE_KEY), 10);
    return Number.isFinite(value) ? value : 99;
  } catch {
    return 99;
  }
}

function saveBestPlace(place) {
  if (place >= bestPlace) {
    return;
  }
  bestPlace = place;
  try {
    localStorage.setItem(HIGH_SCORE_KEY, String(place));
  } catch {
    // Ignore storage failures.
  }
}

function resetInputs() {
  steerControl.reset();
  throttleControl.reset();
  pressedKeys.clear();
  game.setPlayerInput(0, 0);
}

function formatTime(seconds) {
  const whole = Math.floor(seconds);
  const millis = Math.floor((seconds - whole) * 100);
  return `${String(whole).padStart(2, "0")}:${String(millis).padStart(2, "0")}`;
}

function ordinal(place) {
  const suffixes = ["th", "st", "nd", "rd"];
  const mod = place % 100;
  const suffix = suffixes[(mod - 20) % 10] || suffixes[mod] || suffixes[0];
  return `${place}${suffix}`;
}

function beginGame() {
  ensureAudio();
  resetInputs();
  skids.length = 0;
  game.start();
  overlay.hidden = true;
  resetButton.disabled = false;
  setMessage("Wait for the green light. Draft the inside line and hit boost on the straight.");
  playStartSound();
  updateHud();
}

function showEndScreen() {
  resetInputs();
  const place = game.playerCar?.position ?? 5;
  saveBestPlace(place);
  overlayKicker.textContent = place === 1 ? "Pole to win" : "Race complete";
  overlayTitle.textContent =
    place === 1 ? "You took the loop!" : `${ordinal(place)} place finish`;
  overlayCopy.textContent =
    place === 1
      ? `Three clean laps in ${formatTime(game.playerCar.finishTime ?? game.raceTime)}. The carpet is yours.`
      : `You crossed in ${formatTime(game.playerCar?.finishTime ?? game.raceTime)}. Line up another grid start.`;
  startButton.textContent = "Race again";
  overlay.hidden = false;
  updateHud();
}

function setMessage(text) {
  message.textContent = text;
}

function updateHud() {
  const player = game.playerCar;
  lapValue.textContent = player
    ? `${Math.min(player.lap + 1, TRACK.lapCount)}/${TRACK.lapCount}`
    : `1/${TRACK.lapCount}`;
  placeValue.textContent = player ? ordinal(player.position) : "—";
  timeValue.textContent = formatTime(game.raceTime);
  bestValue.textContent = bestPlace <= 5 ? ordinal(bestPlace) : "—";
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

  const keyboardSteer = controlFromKeys("ArrowLeft", "ArrowRight");
  const keyboardThrottle = controlFromKeys("ArrowDown", "ArrowUp");
  const touchSteer = steerControl.axis;
  const touchThrottle = throttleControl.active ? 1 : 0;

  const throttle = Math.max(
    -1,
    Math.min(1, keyboardThrottle + touchThrottle + controlFromKeys("KeyS", "KeyW")),
  );
  const steer = Math.max(
    -1,
    Math.min(1, keyboardSteer + touchSteer + controlFromKeys("KeyA", "KeyD")),
  );

  game.setPlayerInput(throttle, steer);
}

function processGameEvents() {
  for (const event of game.consumeEvents()) {
    if (event.type === "go") {
      setMessage("Go! Feather the throttle — these cars are light and snappy.");
      playGoSound();
      vibrate([20, 30, 20]);
    } else if (event.type === "lap" && event.car === "player") {
      setMessage(`Lap ${event.lap} complete. Keep the wheels on the carpet.`);
      playLapSound();
    } else if (event.type === "boost") {
      setMessage("Turbo spooled! Hold your line through the loop.");
      playBoostSound();
    } else if (event.type === "finish" && event.car === "player") {
      setMessage(`Checkered flag in ${formatTime(event.time)}.`);
      playFinishSound();
    } else if (event.type === "raceover") {
      showEndScreen();
    }
  }
}

function ensureAudio() {
  if (!soundEnabled) {
    return null;
  }
  if (!audioContext) {
    const AudioContext = window.AudioContext || window.webkitAudioContext;
    if (!AudioContext) {
      return null;
    }
    audioContext = new AudioContext();
  }
  if (audioContext.state === "suspended") {
    audioContext.resume();
  }
  return audioContext;
}

function playTone(frequency, duration, delay = 0, type = "square", volume = 0.04) {
  const audio = ensureAudio();
  if (!audio) {
    return;
  }
  const oscillator = audio.createOscillator();
  const gain = audio.createGain();
  const start = audio.currentTime + delay;
  oscillator.type = type;
  oscillator.frequency.setValueAtTime(frequency, start);
  gain.gain.setValueAtTime(0.0001, start);
  gain.gain.exponentialRampToValueAtTime(volume, start + 0.01);
  gain.gain.exponentialRampToValueAtTime(0.0001, start + duration);
  oscillator.connect(gain).connect(audio.destination);
  oscillator.start(start);
  oscillator.stop(start + duration + 0.02);
}

function playStartSound() {
  playTone(196, 0.12, 0, "square", 0.03);
  playTone(247, 0.14, 0.08, "square", 0.03);
}

function playGoSound() {
  playTone(523, 0.18, 0, "triangle", 0.05);
  playTone(784, 0.22, 0.08, "triangle", 0.045);
}

function playLapSound() {
  playTone(440, 0.12, 0, "triangle", 0.04);
  playTone(554, 0.16, 0.08, "triangle", 0.04);
}

function playBoostSound() {
  playTone(120, 0.28, 0, "sawtooth", 0.035);
  playTone(180, 0.24, 0.05, "sawtooth", 0.03);
}

function playFinishSound() {
  [523, 659, 784].forEach((frequency, index) => {
    playTone(frequency, 0.24, index * 0.09, "triangle", 0.045);
  });
}

function vibrate(pattern) {
  if ("vibrate" in navigator) {
    navigator.vibrate(pattern);
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

function recordSkids(now) {
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
        born: now,
      });
    }
  }
  while (skids.length > 180) {
    skids.shift();
  }
}

function drawPlayfield(now) {
  const scaleX = canvas.width / WORLD.width;
  const scaleY = canvas.height / WORLD.height;
  context.setTransform(scaleX, 0, 0, scaleY, 0, 0);
  context.clearRect(0, 0, WORLD.width, WORLD.height);

  drawRoom();
  drawTrack(now);
  drawSkids(now);
  drawFinishLine();
  drawCars(now);
  drawHudOverlay(now);
}

function drawRoom() {
  const floor = context.createLinearGradient(0, 0, WORLD.width, WORLD.height);
  floor.addColorStop(0, "#2d2418");
  floor.addColorStop(0.5, "#241c13");
  floor.addColorStop(1, "#171109");
  context.fillStyle = floor;
  context.fillRect(0, 0, WORLD.width, WORLD.height);

  context.save();
  context.strokeStyle = "rgba(255, 230, 170, 0.025)";
  context.lineWidth = 1;
  for (let y = 8; y < WORLD.height; y += 10) {
    context.beginPath();
    context.moveTo(0, y);
    context.lineTo(WORLD.width, y);
    context.stroke();
  }
  for (let x = 8; x < WORLD.width; x += 10) {
    context.beginPath();
    context.moveTo(x, 0);
    context.lineTo(x, WORLD.height);
    context.stroke();
  }
  context.restore();

  const vignette = context.createRadialGradient(
    WORLD.cx,
    WORLD.cy,
    80,
    WORLD.cx,
    WORLD.cy,
    430,
  );
  vignette.addColorStop(0, "rgba(255, 214, 120, 0.08)");
  vignette.addColorStop(1, "rgba(0, 0, 0, 0.45)");
  context.fillStyle = vignette;
  context.fillRect(0, 0, WORLD.width, WORLD.height);
}

function drawTrack(now) {
  context.save();
  context.translate(WORLD.cx, WORLD.cy);

  context.fillStyle = "#120d08";
  context.beginPath();
  context.ellipse(0, 0, TRACK.outerA + 28, TRACK.outerB + 28, 0, 0, Math.PI * 2);
  context.fill();

  const carpet = context.createLinearGradient(-TRACK.outerA, -TRACK.outerB, TRACK.outerA, TRACK.outerB);
  carpet.addColorStop(0, "#6b4b2d");
  carpet.addColorStop(0.45, "#7a5735");
  carpet.addColorStop(1, "#5a4028");
  context.fillStyle = carpet;
  context.beginPath();
  context.ellipse(0, 0, TRACK.outerA, TRACK.outerB, 0, 0, Math.PI * 2);
  context.fill();

  context.fillStyle = "#17130d";
  context.beginPath();
  context.ellipse(0, 0, TRACK.innerA, TRACK.innerB, 0, 0, Math.PI * 2);
  context.fill();

  context.strokeStyle = "rgba(255, 224, 150, 0.18)";
  context.lineWidth = 2;
  context.setLineDash([10, 12]);
  context.beginPath();
  context.ellipse(0, 0, TRACK.centerA, TRACK.centerB, 0, 0, Math.PI * 2);
  context.stroke();
  context.setLineDash([]);

  context.lineWidth = 5;
  context.strokeStyle = "#f0d090";
  context.beginPath();
  context.ellipse(0, 0, TRACK.outerA, TRACK.outerB, 0, 0, Math.PI * 2);
  context.stroke();

  context.lineWidth = 4;
  context.strokeStyle = "#d8ba78";
  context.beginPath();
  context.ellipse(0, 0, TRACK.innerA, TRACK.innerB, 0, 0, Math.PI * 2);
  context.stroke();

  const pulse = 0.5 + Math.sin(now / 180) * 0.5;
  context.fillStyle = `rgba(255, 244, 190, ${0.05 + pulse * 0.04})`;
  for (let index = 0; index < 24; index += 1) {
    const point = centerlinePoint(index / 24);
    context.beginPath();
    context.arc(point.x - WORLD.cx, point.y - WORLD.cy, 3, 0, Math.PI * 2);
    context.fill();
  }

  context.restore();
}

function drawFinishLine() {
  const start = centerlinePoint(0);
  const nx = -start.tangentY;
  const ny = start.tangentX;
  context.save();
  context.translate(start.x, start.y);
  context.rotate(Math.atan2(ny, nx));
  for (let stripe = -4; stripe < 4; stripe += 1) {
    context.fillStyle = stripe % 2 === 0 ? "#f5f5f5" : "#101010";
    context.fillRect(stripe * 8, -18, 8, 36);
  }
  context.restore();
}

function drawSkids(now) {
  context.save();
  context.lineCap = "round";
  for (const mark of skids) {
    const age = (now - mark.born) / 1000;
    const alpha = Math.max(0, mark.alpha - age * 0.08);
    if (alpha <= 0) {
      continue;
    }
    context.strokeStyle = `rgba(30, 20, 10, ${alpha})`;
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

function drawCarShadow(car) {
  context.save();
  context.translate(car.x + 2, car.y + 3);
  context.rotate(car.angle);
  context.fillStyle = "rgba(0, 0, 0, 0.35)";
  context.beginPath();
  context.roundRect(-CAR.length / 2, -CAR.width / 2, CAR.length, CAR.width, 3);
  context.fill();
  context.restore();
}

function drawCar(car, now) {
  drawCarShadow(car);
  context.save();
  context.translate(car.x, car.y);
  context.rotate(car.angle);

  const body = context.createLinearGradient(-CAR.length / 2, 0, CAR.length / 2, 0);
  body.addColorStop(0, shadeColor(car.color, -18));
  body.addColorStop(0.35, car.color);
  body.addColorStop(1, shadeColor(car.color, -28));
  context.fillStyle = body;
  context.beginPath();
  context.roundRect(-CAR.length / 2, -CAR.width / 2, CAR.length, CAR.width, 3);
  context.fill();

  context.fillStyle = car.accent;
  context.fillRect(CAR.length / 2 - 4, -2, 3, 4);

  context.fillStyle = "#101010";
  context.fillRect(-3, -CAR.width / 2 + 1, 6, 2);
  context.fillRect(-3, CAR.width / 2 - 3, 6, 2);
  context.fillRect(CAR.length / 2 - 5, -CAR.width / 2 + 1, 4, 2);
  context.fillRect(CAR.length / 2 - 5, CAR.width / 2 - 3, 4, 2);

  context.strokeStyle = "rgba(255,255,255,0.35)";
  context.lineWidth = 1;
  context.beginPath();
  context.moveTo(-2, 0);
  context.lineTo(CAR.length / 2 - 2, 0);
  context.stroke();

  if (car.boostTime > 0) {
    const flicker = 0.5 + Math.sin(now / 30) * 0.5;
    context.fillStyle = `rgba(255, 180, 40, ${0.35 + flicker * 0.35})`;
    context.beginPath();
    context.moveTo(-CAR.length / 2 - 2, 0);
    context.lineTo(-CAR.length / 2 - 8 - flicker * 4, -3);
    context.lineTo(-CAR.length / 2 - 8 - flicker * 4, 3);
    context.closePath();
    context.fill();
  }

  if (!car.isPlayer) {
    context.fillStyle = "rgba(255,255,255,0.85)";
    context.font = "600 7px ui-monospace, monospace";
    context.textAlign = "center";
    context.fillText(String(car.position), 0, -CAR.width / 2 - 4);
  } else {
    context.fillStyle = "#fff6cf";
    context.beginPath();
    context.arc(0, 0, 2.2, 0, Math.PI * 2);
    context.fill();
  }

  context.restore();

  context.save();
  context.translate(car.x, car.y);
  context.strokeStyle = "rgba(255,255,255,0.45)";
  context.lineWidth = 1;
  context.beginPath();
  context.moveTo(0, -CAR.width / 2);
  context.lineTo(0, -CAR.width / 2 - 5);
  context.stroke();
  context.restore();
}

function shadeColor(hex, amount) {
  const value = hex.replace("#", "");
  const channels = [
    Number.parseInt(value.slice(0, 2), 16),
    Number.parseInt(value.slice(2, 4), 16),
    Number.parseInt(value.slice(4, 6), 16),
  ].map((channel) => clamp(channel + amount, 0, 255));
  return `#${channels.map((channel) => channel.toString(16).padStart(2, "0")).join("")}`;
}

function clamp(value, min, max) {
  return Math.min(max, Math.max(min, value));
}

function drawCars(now) {
  const drawOrder = [...game.cars].sort(
    (left, right) => left.y - right.y || left.x - right.x,
  );
  for (const car of drawOrder) {
    drawCar(car, now);
  }
}

function drawHudOverlay(now) {
  if (game.phase === "countdown") {
    const count = Math.ceil(Math.max(0, game.countdown));
    context.save();
    context.fillStyle = "rgba(0, 0, 0, 0.35)";
    context.fillRect(0, 0, WORLD.width, WORLD.height);
    context.fillStyle = count > 0 ? "#fff1bf" : "#7dff8a";
    context.font = "900 96px ui-sans-serif, system-ui, sans-serif";
    context.textAlign = "center";
    context.textBaseline = "middle";
    context.fillText(count > 0 ? String(count) : "GO!", WORLD.cx, WORLD.cy - 20);
    context.restore();
  }

  context.save();
  context.fillStyle = "rgba(255, 240, 200, 0.72)";
  context.font = "600 14px ui-monospace, SFMono-Regular, Menlo, monospace";
  context.textAlign = "left";
  context.fillText("RC LOOP GP", 18, 24);
  context.textAlign = "right";
  context.fillText(`${TRACK.lapCount} LAP CARPET OVAL`, WORLD.width - 18, 24);
  context.restore();
}

function animationFrame(now) {
  const deltaSeconds = Math.min(0.1, (now - lastFrame) / 1000);
  lastFrame = now;

  updateControls();
  game.update(deltaSeconds);
  recordSkids(now);
  processGameEvents();
  updateHud();
  drawPlayfield(now);
  requestAnimationFrame(animationFrame);
}

startButton.addEventListener("click", beginGame);
resetButton.addEventListener("click", beginGame);

soundButton.addEventListener("click", () => {
  soundEnabled = !soundEnabled;
  soundButton.setAttribute("aria-pressed", String(soundEnabled));
  soundButton.textContent = soundEnabled ? "Sound on" : "Sound off";
  if (soundEnabled) {
    playTone(440, 0.08, 0, "sine", 0.03);
  }
});

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
  if (event.code === "Space" && game.phase === "ready") {
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

bestValue.textContent = bestPlace <= 5 ? ordinal(bestPlace) : "—";
updateHud();
resizeCanvas();
drawPlayfield(performance.now());
requestAnimationFrame(animationFrame);
