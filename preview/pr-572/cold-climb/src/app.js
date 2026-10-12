import { BOARD, ColdClimbGame, HOLE_COUNT, axisFromDrag } from "./game.js";

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
const targetValue = document.querySelector("#target-value");
const scoreValue = document.querySelector("#score-value");
const bestValue = document.querySelector("#best-value");
const livesValue = document.querySelector("#lives-value");
const leftControlElement = document.querySelector("#left-control");
const rightControlElement = document.querySelector("#right-control");

const game = new ColdClimbGame();
const pressedKeys = new Set();
const HIGH_SCORE_KEY = "cold-climb-high-score";
let highScore = readHighScore();
let soundEnabled = true;
let audioContext = null;
let lastFrame = performance.now();
let ballRotation = 0;

const decorativeBubbles = [
  [86, 92, 8],
  [638, 178, 13],
  [75, 300, 11],
  [650, 400, 7],
  [90, 655, 14],
  [625, 820, 10],
  [102, 940, 7],
  [610, 980, 15],
];

class TouchStick {
  constructor(element) {
    this.element = element;
    this.pointerId = null;
    this.startY = 0;
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
    this.startY = event.clientY;
    this.element.setPointerCapture(event.pointerId);
    this.element.classList.add("is-active");
    this.#setAxis(0);
  }

  #move(event) {
    if (event.pointerId !== this.pointerId) {
      return;
    }

    event.preventDefault();
    this.#setAxis(axisFromDrag(this.startY, event.clientY));
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
    this.element.style.setProperty("--knob-y", `${Math.round(axis * -25)}px`);
    this.element.setAttribute("aria-valuenow", String(Math.round(axis * 100)));
    this.element.setAttribute(
      "aria-valuetext",
      axis > 0.08 ? "Rising" : axis < -0.08 ? "Lowering" : "Stopped",
    );
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

const leftStick = new TouchStick(leftControlElement);
const rightStick = new TouchStick(rightControlElement);

function readHighScore() {
  try {
    const value = Number.parseInt(localStorage.getItem(HIGH_SCORE_KEY), 10);
    return Number.isFinite(value) ? value : 0;
  } catch {
    return 0;
  }
}

function saveHighScore() {
  if (game.score <= highScore) {
    return;
  }

  highScore = game.score;
  try {
    localStorage.setItem(HIGH_SCORE_KEY, String(highScore));
  } catch {
    // Storage can be unavailable in private browsing; the in-memory score remains.
  }
}

function resetInputs() {
  leftStick.reset();
  rightStick.reset();
  pressedKeys.clear();
  game.setControls(0, 0);
}

function beginGame() {
  ensureAudio();
  resetInputs();
  game.start();
  overlay.hidden = true;
  resetButton.disabled = false;
  setMessage("Target 1 is lit. Keep the ball out of every dark pocket.");
  playStartSound();
  updateHud();
}

function showEndScreen(won) {
  resetInputs();
  saveHighScore();
  overlayKicker.textContent = won ? "Perfect pour" : "Ball return";
  overlayTitle.textContent = won ? "You cleared the wall!" : "Last call";
  overlayCopy.textContent = won
    ? `All ${HOLE_COUNT} pockets cleared with ${game.score.toLocaleString()} points.`
    : `You reached target ${Math.min(game.level + 1, HOLE_COUNT)} with ${game.score.toLocaleString()} points.`;
  startButton.textContent = "Play again";
  overlay.hidden = false;
  updateHud();
}

function setMessage(text) {
  message.textContent = text;
}

function updateHud() {
  const shownTarget = Math.min(game.level + 1, HOLE_COUNT);
  targetValue.textContent = `${shownTarget}/${HOLE_COUNT}`;
  scoreValue.textContent = game.score.toLocaleString().padStart(5, "0");
  bestValue.textContent = highScore.toLocaleString().padStart(5, "0");
  livesValue.textContent = `${"●".repeat(game.lives)}${"○".repeat(3 - game.lives)}`;
  livesValue.setAttribute(
    "aria-label",
    `${game.lives} ${game.lives === 1 ? "ball" : "balls"} remaining`,
  );
}

function controlFromKeys(upKey, downKey) {
  return Math.max(
    -1,
    Math.min(1, Number(pressedKeys.has(upKey)) - Number(pressedKeys.has(downKey))),
  );
}

function updateControls() {
  if (game.phase !== "playing") {
    return;
  }

  const leftKeyboard = controlFromKeys("KeyW", "KeyS");
  const rightKeyboard = controlFromKeys("ArrowUp", "ArrowDown");
  game.setControls(
    Math.max(-1, Math.min(1, leftStick.axis + leftKeyboard)),
    Math.max(-1, Math.min(1, rightStick.axis + rightKeyboard)),
  );
}

function processGameEvents() {
  for (const event of game.consumeEvents()) {
    if (event.type === "hole") {
      resetInputs();
      if (event.success) {
        setMessage(`Pocket ${event.hole.id}! Nice catch.`);
        playSuccessSound();
        vibrate([18, 35, 28]);
      } else {
        setMessage(`Pocket ${event.hole.id} was dark. Ball lost.`);
        playMissSound();
        vibrate(90);
      }
    } else if (event.type === "target") {
      saveHighScore();
      setMessage(
        `+${event.points.toLocaleString()} · Target ${event.target.id} is now lit.`,
      );
    } else if (event.type === "retry") {
      setMessage(
        `${event.lives} ${event.lives === 1 ? "ball" : "balls"} left · Target ${game.target.id} is still lit.`,
      );
    } else if (event.type === "edge") {
      playEdgeSound();
    } else if (event.type === "won") {
      playWinSound();
      showEndScreen(true);
    } else if (event.type === "gameover") {
      playGameOverSound();
      showEndScreen(false);
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

function playTone(frequency, duration, delay = 0, type = "sine", volume = 0.05) {
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
  gain.gain.exponentialRampToValueAtTime(volume, start + 0.012);
  gain.gain.exponentialRampToValueAtTime(0.0001, start + duration);
  oscillator.connect(gain).connect(audio.destination);
  oscillator.start(start);
  oscillator.stop(start + duration + 0.02);
}

function playStartSound() {
  playTone(220, 0.12, 0, "square", 0.025);
  playTone(330, 0.16, 0.1, "square", 0.025);
}

function playSuccessSound() {
  playTone(440, 0.18, 0, "triangle", 0.055);
  playTone(660, 0.22, 0.1, "triangle", 0.05);
  playTone(880, 0.28, 0.2, "triangle", 0.045);
}

function playMissSound() {
  playTone(150, 0.34, 0, "sawtooth", 0.035);
  playTone(105, 0.4, 0.12, "sawtooth", 0.03);
}

function playEdgeSound() {
  playTone(190, 0.045, 0, "square", 0.018);
}

function playWinSound() {
  [523, 659, 784, 1047].forEach((frequency, index) => {
    playTone(frequency, 0.32, index * 0.11, "triangle", 0.045);
  });
}

function playGameOverSound() {
  [220, 185, 147].forEach((frequency, index) => {
    playTone(frequency, 0.32, index * 0.16, "square", 0.025);
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

function drawPlayfield(now) {
  const scaleX = canvas.width / BOARD.width;
  const scaleY = canvas.height / BOARD.height;
  context.setTransform(scaleX, 0, 0, scaleY, 0, 0);
  context.clearRect(0, 0, BOARD.width, BOARD.height);

  const background = context.createLinearGradient(0, 0, BOARD.width, BOARD.height);
  background.addColorStop(0, "#ca741f");
  background.addColorStop(0.48, "#9f4a15");
  background.addColorStop(1, "#61230f");
  context.fillStyle = background;
  context.fillRect(0, 0, BOARD.width, BOARD.height);

  const shine = context.createRadialGradient(230, 130, 20, 280, 250, 700);
  shine.addColorStop(0, "rgba(255, 206, 103, 0.24)");
  shine.addColorStop(1, "rgba(255, 206, 103, 0)");
  context.fillStyle = shine;
  context.fillRect(0, 0, BOARD.width, BOARD.height);

  context.save();
  context.strokeStyle = "rgba(255, 213, 132, 0.16)";
  context.lineWidth = 3;
  for (const [x, y, radius] of decorativeBubbles) {
    context.beginPath();
    context.arc(x, y, radius, 0, Math.PI * 2);
    context.stroke();
  }
  context.restore();

  drawRails();
  drawHoles(now);
  drawBar();
  drawBall();

  context.save();
  context.fillStyle = "rgba(255, 237, 194, 0.5)";
  context.font = "600 17px ui-monospace, SFMono-Regular, Menlo, monospace";
  context.textAlign = "left";
  context.fillText("TWO-HANDLE PRECISION TEST", 24, 34);
  context.textAlign = "right";
  context.fillText(`POCKET ${Math.min(game.level + 1, HOLE_COUNT)}`, 696, 34);
  context.restore();
}

function drawRails() {
  context.save();
  context.lineCap = "round";
  context.strokeStyle = "rgba(55, 17, 7, 0.38)";
  context.lineWidth = 10;
  context.beginPath();
  context.moveTo(BOARD.barLeftX, 70);
  context.lineTo(BOARD.barLeftX, 1035);
  context.moveTo(BOARD.barRightX, 70);
  context.lineTo(BOARD.barRightX, 1035);
  context.stroke();

  context.strokeStyle = "rgba(255, 207, 120, 0.19)";
  context.lineWidth = 2;
  context.beginPath();
  context.moveTo(BOARD.barLeftX - 2, 70);
  context.lineTo(BOARD.barLeftX - 2, 1035);
  context.moveTo(BOARD.barRightX - 2, 70);
  context.lineTo(BOARD.barRightX - 2, 1035);
  context.stroke();
  context.restore();
}

function drawHoles(now) {
  const pulse = 0.5 + Math.sin(now / 170) * 0.5;

  for (const hole of game.holes) {
    const isTarget = hole.id === game.target?.id && game.phase !== "won";

    context.save();
    if (isTarget) {
      context.shadowColor = "#fff0a6";
      context.shadowBlur = 22 + pulse * 14;
      context.strokeStyle = `rgba(255, 239, 150, ${0.78 + pulse * 0.22})`;
      context.lineWidth = 8;
      context.beginPath();
      context.arc(hole.x, hole.y, hole.radius + 10 + pulse * 2, 0, Math.PI * 2);
      context.stroke();
    }

    const rim = context.createRadialGradient(
      hole.x - 7,
      hole.y - 8,
      3,
      hole.x,
      hole.y,
      hole.radius + 7,
    );
    rim.addColorStop(0, "#110805");
    rim.addColorStop(0.62, "#251008");
    rim.addColorStop(0.7, "#4b1d0b");
    rim.addColorStop(0.84, isTarget ? "#f2ba3b" : "#7b3512");
    rim.addColorStop(1, "#3a1408");
    context.fillStyle = rim;
    context.beginPath();
    context.arc(hole.x, hole.y, hole.radius + 5, 0, Math.PI * 2);
    context.fill();

    if (isTarget) {
      const glow = context.createRadialGradient(
        hole.x,
        hole.y,
        1,
        hole.x,
        hole.y,
        hole.radius,
      );
      glow.addColorStop(0, "rgba(255, 244, 173, 0.42)");
      glow.addColorStop(1, "rgba(245, 170, 36, 0)");
      context.fillStyle = glow;
      context.beginPath();
      context.arc(hole.x, hole.y, hole.radius - 2, 0, Math.PI * 2);
      context.fill();
    }

    context.shadowBlur = 0;
    context.fillStyle = isTarget ? "#fff3b7" : "rgba(255, 213, 142, 0.7)";
    context.font = "700 22px ui-monospace, SFMono-Regular, Menlo, monospace";
    context.textAlign = "center";
    context.textBaseline = "middle";
    context.fillText(String(hole.id), hole.x, hole.y + 1);
    context.restore();
  }
}

function drawBar() {
  const leftX = BOARD.barLeftX;
  const rightX = BOARD.barRightX;
  const leftY = game.leftBarY;
  const rightY = game.rightBarY;

  context.save();
  context.lineCap = "round";
  context.strokeStyle = "rgba(33, 12, 5, 0.55)";
  context.lineWidth = 24;
  context.beginPath();
  context.moveTo(leftX, leftY + 7);
  context.lineTo(rightX, rightY + 7);
  context.stroke();

  const metal = context.createLinearGradient(leftX, leftY, rightX, rightY);
  metal.addColorStop(0, "#6d7473");
  metal.addColorStop(0.18, "#e8eee6");
  metal.addColorStop(0.52, "#8c9692");
  metal.addColorStop(0.78, "#f8f4df");
  metal.addColorStop(1, "#656b69");
  context.strokeStyle = metal;
  context.lineWidth = BOARD.barRadius * 2;
  context.beginPath();
  context.moveTo(leftX, leftY);
  context.lineTo(rightX, rightY);
  context.stroke();

  context.strokeStyle = "rgba(255, 255, 244, 0.62)";
  context.lineWidth = 3;
  context.beginPath();
  context.moveTo(leftX + 5, leftY - 4);
  context.lineTo(rightX - 5, rightY - 4);
  context.stroke();

  for (const [x, y] of [
    [leftX, leftY],
    [rightX, rightY],
  ]) {
    context.fillStyle = "#292c2b";
    context.beginPath();
    context.arc(x, y, 17, 0, Math.PI * 2);
    context.fill();
    context.strokeStyle = "#d6d9cf";
    context.lineWidth = 5;
    context.stroke();
  }
  context.restore();
}

function drawBall() {
  let x = game.ballX;
  if (game.phase === "falling" && game.fall) {
    const progress = Math.min(1, game.fall.elapsed / BOARD.fallDuration);
    const eased = progress * progress;
    x = game.fall.originX + (game.fall.hole.x - game.fall.originX) * eased;
  }
  const y = game.ballY;
  const radius = BOARD.ballRadius * game.ballScale;

  context.save();
  context.translate(x, y);
  context.rotate(ballRotation);
  context.shadowColor = "rgba(29, 9, 3, 0.65)";
  context.shadowBlur = 12;
  context.shadowOffsetY = 8;

  const steel = context.createRadialGradient(-7, -9, 2, 0, 0, radius);
  steel.addColorStop(0, "#ffffff");
  steel.addColorStop(0.16, "#e8eee9");
  steel.addColorStop(0.48, "#8f9996");
  steel.addColorStop(0.78, "#4c5553");
  steel.addColorStop(1, "#1c2221");
  context.fillStyle = steel;
  context.beginPath();
  context.arc(0, 0, Math.max(2, radius), 0, Math.PI * 2);
  context.fill();

  context.shadowBlur = 0;
  context.strokeStyle = "rgba(255, 255, 255, 0.6)";
  context.lineWidth = 2;
  context.beginPath();
  context.arc(-5, -5, Math.max(1, radius * 0.36), Math.PI, Math.PI * 1.72);
  context.stroke();
  context.restore();
}

function animationFrame(now) {
  const deltaSeconds = Math.min(0.1, (now - lastFrame) / 1000);
  lastFrame = now;

  updateControls();
  const previousX = game.ballX;
  game.update(deltaSeconds);
  ballRotation += (game.ballX - previousX) / BOARD.ballRadius;
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
    playTone(440, 0.08, 0, "sine", 0.035);
  }
});

window.addEventListener("keydown", (event) => {
  const controlKeys = new Set([
    "KeyW",
    "KeyS",
    "ArrowUp",
    "ArrowDown",
    "Space",
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

bestValue.textContent = highScore.toLocaleString().padStart(5, "0");
updateHud();
resizeCanvas();
drawPlayfield(performance.now());
requestAnimationFrame(animationFrame);
