import {
  ArtilleryGame,
  WORLD,
  barrelPose,
  chooseComputerAim,
  createProjectile,
  tankPose,
  terrainHeightAt,
} from "./game.js";

const canvas = document.querySelector("#game-canvas");
const context = canvas.getContext("2d");
const battlefield = document.querySelector(".battlefield-frame");
const overlay = document.querySelector("#screen-overlay");
const overlayKicker = document.querySelector("#overlay-kicker");
const overlayTitle = document.querySelector("#overlay-title");
const overlayCopy = document.querySelector("#overlay-copy");
const modeButtons = [...document.querySelectorAll("[data-mode]")];
const newDuelButton = document.querySelector("#new-duel-button");
const soundButton = document.querySelector("#sound-button");
const soundLabel = document.querySelector("#sound-label");
const message = document.querySelector("#message");
const shotReadout = document.querySelector("#shot-readout");
const windArrow = document.querySelector("#wind-arrow");
const windValue = document.querySelector("#wind-value");
const turnValue = document.querySelector("#turn-value");
const operatorName = document.querySelector("#operator-name");
const readyBadge = document.querySelector("#ready-badge");
const angleInput = document.querySelector("#angle-input");
const powerInput = document.querySelector("#power-input");
const angleOutput = document.querySelector("#angle-output");
const powerOutput = document.querySelector("#power-output");
const arcValue = document.querySelector("#arc-value");
const driftValue = document.querySelector("#drift-value");
const fireButton = document.querySelector("#fire-button");
const adjustButtons = [...document.querySelectorAll(".adjust-button")];
const playerCards = [0, 1].map((index) =>
  document.querySelector(`#player-card-${index}`),
);
const playerNames = [0, 1].map((index) =>
  document.querySelector(`#player-name-${index}`),
);
const healthValues = [0, 1].map((index) =>
  document.querySelector(`#health-value-${index}`),
);
const healthBars = [0, 1].map((index) =>
  document.querySelector(`#health-bar-${index}`),
);

const game = new ArtilleryGame();
const stars = Array.from({ length: 82 }, (_, index) => ({
  x: (index * 197.31 + 43) % WORLD.width,
  y: (index * index * 11.73 + 21) % 330,
  radius: 0.6 + ((index * 17) % 10) / 10,
  alpha: 0.2 + ((index * 23) % 70) / 100,
}));

let mode = "cpu";
let modalOpen = true;
let soundEnabled = true;
let audioContext = null;
let masterGain = null;
let aiTimer = null;
let lastFrame = performance.now();
let lastUiTick = 0;
let trail = [];
let particles = [];
let muzzleFlash = null;

function getPlayerName(index) {
  if (index === 0) {
    return mode === "local" ? "Cyan" : "Ranger";
  }
  return mode === "cpu" ? "Vector AI" : "Magenta";
}

function humanCanControl() {
  return (
    !modalOpen &&
    game.phase === "aiming" &&
    (mode === "local" || game.activePlayer === 0)
  );
}

function setMessage(text) {
  message.textContent = text;
}

function setRangeFill(input) {
  const minimum = Number(input.min);
  const maximum = Number(input.max);
  const value = Number(input.value);
  const percentage = ((value - minimum) / (maximum - minimum)) * 100;
  input.style.setProperty("--fill", `${percentage}%`);
}

function describeArc(angle) {
  if (angle >= 64) {
    return "High arc";
  }
  if (angle <= 29) {
    return "Low drive";
  }
  return "Balanced";
}

function describeWind(wind) {
  if (wind === 0) {
    return "Calm";
  }
  return `${wind > 0 ? "East" : "West"} ${Math.abs(wind).toFixed(1)}`;
}

function updateAimReadouts() {
  const angle = Number(angleInput.value);
  const power = Number(powerInput.value);
  angleOutput.textContent = `${angle}°`;
  powerOutput.textContent = `${power}%`;
  shotReadout.textContent = `A${angle}° / P${power}`;
  arcValue.textContent = describeArc(angle);
  driftValue.textContent = describeWind(game.wind);
  setRangeFill(angleInput);
  setRangeFill(powerInput);
}

function loadCurrentAim() {
  angleInput.value = String(game.currentAim.angle);
  powerInput.value = String(game.currentAim.power);
  updateAimReadouts();
}

function applyInputAim(withSound = false) {
  if (!humanCanControl()) {
    loadCurrentAim();
    return;
  }

  const aim = game.setAim(Number(angleInput.value), Number(powerInput.value));
  angleInput.value = String(aim.angle);
  powerInput.value = String(aim.power);
  updateAimReadouts();

  if (withSound && performance.now() - lastUiTick > 45) {
    playUiTick();
    lastUiTick = performance.now();
  }
}

function clearComputerTimer() {
  if (aiTimer !== null) {
    window.clearTimeout(aiTimer);
    aiTimer = null;
  }
}

function startDuel(selectedMode) {
  mode = selectedMode === "local" ? "local" : "cpu";
  modalOpen = false;
  clearComputerTimer();
  ensureAudio();
  trail = [];
  particles = [];
  muzzleFlash = null;
  game.start(0);
  overlay.hidden = true;
  playerNames[0].textContent = getPlayerName(0);
  playerNames[1].textContent = getPlayerName(1);
  loadCurrentAim();
  processGameEvents();
  syncHud();
  playBootSound();
  vibrate(18);
}

function resetOverlayCopy() {
  overlayKicker.textContent = "Frontier protocol";
  overlayTitle.innerHTML = "Read the wind.<br>Own the horizon.";
  overlayCopy.textContent =
    "Set your angle and powder, then send it. Direct hits deal maximum damage; nearby blasts still bite.";
  const [cpuButton, localButton] = modeButtons;
  cpuButton.querySelector("strong").textContent = "Vs. Vector AI";
  cpuButton.querySelector("small").textContent = "Imperfect machine rival";
  localButton.querySelector("strong").textContent = "Two players";
  localButton.querySelector("small").textContent = "Pass-and-play duel";
}

function showModeScreen() {
  clearComputerTimer();
  modalOpen = true;
  resetOverlayCopy();
  overlay.hidden = false;
  syncHud();
}

function showEndScreen(winner) {
  clearComputerTimer();
  modalOpen = true;
  const winnerName = getPlayerName(winner);
  overlayKicker.textContent = "Duel complete";
  overlayTitle.textContent = `${winnerName} controls the horizon`;
  overlayCopy.textContent =
    winner === 0 && mode === "cpu"
      ? "Vector AI has been neutralized. Run the simulation again or hand the controls to a second player."
      : `${winnerName} found the decisive firing solution. Re-arm for another duel.`;

  const [cpuButton, localButton] = modeButtons;
  cpuButton.querySelector("strong").textContent =
    mode === "cpu" ? "Rematch AI" : "Challenge the AI";
  cpuButton.querySelector("small").textContent = "New armor, same battlefield";
  localButton.querySelector("strong").textContent =
    mode === "local" ? "Play again" : "Two-player duel";
  localButton.querySelector("small").textContent = "Local pass-and-play";
  overlay.hidden = false;
  syncHud();
}

function fireCurrentShot() {
  if (!humanCanControl()) {
    return;
  }

  ensureAudio();
  game.setAim(Number(angleInput.value), Number(powerInput.value));
  game.fire();
  processGameEvents();
  syncHud();
}

function queueComputerTurn() {
  clearComputerTimer();
  setMessage("Vector AI is sampling the crosswind…");

  aiTimer = window.setTimeout(() => {
    aiTimer = null;
    if (
      modalOpen ||
      mode !== "cpu" ||
      game.phase !== "aiming" ||
      game.activePlayer !== 1
    ) {
      return;
    }

    const aim = chooseComputerAim({
      terrain: game.terrain,
      tanks: game.tanks,
      shooterIndex: 1,
      wind: game.wind,
    });
    game.setAim(aim.angle, aim.power);
    loadCurrentAim();
    setMessage(`Vector AI locked A${aim.angle}° / P${aim.power}.`);
    playTargetLock();

    aiTimer = window.setTimeout(() => {
      aiTimer = null;
      if (
        !modalOpen &&
        mode === "cpu" &&
        game.phase === "aiming" &&
        game.activePlayer === 1
      ) {
        game.fire();
        processGameEvents();
        syncHud();
      }
    }, 620);
  }, 720);
}

function impactMessage(event) {
  if (event.kind === "out") {
    return "Round left the sensor envelope. No damage.";
  }

  const maximumDamage = Math.max(...event.damages);
  if (maximumDamage === 0) {
    return "Terrain strike. Both armor systems remain intact.";
  }

  const target = event.damages.indexOf(maximumDamage);
  if (event.directTank === target) {
    return `Direct hit on ${getPlayerName(target)} · −${maximumDamage} armor.`;
  }
  return `Blast damage to ${getPlayerName(target)} · −${maximumDamage} armor.`;
}

function processGameEvents() {
  for (const event of game.consumeEvents()) {
    if (event.type === "started") {
      setMessage(
        event.wind === 0
          ? `${getPlayerName(event.player)} online. No crosswind detected.`
          : `${getPlayerName(event.player)} online. Compensate for ${describeWind(event.wind).toLowerCase()} drift.`,
      );
      loadCurrentAim();
    } else if (event.type === "fired") {
      trail = [];
      muzzleFlash = { player: event.player, started: performance.now() };
      setMessage(
        `${getPlayerName(event.player)} launched · A${event.aim.angle}° / P${event.aim.power}.`,
      );
      playFireSound();
      vibrate(24);
    } else if (event.type === "impact") {
      setMessage(impactMessage(event));
      spawnExplosion(event);
      triggerImpactShake();
      playImpactSound(Math.max(...event.damages));
      vibrate(Math.max(...event.damages) > 0 ? [35, 22, 70] : 55);
    } else if (event.type === "turn") {
      loadCurrentAim();
      setMessage(
        `${getPlayerName(event.player)} to fire · wind is ${describeWind(event.wind).toLowerCase()}.`,
      );
      playTurnSound(event.player);
      if (mode === "cpu" && event.player === 1) {
        queueComputerTurn();
      }
    } else if (event.type === "gameover") {
      const winnerName = getPlayerName(event.winner);
      setMessage(`${winnerName} wins the duel.`);
      playVictorySound(event.winner);
      vibrate([45, 45, 45, 45, 110]);
      showEndScreen(event.winner);
    }
  }
}

function syncHud() {
  game.tanks.forEach((tank, index) => {
    const health = Math.max(0, Math.round(tank.health));
    healthValues[index].textContent = String(health);
    healthBars[index].style.width = `${health}%`;
    playerCards[index].classList.toggle(
      "is-active",
      game.phase !== "ready" &&
        game.phase !== "gameover" &&
        game.activePlayer === index,
    );
  });

  const wind = game.wind;
  windValue.textContent = Math.abs(wind).toFixed(1);
  windArrow.textContent = wind === 0 ? "•" : "➜";
  windArrow.style.transform = wind < 0 ? "scaleX(-1)" : "scaleX(1)";
  driftValue.textContent = describeWind(wind);

  const canControl = humanCanControl();
  const controlsDisabled = !canControl;
  angleInput.disabled = controlsDisabled;
  powerInput.disabled = controlsDisabled;
  adjustButtons.forEach((button) => {
    button.disabled = controlsDisabled;
  });
  fireButton.disabled = controlsDisabled;
  readyBadge.classList.toggle("is-ready", canControl);

  if (game.phase === "ready" || modalOpen) {
    turnValue.textContent = "Awaiting deployment";
    operatorName.textContent = "System idle";
    readyBadge.textContent = "Stand by";
  } else if (game.phase === "aiming") {
    const isComputer = mode === "cpu" && game.activePlayer === 1;
    turnValue.textContent = `${getPlayerName(game.activePlayer)} turn`;
    operatorName.textContent = isComputer
      ? "AI calculation"
      : `${getPlayerName(game.activePlayer)} // live`;
    readyBadge.textContent = isComputer ? "Computing" : "Weapon ready";
  } else if (game.phase === "projectile") {
    turnValue.textContent = "Round in flight";
    operatorName.textContent = "Tracking projectile";
    readyBadge.textContent = "Tracking";
  } else if (game.phase === "resolving") {
    turnValue.textContent = "Impact analysis";
    operatorName.textContent = "Reading damage";
    readyBadge.textContent = "Impact";
  } else {
    turnValue.textContent = "Duel complete";
    operatorName.textContent = "Range secured";
    readyBadge.textContent = "Offline";
  }

  canvas.setAttribute(
    "aria-label",
    `${getPlayerName(0)} has ${game.tanks[0].health} armor. ${getPlayerName(1)} has ${game.tanks[1].health} armor. ${turnValue.textContent}.`,
  );
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
    masterGain = audioContext.createGain();
    masterGain.gain.value = 0.72;
    masterGain.connect(audioContext.destination);
  }

  if (audioContext.state === "suspended") {
    audioContext.resume();
  }
  return audioContext;
}

function playTone({
  frequency,
  endFrequency = frequency,
  duration = 0.12,
  delay = 0,
  type = "sine",
  volume = 0.04,
}) {
  const audio = ensureAudio();
  if (!audio) {
    return;
  }

  const start = audio.currentTime + delay;
  const oscillator = audio.createOscillator();
  const gain = audio.createGain();
  oscillator.type = type;
  oscillator.frequency.setValueAtTime(frequency, start);
  oscillator.frequency.exponentialRampToValueAtTime(
    Math.max(1, endFrequency),
    start + duration,
  );
  gain.gain.setValueAtTime(0.0001, start);
  gain.gain.exponentialRampToValueAtTime(volume, start + 0.012);
  gain.gain.exponentialRampToValueAtTime(0.0001, start + duration);
  oscillator.connect(gain).connect(masterGain);
  oscillator.start(start);
  oscillator.stop(start + duration + 0.03);
}

function playNoise({
  duration = 0.25,
  delay = 0,
  volume = 0.08,
  frequency = 900,
}) {
  const audio = ensureAudio();
  if (!audio) {
    return;
  }

  const frameCount = Math.ceil(audio.sampleRate * duration);
  const buffer = audio.createBuffer(1, frameCount, audio.sampleRate);
  const data = buffer.getChannelData(0);
  for (let index = 0; index < frameCount; index += 1) {
    data[index] = Math.random() * 2 - 1;
  }

  const source = audio.createBufferSource();
  const filter = audio.createBiquadFilter();
  const gain = audio.createGain();
  const start = audio.currentTime + delay;
  source.buffer = buffer;
  filter.type = "lowpass";
  filter.frequency.setValueAtTime(frequency, start);
  filter.frequency.exponentialRampToValueAtTime(90, start + duration);
  gain.gain.setValueAtTime(volume, start);
  gain.gain.exponentialRampToValueAtTime(0.0001, start + duration);
  source.connect(filter).connect(gain).connect(masterGain);
  source.start(start);
}

function playUiTick() {
  playTone({
    frequency: 720,
    endFrequency: 580,
    duration: 0.045,
    type: "square",
    volume: 0.012,
  });
}

function playBootSound() {
  [196, 294, 440].forEach((frequency, index) => {
    playTone({
      frequency,
      endFrequency: frequency * 1.02,
      duration: 0.18,
      delay: index * 0.08,
      type: "triangle",
      volume: 0.025,
    });
  });
}

function playTargetLock() {
  playTone({
    frequency: 520,
    endFrequency: 760,
    duration: 0.12,
    type: "square",
    volume: 0.02,
  });
  playTone({
    frequency: 920,
    duration: 0.06,
    delay: 0.13,
    type: "sine",
    volume: 0.026,
  });
}

function playFireSound() {
  playNoise({ duration: 0.22, volume: 0.12, frequency: 1200 });
  playTone({
    frequency: 118,
    endFrequency: 38,
    duration: 0.34,
    type: "sawtooth",
    volume: 0.09,
  });
  playTone({
    frequency: 840,
    endFrequency: 190,
    duration: 0.18,
    type: "square",
    volume: 0.018,
  });
}

function playImpactSound(damage) {
  playNoise({
    duration: damage > 0 ? 0.52 : 0.32,
    volume: damage > 0 ? 0.16 : 0.1,
    frequency: damage > 0 ? 760 : 520,
  });
  playTone({
    frequency: damage > 0 ? 82 : 105,
    endFrequency: 34,
    duration: damage > 0 ? 0.6 : 0.38,
    type: "sine",
    volume: damage > 0 ? 0.12 : 0.07,
  });
  if (damage > 0) {
    playTone({
      frequency: 310,
      endFrequency: 90,
      duration: 0.28,
      delay: 0.06,
      type: "sawtooth",
      volume: 0.035,
    });
  }
}

function playTurnSound(player) {
  const base = player === 0 ? 420 : 330;
  playTone({
    frequency: base,
    endFrequency: base * 1.35,
    duration: 0.14,
    type: "triangle",
    volume: 0.025,
  });
}

function playVictorySound(winner) {
  const notes = winner === 0 ? [392, 523, 659, 784] : [330, 440, 554, 659];
  notes.forEach((frequency, index) => {
    playTone({
      frequency,
      duration: 0.3,
      delay: index * 0.11,
      type: "triangle",
      volume: 0.038,
    });
  });
}

function vibrate(pattern) {
  if ("vibrate" in navigator) {
    navigator.vibrate(pattern);
  }
}

function triggerImpactShake() {
  battlefield.classList.remove("is-impact");
  void battlefield.offsetWidth;
  battlefield.classList.add("is-impact");
  window.setTimeout(() => battlefield.classList.remove("is-impact"), 350);
}

function spawnExplosion(event) {
  const palette =
    event.directTank === 1
      ? ["#fff5d6", "#ff5ba7", "#ff9d55"]
      : ["#fff5d6", "#48f5dc", "#ffb657"];
  const count = event.kind === "out" ? 0 : 64;

  for (let index = 0; index < count; index += 1) {
    const angle = Math.random() * Math.PI * 2;
    const speed = 45 + Math.random() * 235;
    const life = 0.35 + Math.random() * 0.75;
    particles.push({
      x: event.x,
      y: event.y,
      vx: Math.cos(angle) * speed,
      vy: Math.sin(angle) * speed - 35,
      life,
      maximumLife: life,
      size: 2 + Math.random() * 6,
      color: palette[index % palette.length],
    });
  }
}

function updateVisuals(deltaSeconds) {
  if (game.projectile) {
    const previous = trail.at(-1);
    if (
      !previous ||
      Math.hypot(
        previous.x - game.projectile.x,
        previous.y - game.projectile.y,
      ) > 4
    ) {
      trail.push({
        x: game.projectile.x,
        y: game.projectile.y,
        life: 1,
      });
      if (trail.length > 90) {
        trail.shift();
      }
    }
  }

  trail.forEach((point) => {
    point.life -= deltaSeconds * (game.projectile ? 0.28 : 1.15);
  });
  trail = trail.filter((point) => point.life > 0);

  particles.forEach((particle) => {
    particle.life -= deltaSeconds;
    particle.vy += 180 * deltaSeconds;
    particle.vx *= Math.exp(-0.75 * deltaSeconds);
    particle.x += particle.vx * deltaSeconds;
    particle.y += particle.vy * deltaSeconds;
  });
  particles = particles.filter((particle) => particle.life > 0);

  if (muzzleFlash && performance.now() - muzzleFlash.started > 170) {
    muzzleFlash = null;
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

function drawBackground(now) {
  const sky = context.createLinearGradient(0, 0, 0, WORLD.height);
  sky.addColorStop(0, "#06101d");
  sky.addColorStop(0.55, "#0b1c2b");
  sky.addColorStop(1, "#122631");
  context.fillStyle = sky;
  context.fillRect(0, 0, WORLD.width, WORLD.height);

  const horizonGlow = context.createRadialGradient(610, 400, 20, 610, 400, 540);
  horizonGlow.addColorStop(0, "rgba(52, 190, 184, 0.16)");
  horizonGlow.addColorStop(0.52, "rgba(15, 64, 82, 0.09)");
  horizonGlow.addColorStop(1, "rgba(4, 14, 24, 0)");
  context.fillStyle = horizonGlow;
  context.fillRect(0, 0, WORLD.width, WORLD.height);

  context.save();
  for (const star of stars) {
    const shimmer = 0.65 + Math.sin(now * 0.0015 + star.x) * 0.25;
    context.globalAlpha = star.alpha * shimmer;
    context.fillStyle = "#c5f5ff";
    context.beginPath();
    context.arc(star.x, star.y, star.radius, 0, Math.PI * 2);
    context.fill();
  }
  context.restore();

  context.save();
  context.shadowColor = "rgba(102, 222, 236, 0.35)";
  context.shadowBlur = 32;
  const moon = context.createRadialGradient(987, 113, 8, 987, 113, 54);
  moon.addColorStop(0, "#d6ffff");
  moon.addColorStop(0.66, "#80c7d1");
  moon.addColorStop(1, "#2a6574");
  context.fillStyle = moon;
  context.beginPath();
  context.arc(987, 113, 54, 0, Math.PI * 2);
  context.fill();
  context.shadowBlur = 0;
  context.fillStyle = "rgba(7, 22, 35, 0.83)";
  context.beginPath();
  context.arc(1006, 96, 51, 0, Math.PI * 2);
  context.fill();
  context.restore();

  drawDistantRange();
  drawHorizonGrid();
  drawWindStreaks(now);
}

function drawDistantRange() {
  context.save();
  context.fillStyle = "rgba(13, 37, 50, 0.78)";
  context.beginPath();
  context.moveTo(0, 410);
  context.lineTo(90, 338);
  context.lineTo(176, 392);
  context.lineTo(276, 312);
  context.lineTo(381, 389);
  context.lineTo(493, 325);
  context.lineTo(610, 403);
  context.lineTo(748, 301);
  context.lineTo(846, 378);
  context.lineTo(952, 319);
  context.lineTo(1087, 392);
  context.lineTo(1200, 326);
  context.lineTo(1200, 520);
  context.lineTo(0, 520);
  context.closePath();
  context.fill();

  context.strokeStyle = "rgba(66, 137, 153, 0.22)";
  context.lineWidth = 2;
  context.stroke();

  context.fillStyle = "rgba(8, 25, 37, 0.9)";
  for (let index = 0; index < 17; index += 1) {
    const x = 420 + index * 25;
    const height = 18 + ((index * 19) % 46);
    context.fillRect(x, 418 - height, 11 + (index % 3) * 4, height);
    if (index % 2 === 0) {
      context.fillStyle = "rgba(69, 234, 216, 0.28)";
      context.fillRect(x + 4, 408 - height, 2, 2);
      context.fillStyle = "rgba(8, 25, 37, 0.9)";
    }
  }
  context.restore();
}

function drawHorizonGrid() {
  context.save();
  context.strokeStyle = "rgba(79, 174, 183, 0.095)";
  context.lineWidth = 1;
  for (let y = 370; y <= 520; y += 26) {
    context.beginPath();
    context.moveTo(0, y);
    context.lineTo(WORLD.width, y);
    context.stroke();
  }
  for (let x = -200; x <= WORLD.width + 200; x += 80) {
    context.beginPath();
    context.moveTo(WORLD.width / 2, 355);
    context.lineTo(x, 530);
    context.stroke();
  }
  context.restore();
}

function positiveModulo(value, divisor) {
  return ((value % divisor) + divisor) % divisor;
}

function drawWindStreaks(now) {
  if (Math.abs(game.wind) < 0.8) {
    return;
  }

  const direction = Math.sign(game.wind);
  const speed = Math.abs(game.wind) * 0.025;
  context.save();
  context.strokeStyle = "rgba(255, 214, 125, 0.16)";
  context.lineWidth = 1.5;
  context.lineCap = "round";
  for (let index = 0; index < 13; index += 1) {
    const travel = now * speed * direction;
    const x = positiveModulo(index * 113 + travel + 100, WORLD.width + 200) - 100;
    const y = 105 + ((index * 71) % 270);
    const length = 22 + (index % 4) * 9;
    context.beginPath();
    context.moveTo(x, y);
    context.lineTo(x + direction * length, y);
    context.stroke();
  }
  context.restore();
}

function terrainPath() {
  context.beginPath();
  context.moveTo(0, WORLD.height);
  context.lineTo(0, game.terrain[0]);
  for (let x = 0; x <= WORLD.width; x += 4) {
    context.lineTo(x, game.terrain[x]);
  }
  context.lineTo(WORLD.width, WORLD.height);
  context.closePath();
}

function drawTerrain() {
  const ground = context.createLinearGradient(0, 400, 0, WORLD.height);
  ground.addColorStop(0, "#183c43");
  ground.addColorStop(0.18, "#102b34");
  ground.addColorStop(1, "#07151f");
  terrainPath();
  context.fillStyle = ground;
  context.fill();

  context.save();
  terrainPath();
  context.clip();
  context.strokeStyle = "rgba(76, 165, 170, 0.09)";
  context.lineWidth = 1;
  for (let x = 0; x <= WORLD.width; x += 34) {
    context.beginPath();
    context.moveTo(x, 420);
    context.lineTo(x, WORLD.height);
    context.stroke();
  }
  for (let y = 465; y <= WORLD.height; y += 27) {
    context.beginPath();
    context.moveTo(0, y);
    context.lineTo(WORLD.width, y);
    context.stroke();
  }
  context.restore();

  context.save();
  context.shadowColor = "rgba(53, 242, 216, 0.38)";
  context.shadowBlur = 10;
  context.strokeStyle = "#3bd4c6";
  context.lineWidth = 2;
  context.beginPath();
  context.moveTo(0, game.terrain[0]);
  for (let x = 0; x <= WORLD.width; x += 3) {
    context.lineTo(x, game.terrain[x]);
  }
  context.stroke();
  context.shadowBlur = 0;
  context.strokeStyle = "rgba(187, 255, 244, 0.24)";
  context.lineWidth = 1;
  context.stroke();
  context.restore();
}

function drawTrajectoryPreview() {
  if (game.phase !== "aiming" || modalOpen) {
    return;
  }

  const projectile = createProjectile(
    game.terrain,
    game.activePlayer,
    game.currentAim,
    game.wind,
  );
  const color = game.activePlayer === 0 ? "#65f8e5" : "#ff68b0";
  context.save();
  context.fillStyle = color;
  context.shadowColor = color;
  context.shadowBlur = 7;
  for (let index = 1; index <= 9; index += 1) {
    const time = index * 0.075;
    const x =
      projectile.x +
      projectile.vx * time +
      0.5 * projectile.wind * WORLD.windScale * time * time;
    const y =
      projectile.y +
      projectile.vy * time +
      0.5 * WORLD.gravity * time * time;
    context.globalAlpha = 0.8 - index * 0.065;
    context.beginPath();
    context.arc(x, y, Math.max(1.3, 3.2 - index * 0.18), 0, Math.PI * 2);
    context.fill();
  }
  context.restore();
}

function drawTank(tank, index, now) {
  const pose = tankPose(game.terrain, index);
  const groundAngle = pose.groundAngle;
  const aim = game.aims[index];
  const direction = index === 0 ? 1 : -1;
  const radians = (aim.angle * Math.PI) / 180;
  const color = index === 0 ? "#39f2db" : "#ff4ea3";
  const darkColor = index === 0 ? "#0c7f79" : "#8e275a";
  const active =
    game.activePlayer === index &&
    !modalOpen &&
    game.phase !== "gameover" &&
    game.phase !== "ready";

  if (active) {
    const pulse = 0.55 + Math.sin(now * 0.004) * 0.18;
    context.save();
    context.strokeStyle =
      index === 0
        ? `rgba(57, 242, 219, ${pulse})`
        : `rgba(255, 78, 163, ${pulse})`;
    context.lineWidth = 2;
    context.setLineDash([8, 8]);
    context.beginPath();
    context.ellipse(tank.x, tank.y + 17, 54, 13, 0, 0, Math.PI * 2);
    context.stroke();
    context.restore();
  }

  context.save();
  context.translate(tank.x, tank.y);
  context.rotate(groundAngle);

  context.save();
  context.strokeStyle = darkColor;
  context.lineWidth = 12;
  context.lineCap = "round";
  context.shadowColor = color;
  context.shadowBlur = active ? 14 : 5;
  context.beginPath();
  context.moveTo(0, -7);
  context.lineTo(
    direction * Math.cos(radians) * WORLD.barrelLength,
    -7 - Math.sin(radians) * WORLD.barrelLength,
  );
  context.stroke();
  context.strokeStyle = color;
  context.lineWidth = 4;
  context.stroke();
  context.restore();

  context.fillStyle = "#061119";
  context.strokeStyle = darkColor;
  context.lineWidth = 3;
  context.beginPath();
  context.roundRect(-31, 4, 62, 17, 7);
  context.fill();
  context.stroke();

  const body = context.createLinearGradient(-25, -18, 25, 14);
  body.addColorStop(0, color);
  body.addColorStop(0.42, darkColor);
  body.addColorStop(1, "#09202a");
  context.fillStyle = body;
  context.shadowColor = color;
  context.shadowBlur = active ? 11 : 4;
  context.beginPath();
  context.moveTo(-26, 7);
  context.lineTo(-18, -13);
  context.lineTo(17, -13);
  context.lineTo(28, 7);
  context.closePath();
  context.fill();

  context.fillStyle = "#07141d";
  context.strokeStyle = color;
  context.lineWidth = 2.5;
  context.beginPath();
  context.arc(0, -12, 12, Math.PI, 0);
  context.lineTo(12, -7);
  context.lineTo(-12, -7);
  context.closePath();
  context.fill();
  context.stroke();

  context.shadowBlur = 0;
  context.fillStyle = color;
  for (const x of [-19, 0, 19]) {
    context.beginPath();
    context.arc(x, 12, 4, 0, Math.PI * 2);
    context.fill();
  }
  context.restore();

  if (
    muzzleFlash?.player === index &&
    performance.now() - muzzleFlash.started < 170
  ) {
    const barrel = barrelPose(game.terrain, index, aim);
    const progress = (performance.now() - muzzleFlash.started) / 170;
    context.save();
    context.globalAlpha = 1 - progress;
    context.translate(barrel.tipX, barrel.tipY);
    context.shadowColor = "#fff3b0";
    context.shadowBlur = 20;
    context.fillStyle = "#fff6cf";
    context.beginPath();
    context.arc(0, 0, 15 * (1 - progress * 0.5), 0, Math.PI * 2);
    context.fill();
    context.restore();
  }
}

function drawTrailAndProjectile() {
  if (trail.length > 1) {
    context.save();
    context.lineCap = "round";
    context.lineJoin = "round";
    for (let index = 1; index < trail.length; index += 1) {
      const point = trail[index];
      const previous = trail[index - 1];
      context.globalAlpha = point.life * (index / trail.length) * 0.72;
      context.strokeStyle =
        game.activePlayer === 0 ? "#72fff0" : "#ff79bb";
      context.lineWidth = 1 + (index / trail.length) * 3;
      context.beginPath();
      context.moveTo(previous.x, previous.y);
      context.lineTo(point.x, point.y);
      context.stroke();
    }
    context.restore();
  }

  if (!game.projectile) {
    return;
  }

  const color = game.projectile.shooter === 0 ? "#73fff0" : "#ff76b9";
  context.save();
  context.shadowColor = color;
  context.shadowBlur = 22;
  const glow = context.createRadialGradient(
    game.projectile.x - 2,
    game.projectile.y - 2,
    1,
    game.projectile.x,
    game.projectile.y,
    12,
  );
  glow.addColorStop(0, "#ffffff");
  glow.addColorStop(0.35, color);
  glow.addColorStop(1, "rgba(255,255,255,0)");
  context.fillStyle = glow;
  context.beginPath();
  context.arc(game.projectile.x, game.projectile.y, 12, 0, Math.PI * 2);
  context.fill();
  context.restore();
}

function drawExplosion() {
  if (game.phase !== "resolving" || !game.lastImpact || game.lastImpact.kind === "out") {
    return;
  }

  const progress = Math.min(
    1,
    game.resolutionTime / WORLD.explosionDuration,
  );
  const radius = 12 + Math.sin(progress * Math.PI * 0.84) * 78;
  const alpha = Math.max(0, 1 - progress);
  context.save();
  context.globalAlpha = alpha;
  context.shadowColor = "#ffb45b";
  context.shadowBlur = 26;
  const blast = context.createRadialGradient(
    game.lastImpact.x,
    game.lastImpact.y,
    0,
    game.lastImpact.x,
    game.lastImpact.y,
    radius,
  );
  blast.addColorStop(0, "#ffffff");
  blast.addColorStop(0.16, "#fff0a8");
  blast.addColorStop(0.44, "#ff6f46");
  blast.addColorStop(1, "rgba(255, 55, 98, 0)");
  context.fillStyle = blast;
  context.beginPath();
  context.arc(game.lastImpact.x, game.lastImpact.y, radius, 0, Math.PI * 2);
  context.fill();

  context.globalAlpha = alpha * 0.8;
  context.strokeStyle = "#fff0bd";
  context.lineWidth = 3;
  context.beginPath();
  context.arc(
    game.lastImpact.x,
    game.lastImpact.y,
    20 + progress * 90,
    0,
    Math.PI * 2,
  );
  context.stroke();
  context.restore();
}

function drawParticles() {
  context.save();
  for (const particle of particles) {
    const alpha = Math.max(0, particle.life / particle.maximumLife);
    context.globalAlpha = alpha;
    context.fillStyle = particle.color;
    context.shadowColor = particle.color;
    context.shadowBlur = 8;
    context.beginPath();
    context.arc(
      particle.x,
      particle.y,
      particle.size * Math.max(0.3, alpha),
      0,
      Math.PI * 2,
    );
    context.fill();
  }
  context.restore();
}

function drawPlayfield(now) {
  const scaleX = canvas.width / WORLD.width;
  const scaleY = canvas.height / WORLD.height;
  context.setTransform(scaleX, 0, 0, scaleY, 0, 0);
  context.clearRect(0, 0, WORLD.width, WORLD.height);
  drawBackground(now);
  drawTerrain();
  drawTrajectoryPreview();
  game.tanks.forEach((tank, index) => drawTank(tank, index, now));
  drawTrailAndProjectile();
  drawExplosion();
  drawParticles();

  context.save();
  context.fillStyle = "rgba(139, 194, 210, 0.45)";
  context.font = "600 11px ui-monospace, SFMono-Regular, Menlo, monospace";
  context.letterSpacing = "1px";
  context.fillText("SECTOR 07 // BALLISTIC RANGE", 17, 24);
  context.textAlign = "right";
  context.fillText("LUNAR DUSK  •  GRID 1200", WORLD.width - 17, 24);
  context.restore();
}

function animationFrame(now) {
  const deltaSeconds = Math.min(0.05, Math.max(0, (now - lastFrame) / 1000));
  lastFrame = now;

  if (!modalOpen) {
    game.update(deltaSeconds);
  }
  processGameEvents();
  updateVisuals(deltaSeconds);
  syncHud();
  drawPlayfield(now);
  requestAnimationFrame(animationFrame);
}

modeButtons.forEach((button) => {
  button.addEventListener("click", () => startDuel(button.dataset.mode));
});

newDuelButton.addEventListener("click", () => {
  playUiTick();
  showModeScreen();
});

soundButton.addEventListener("click", () => {
  soundEnabled = !soundEnabled;
  soundButton.setAttribute("aria-pressed", String(soundEnabled));
  soundLabel.textContent = soundEnabled ? "Sound on" : "Sound off";
  soundButton.querySelector(".sound-icon").textContent = soundEnabled ? "◖))" : "◖";
  if (soundEnabled) {
    playTargetLock();
  }
});

angleInput.addEventListener("input", () => applyInputAim(true));
powerInput.addEventListener("input", () => applyInputAim(true));

adjustButtons.forEach((button) => {
  button.addEventListener("click", () => {
    const input = button.dataset.control === "angle" ? angleInput : powerInput;
    input.value = String(Number(input.value) + Number(button.dataset.delta));
    applyInputAim(true);
  });
});

fireButton.addEventListener("click", fireCurrentShot);

window.addEventListener("keydown", (event) => {
  if (!humanCanControl()) {
    return;
  }

  const keyActions = {
    ArrowLeft: [angleInput, -1],
    ArrowRight: [angleInput, 1],
    ArrowDown: [powerInput, -2],
    ArrowUp: [powerInput, 2],
  };

  if (event.code === "Space") {
    event.preventDefault();
    fireCurrentShot();
    return;
  }

  const action = keyActions[event.code];
  if (!action) {
    return;
  }

  event.preventDefault();
  const [input, delta] = action;
  input.value = String(Number(input.value) + delta);
  applyInputAim(true);
});

document.addEventListener("visibilitychange", () => {
  lastFrame = performance.now();
});

new ResizeObserver(resizeCanvas).observe(canvas);
window.addEventListener("resize", resizeCanvas);

setRangeFill(angleInput);
setRangeFill(powerInput);
syncHud();
resizeCanvas();
drawPlayfield(performance.now());
requestAnimationFrame(animationFrame);
