import {
  castLayers,
  castTransform,
  gnomonShadow,
  pageBackground,
  parseLocation,
  parsePinnedTime,
  rgbCss,
  rgbToHex,
  sceneFromSun,
  sunPosition,
} from "./solar.js";

const clockEl = document.getElementById("clock");
const timeEl = document.getElementById("time");
const periodEl = document.getElementById("period");
const dateEl = document.getElementById("date");
const hintEl = document.getElementById("hint");
const nowBtn = document.getElementById("now");
const northEl = document.getElementById("north");
const themeColorMeta = document.getElementById("theme-color");
const castEls = clockEl.querySelectorAll("[data-cast]");

const timeFormat = new Intl.DateTimeFormat(undefined, {
  hour: "numeric",
  minute: "2-digit",
});
const dateFormat = new Intl.DateTimeFormat(undefined, {
  weekday: "long",
  month: "long",
  day: "numeric",
});

const motionQuery = window.matchMedia("(prefers-reduced-motion: reduce)");

let scrubMs = 0;
let live = true;
let dragging = false;
let dragOriginX = 0;
let dragOriginScrub = 0;
let moved = false;
let frameId = 0;

const pinned = parsePinnedTime(window.location.search);
if (pinned) {
  live = false;
  scrubMs = pinned.getTime() - Date.now();
}

function hoursPerWidth() {
  if (window.innerWidth < 600) {
    return 16;
  }
  return 24;
}

function shownDate() {
  return new Date(Date.now() + scrubMs);
}

function formatClock(date) {
  const parts = timeFormat.formatToParts(date);
  let hour = "";
  let minute = "";
  let dayPeriod = "";
  for (const part of parts) {
    if (part.type === "hour") {
      hour = part.value;
    } else if (part.type === "minute") {
      minute = part.value;
    } else if (part.type === "dayPeriod") {
      dayPeriod = part.value;
    }
  }
  return {
    time: `${hour}:${minute}`,
    period: dayPeriod,
    spoken: timeFormat.format(date),
  };
}

function writePeriod(el, period) {
  el.textContent = period;
  el.hidden = !period;
}

function writeClockText(clock) {
  timeEl.textContent = clock.time;
  writePeriod(periodEl, clock.period);
  for (const castEl of castEls) {
    castEl.querySelector("[data-time]").textContent = clock.time;
    writePeriod(castEl.querySelector("[data-period]"), clock.period);
  }
}

function clearCast(castEl) {
  castEl.style.transform = "none";
  castEl.style.filter = "none";
  castEl.style.opacity = "0";
}

function paintCast(castEl, layer, color) {
  castEl.style.color = rgbCss(color);
  castEl.style.opacity = String(layer.opacity);
  castEl.style.filter = `blur(${layer.blur.toFixed(2)}px)`;
  castEl.style.transform = castTransform(layer);
}

function maxShadowLength() {
  return Math.min(window.innerWidth, window.innerHeight) * 0.48;
}

function render() {
  const date = shownDate();
  const { latitude, longitude } = parseLocation(window.location.search, date);
  const sun = sunPosition(date, latitude, longitude);
  const scene = sceneFromSun(sun);
  const shadow = gnomonShadow(sun, maxShadowLength());
  const clock = formatClock(date);
  const layers = castLayers(shadow, scene.shadow);

  writeClockText(clock);
  clockEl.setAttribute("aria-label", clock.spoken);
  dateEl.textContent = dateFormat.format(date);

  const ink = rgbCss(scene.ink);
  document.body.style.background = pageBackground(scene);
  document.body.style.color = ink;
  document.documentElement.style.colorScheme = scene.colorScheme;
  clockEl.classList.toggle("is-night", scene.night);

  for (let i = 0; i < castEls.length; i += 1) {
    const layer = layers[i];
    if (layer) {
      paintCast(castEls[i], layer, scene.shadow);
    } else {
      clearCast(castEls[i]);
    }
  }

  if (themeColorMeta) {
    themeColorMeta.setAttribute("content", rgbToHex(scene.paper));
  }

  if (live) {
    nowBtn.hidden = true;
    hintEl.hidden = false;
  } else {
    nowBtn.hidden = false;
    hintEl.hidden = true;
  }

  if (scene.night) {
    northEl.dataset.phase = "night";
  } else {
    northEl.dataset.phase = "day";
  }
}

function setLive() {
  live = true;
  scrubMs = 0;
  render();
}

function setScrub(nextMs) {
  live = false;
  scrubMs = nextMs;
  render();
}

function onPointerDown(event) {
  if (event.target === nowBtn) {
    return;
  }
  if (event.pointerType === "mouse" && event.button !== 0) {
    return;
  }
  dragging = true;
  moved = false;
  dragOriginX = event.clientX;
  dragOriginScrub = scrubMs;
  document.body.setPointerCapture(event.pointerId);
}

function onPointerMove(event) {
  if (!dragging) {
    return;
  }
  const deltaX = event.clientX - dragOriginX;
  if (Math.abs(deltaX) > 8) {
    moved = true;
  }
  if (!moved) {
    return;
  }
  const dayMs = hoursPerWidth() * 60 * 60 * 1000;
  const next = dragOriginScrub + (deltaX / window.innerWidth) * dayMs;
  setScrub(next);
}

function onPointerUp(event) {
  if (!dragging) {
    return;
  }
  dragging = false;
  if (document.body.hasPointerCapture(event.pointerId)) {
    document.body.releasePointerCapture(event.pointerId);
  }
}

function onKeyDown(event) {
  if (event.key === "Escape" || event.key === "Home") {
    event.preventDefault();
    setLive();
    return;
  }

  let stepMin = 0;
  if (event.key === "ArrowLeft") {
    stepMin = -15;
  } else if (event.key === "ArrowRight") {
    stepMin = 15;
  } else {
    return;
  }

  event.preventDefault();
  if (event.shiftKey) {
    stepMin *= 4;
  }
  setScrub(scrubMs + stepMin * 60 * 1000);
}

nowBtn.addEventListener("click", setLive);
document.body.addEventListener("pointerdown", onPointerDown);
document.body.addEventListener("pointermove", onPointerMove);
document.body.addEventListener("pointerup", onPointerUp);
document.body.addEventListener("pointercancel", onPointerUp);
document.addEventListener("keydown", onKeyDown);

function tick() {
  if (live || dragging || !motionQuery.matches) {
    render();
  }
  frameId = window.requestAnimationFrame(tick);
}

render();
frameId = window.requestAnimationFrame(tick);

window.addEventListener("pagehide", function stop() {
  window.cancelAnimationFrame(frameId);
});
