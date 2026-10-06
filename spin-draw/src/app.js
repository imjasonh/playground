import { buildDisc, paperPolylines } from "./rotadraw.js";
import { PICTURES, pictureById } from "./pictures.js";
import { maskFromRgba, strokesFromMask } from "./trace.js";

const STEP_COLORS = ["#1e3a8a", "#9f1239", "#14532d", "#9a3412", "#581c87", "#164e63", "#3f6212", "#7f1d1d"];

const SVG_NS = "http://www.w3.org/2000/svg";

// index.html viewBox is 224 units across. The circle radius is 100,
// so a 190.4 mm SVG prints a 170 mm circle.
const PRINT_WIDTH = "190.4mm";

const discSvg = document.querySelector("#disc");
const paperSvg = document.querySelector("#paper");
const rotor = document.querySelector("#rotor");
const discCaption = document.querySelector("#disc-caption");
const stepStatus = document.querySelector("#step-status");
const lineCount = document.querySelector("#line-count");
const linesInput = document.querySelector("#lines");
const pictureButtons = document.querySelector("#pictures");
const drawPanel = document.querySelector("#draw-panel");
const drawCanvas = document.querySelector("#draw-canvas");
const uploadPanel = document.querySelector("#upload-panel");
const uploadPreview = document.querySelector("#upload-preview");
const thresholdInput = document.querySelector("#threshold");
const thresholdValue = document.querySelector("#threshold-value");
const fileInput = document.querySelector("#file");
const showPicture = document.querySelector("#show-picture");
const prevButton = document.querySelector("#prev");
const nextButton = document.querySelector("#next");
const playButton = document.querySelector("#play");
const downloadButton = document.querySelector("#download");
const emptyNote = document.querySelector("#empty-note");

const reduceMotion = window.matchMedia("(prefers-reduced-motion: reduce)");

let source = "dog";
let customStrokes = null;
let pictureName = "Dog";
let disc = buildDisc(pictureById("dog").strokes, { steps: 16 });
let traced = 0;
let displayTheta = 0;
let playing = false;
let playTimer = 0;
let anim = 0;
let drawing = false;
let drawStrokes = [];
let activeDraw = null;
let uploadImage = null;

function svgEl(name, attrs) {
  const node = document.createElementNS(SVG_NS, name);
  for (const [key, value] of Object.entries(attrs)) {
    node.setAttribute(key, String(value));
  }
  return node;
}

function colorFor(index) {
  return STEP_COLORS[index % STEP_COLORS.length];
}

function pointsAttr(poly) {
  const parts = [];
  for (const point of poly) {
    parts.push(`${point.x.toFixed(2)},${(-point.y).toFixed(2)}`);
  }
  return parts.join(" ");
}

function clear(node) {
  while (node.firstChild) {
    node.removeChild(node.firstChild);
  }
}

function currentIndex() {
  if (disc.steps.length === 0) {
    return 0;
  }
  if (traced >= disc.steps.length) {
    return disc.steps.length - 1;
  }
  return traced;
}

function renderDisc() {
  clear(rotor);
  rotor.appendChild(
    svgEl("circle", {
      r: disc.radius,
      fill: "#fff",
      stroke: "#1c1915",
      "stroke-width": 0.8,
    }),
  );
  rotor.appendChild(
    svgEl("circle", {
      r: disc.hole,
      fill: "none",
      stroke: "#1c1915",
      "stroke-width": 0.7,
    }),
  );
  rotor.appendChild(svgEl("circle", { r: 0.55, fill: "#1c1915" }));
  for (const step of disc.steps) {
    const group = svgEl("g", { class: "step", "data-number": step.number });
    const color = colorFor(step.index);
    for (const poly of step.local) {
      group.appendChild(
        svgEl("polyline", {
          points: pointsAttr(poly),
          fill: "none",
          stroke: color,
          "stroke-width": 1.35,
          "stroke-linecap": "round",
          "stroke-linejoin": "round",
        }),
      );
    }
    const tick = svgEl("line", {
      x1: (96 * Math.cos(step.labelAngle)).toFixed(2),
      y1: (-96 * Math.sin(step.labelAngle)).toFixed(2),
      x2: (disc.radius * Math.cos(step.labelAngle)).toFixed(2),
      y2: (-disc.radius * Math.sin(step.labelAngle)).toFixed(2),
      stroke: color,
      "stroke-width": 0.9,
    });
    group.appendChild(tick);
    const rim = svgEl("text", {
      transform: `translate(${(disc.rim * Math.cos(step.labelAngle)).toFixed(2)} ${(-disc.rim * Math.sin(step.labelAngle)).toFixed(2)}) rotate(${((step.theta * 180) / Math.PI).toFixed(2)})`,
      "text-anchor": "middle",
      "dominant-baseline": "central",
      fill: color,
      "font-size": 4.6,
      "font-family": "ui-sans-serif, system-ui, sans-serif",
      "font-weight": 700,
    });
    rim.textContent = String(step.number);
    group.appendChild(rim);
    const near = svgEl("text", {
      transform: `translate(${step.label.x.toFixed(2)} ${(-step.label.y).toFixed(2)}) rotate(${((step.theta * 180) / Math.PI).toFixed(2)})`,
      "text-anchor": "middle",
      "dominant-baseline": "central",
      fill: color,
      "font-size": 4.2,
      "font-family": "ui-sans-serif, system-ui, sans-serif",
      "font-weight": 700,
    });
    near.textContent = String(step.number);
    group.appendChild(near);
    rotor.appendChild(group);
  }
}

function renderPaper() {
  const layer = paperSvg.querySelector("#ink");
  clear(layer);
  const showAll = showPicture.checked;
  const limit = showAll ? disc.steps.length : traced;
  for (let i = 0; i < limit; i += 1) {
    const done = i < traced;
    for (const poly of paperPolylines(disc.steps[i])) {
      layer.appendChild(
        svgEl("polyline", {
          points: pointsAttr(poly),
          fill: "none",
          stroke: done ? "#1c1915" : "#b7aa9a",
          "stroke-width": 1.45,
          "stroke-linecap": "round",
          "stroke-linejoin": "round",
        }),
      );
    }
  }
}

function applyRotation(theta) {
  displayTheta = theta;
  const deg = (-theta * 180) / Math.PI;
  rotor.setAttribute("transform", `rotate(${deg.toFixed(3)})`);
}

function highlight() {
  const current = currentIndex();
  const groups = rotor.querySelectorAll(".step");
  groups.forEach((group, index) => {
    if (disc.steps.length > 0 && index === current && traced < disc.steps.length) {
      group.classList.add("is-current");
    } else {
      group.classList.remove("is-current");
    }
  });
  const total = disc.steps.length;
  const shown = total === 0 ? 0 : Math.min(traced + 1, total);
  if (total === 0) {
    stepStatus.textContent = "No lines";
  } else if (traced >= total) {
    stepStatus.textContent = `${total} of ${total}`;
  } else {
    stepStatus.textContent = `Line ${shown} of ${total}`;
  }
  lineCount.textContent = String(total);
  discCaption.textContent = pictureName;
  discSvg.setAttribute(
    "aria-label",
    total === 0 ? `${pictureName} disc` : `${pictureName} disc, line ${shown} of ${total}`,
  );
  paperSvg.setAttribute(
    "aria-label",
    traced === 0 ? "Nothing traced yet" : `${Math.min(traced, total)} lines traced`,
  );
  prevButton.disabled = traced === 0;
  nextButton.disabled = total === 0 || traced >= total;
  playButton.disabled = total === 0;
  emptyNote.hidden = total > 0;
  if (source === "draw") {
    emptyNote.textContent = "Draw a line and it shows up on the disc.";
  } else if (source === "upload") {
    emptyNote.textContent = "No dark lines in this picture. Move Threshold.";
  }
}

function jumpTo(theta) {
  cancelAnimationFrame(anim);
  applyRotation(theta);
  highlight();
  renderPaper();
}

function animateTo(theta, done) {
  cancelAnimationFrame(anim);
  if (reduceMotion.matches) {
    applyRotation(theta);
    done();
    return;
  }
  const from = displayTheta;
  const start = performance.now();
  const duration = 420;
  function frame(now) {
    const t = Math.min(1, (now - start) / duration);
    const eased = t < 0.5 ? 2 * t * t : 1 - (-2 * t + 2) ** 2 / 2;
    applyRotation(from + (theta - from) * eased);
    if (t < 1) {
      anim = requestAnimationFrame(frame);
    } else {
      done();
    }
  }
  anim = requestAnimationFrame(frame);
}

function unwrapForward(theta) {
  let target = theta;
  while (target < displayTheta - 1e-4) {
    target += Math.PI * 2;
  }
  return target;
}

function unwrapBack(theta) {
  let target = theta;
  while (target > displayTheta + 1e-4) {
    target -= Math.PI * 2;
  }
  return target;
}

function stopPlay() {
  playing = false;
  window.clearTimeout(playTimer);
  playButton.textContent = "Play";
  playButton.setAttribute("aria-pressed", "false");
}

function finishPlayStep() {
  if (!playing) {
    return;
  }
  if (traced >= disc.steps.length) {
    stopPlay();
    return;
  }
  traced += 1;
  const nextIndex = Math.min(traced, disc.steps.length - 1);
  const more = traced < disc.steps.length;
  renderPaper();
  highlight();
  animateTo(unwrapForward(disc.steps[nextIndex].theta), () => {
    if (!playing) {
      return;
    }
    if (!more) {
      stopPlay();
      return;
    }
    playTimer = window.setTimeout(finishPlayStep, 260);
  });
}

function play() {
  if (playing) {
    stopPlay();
    return;
  }
  if (disc.steps.length === 0) {
    return;
  }
  if (traced >= disc.steps.length) {
    traced = 0;
    jumpTo(0);
  }
  playing = true;
  playButton.textContent = "Stop";
  playButton.setAttribute("aria-pressed", "true");
  finishPlayStep();
}

function goNext() {
  stopPlay();
  if (disc.steps.length === 0 || traced >= disc.steps.length) {
    return;
  }
  traced += 1;
  renderPaper();
  highlight();
  const index = Math.min(traced, disc.steps.length - 1);
  animateTo(unwrapForward(disc.steps[index].theta), () => {});
}

function goPrev() {
  stopPlay();
  if (traced <= 0) {
    return;
  }
  traced -= 1;
  renderPaper();
  highlight();
  animateTo(unwrapBack(disc.steps[traced].theta), () => {});
}

function strokesForSource() {
  if (source === "draw") {
    return drawStrokes;
  }
  if (source === "upload") {
    return customStrokes || [];
  }
  return pictureById(source).strokes;
}

function nameForSource() {
  if (source === "draw") {
    return "Drawing";
  }
  if (source === "upload") {
    return "Upload";
  }
  return pictureById(source).name;
}

function rebuild() {
  stopPlay();
  cancelAnimationFrame(anim);
  pictureName = nameForSource();
  disc = buildDisc(strokesForSource(), { steps: Number(linesInput.value) });
  traced = 0;
  displayTheta = 0;
  renderDisc();
  jumpTo(0);
  for (const button of pictureButtons.querySelectorAll("button")) {
    button.setAttribute("aria-pressed", button.dataset.picture === source ? "true" : "false");
  }
  drawPanel.hidden = source !== "draw";
  uploadPanel.hidden = source !== "upload";
  document.querySelector("#draw").setAttribute("aria-pressed", source === "draw" ? "true" : "false");
  document.querySelector("#upload-label").classList.toggle("is-selected", source === "upload");
}

function selectPicture(id) {
  source = id;
  rebuild();
}

function flipY(strokes, height) {
  return strokes.map((stroke) =>
    stroke.map((point) => ({
      x: point.x,
      y: height - point.y,
    })),
  );
}

function canvasPoint(event, canvas) {
  const rect = canvas.getBoundingClientRect();
  return {
    x: ((event.clientX - rect.left) / rect.width) * canvas.width,
    y: ((event.clientY - rect.top) / rect.height) * canvas.height,
  };
}

function paintDraw() {
  const ctx = drawCanvas.getContext("2d");
  ctx.clearRect(0, 0, drawCanvas.width, drawCanvas.height);
  ctx.lineWidth = 4;
  ctx.lineCap = "round";
  ctx.lineJoin = "round";
  ctx.strokeStyle = "#1c1915";
  const all = activeDraw ? drawStrokes.concat([activeDraw]) : drawStrokes;
  for (const stroke of all) {
    if (stroke.length < 2) {
      continue;
    }
    ctx.beginPath();
    ctx.moveTo(stroke[0].x, stroke[0].y);
    for (let i = 1; i < stroke.length; i += 1) {
      ctx.lineTo(stroke[i].x, stroke[i].y);
    }
    ctx.stroke();
  }
}

function commitDrawing() {
  source = "draw";
  rebuild();
}

function sampleUpload() {
  if (!uploadImage) {
    return;
  }
  const maxSide = 180;
  const scale = maxSide / Math.max(uploadImage.width, uploadImage.height);
  const width = Math.max(2, Math.round(uploadImage.width * scale));
  const height = Math.max(2, Math.round(uploadImage.height * scale));
  uploadPreview.width = width;
  uploadPreview.height = height;
  const ctx = uploadPreview.getContext("2d", { willReadFrequently: true });
  ctx.fillStyle = "#fff";
  ctx.fillRect(0, 0, width, height);
  ctx.drawImage(uploadImage, 0, 0, width, height);
  const pixels = ctx.getImageData(0, 0, width, height);
  const mask = maskFromRgba(pixels.data, width, height, Number(thresholdInput.value));
  const raw = strokesFromMask(mask, width, height);
  customStrokes = flipY(raw, height);
  ctx.strokeStyle = "#9f1239";
  ctx.lineWidth = 1.5;
  for (const stroke of raw) {
    ctx.beginPath();
    ctx.moveTo(stroke[0].x, stroke[0].y);
    for (let i = 1; i < stroke.length; i += 1) {
      ctx.lineTo(stroke[i].x, stroke[i].y);
    }
    ctx.stroke();
  }
  source = "upload";
  rebuild();
}

function downloadSvg() {
  const clone = discSvg.cloneNode(true);
  clone.setAttribute("xmlns", SVG_NS);
  const mark = clone.querySelector(".mark");
  if (mark) {
    mark.remove();
  }
  clone.querySelector("#rotor").setAttribute("transform", "rotate(0)");
  clone.setAttribute("width", PRINT_WIDTH);
  clone.setAttribute("height", PRINT_WIDTH);
  const text = new XMLSerializer().serializeToString(clone);
  const blob = new Blob([text], { type: "image/svg+xml" });
  const url = URL.createObjectURL(blob);
  const link = document.createElement("a");
  link.href = url;
  link.download = `${pictureName.toLowerCase().replaceAll(" ", "-")}-spin-draw.svg`;
  link.click();
  URL.revokeObjectURL(url);
}

for (const picture of PICTURES) {
  const button = document.createElement("button");
  button.type = "button";
  button.textContent = picture.name;
  button.dataset.picture = picture.id;
  button.setAttribute("aria-pressed", picture.id === "dog" ? "true" : "false");
  button.addEventListener("click", () => {
    selectPicture(picture.id);
  });
  pictureButtons.appendChild(button);
}

document.querySelector("#draw").addEventListener("click", () => {
  source = "draw";
  rebuild();
});

document.querySelector("#clear-draw").addEventListener("click", () => {
  drawStrokes = [];
  activeDraw = null;
  paintDraw();
  if (source === "draw") {
    rebuild();
  }
});

linesInput.addEventListener("input", () => {
  rebuild();
});

showPicture.addEventListener("change", () => {
  renderPaper();
});

prevButton.addEventListener("click", goPrev);
nextButton.addEventListener("click", goNext);
playButton.addEventListener("click", play);
downloadButton.addEventListener("click", downloadSvg);

document.querySelector("#print").addEventListener("click", () => {
  stopPlay();
  window.print();
});

window.addEventListener("beforeprint", () => {
  rotor.setAttribute("transform", "rotate(0)");
  discSvg.classList.add("is-flat");
});

window.addEventListener("afterprint", () => {
  discSvg.classList.remove("is-flat");
  applyRotation(displayTheta);
});

window.addEventListener("keydown", (event) => {
  const tag = event.target.tagName;
  if (tag === "INPUT" || tag === "TEXTAREA") {
    return;
  }
  if (event.key === "ArrowRight") {
    event.preventDefault();
    goNext();
  } else if (event.key === "ArrowLeft") {
    event.preventDefault();
    goPrev();
  }
});

drawCanvas.addEventListener("pointerdown", (event) => {
  drawing = true;
  drawCanvas.setPointerCapture(event.pointerId);
  activeDraw = [canvasPoint(event, drawCanvas)];
  paintDraw();
});

drawCanvas.addEventListener("pointermove", (event) => {
  if (!drawing || !activeDraw) {
    return;
  }
  activeDraw.push(canvasPoint(event, drawCanvas));
  paintDraw();
});

function endDraw() {
  if (!drawing) {
    return;
  }
  drawing = false;
  if (activeDraw && activeDraw.length >= 2) {
    drawStrokes.push(activeDraw);
  }
  activeDraw = null;
  paintDraw();
  commitDrawing();
}

drawCanvas.addEventListener("pointerup", endDraw);
drawCanvas.addEventListener("pointercancel", endDraw);

fileInput.addEventListener("change", () => {
  const file = fileInput.files && fileInput.files[0];
  if (!file) {
    return;
  }
  const url = URL.createObjectURL(file);
  const image = new Image();
  image.addEventListener("load", () => {
    URL.revokeObjectURL(url);
    uploadImage = image;
    thresholdValue.textContent = thresholdInput.value;
    sampleUpload();
  });
  image.addEventListener("error", () => {
    URL.revokeObjectURL(url);
    stepStatus.textContent = "That file could not be read as an image.";
  });
  image.src = url;
});

thresholdInput.addEventListener("input", () => {
  thresholdValue.textContent = thresholdInput.value;
  if (uploadImage) {
    sampleUpload();
  }
});

rebuild();
paintDraw();
