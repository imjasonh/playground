import {
  DISPLAYS,
  getDisplay,
  getPalette,
  getResponse,
  displayCategories,
} from "./displays.js";
import {
  DITHER_METHODS,
  renderPipeline,
  paletteColorCount,
} from "./dither.js";
import { rgbToHex } from "./color.js";

const DITHER_LABELS = {
  none: "None (nearest color)",
  "floyd-steinberg": "Floyd–Steinberg",
  atkinson: "Atkinson",
  "jarvis-judice-ninke": "Jarvis–Judice–Ninke",
  stucki: "Stucki",
  sierra: "Sierra",
  "sierra-lite": "Sierra Lite",
  "bayer-2": "Ordered 2×2 (Bayer)",
  "bayer-4": "Ordered 4×4 (Bayer)",
  "bayer-8": "Ordered 8×8 (Bayer)",
};

const els = {
  displaySelect: document.querySelector("#display-select"),
  displayInfo: document.querySelector("#display-info"),
  dropZone: document.querySelector("#drop-zone"),
  fileInput: document.querySelector("#file-input"),
  sampleRow: document.querySelector("#sample-row"),
  ditherSelect: document.querySelector("#dither-select"),
  serpentine: document.querySelector("#serpentine"),
  fitSelect: document.querySelector("#fit-select"),
  rotate: document.querySelector("#rotate"),
  autoBoost: document.querySelector("#auto-boost"),
  resetAdjust: document.querySelector("#reset-adjust"),
  realism: document.querySelector("#realism"),
  paperTexture: document.querySelector("#paper-texture"),
  showGrid: document.querySelector("#show-grid"),
  zoomSelect: document.querySelector("#zoom-select"),
  stageTitle: document.querySelector("#stage-title"),
  compare: document.querySelector("#compare"),
  download: document.querySelector("#download"),
  viewport: document.querySelector("#viewport"),
  device: document.querySelector("#device"),
  viewCanvas: document.querySelector("#view-canvas"),
  emptyHint: document.querySelector("#empty-hint"),
  sourceCanvas: document.querySelector("#source-canvas"),
  renderCaption: document.querySelector("#render-caption"),
};

const state = {
  source: null, // HTMLImageElement or HTMLCanvasElement
  display: DISPLAYS[0],
  adjust: { saturation: 1, contrast: 1, brightness: 1, gamma: 1 },
  showOriginal: false,
  // Offscreen native-resolution panel canvas holding the processed pixels.
  panelCanvas: document.createElement("canvas"),
};

// ---------------------------------------------------------------------------
// Setup: populate selects
// ---------------------------------------------------------------------------

function populateDisplays() {
  for (const category of displayCategories()) {
    const group = document.createElement("optgroup");
    group.label = category;
    for (const d of DISPLAYS.filter((x) => x.category === category)) {
      const opt = document.createElement("option");
      opt.value = d.id;
      opt.textContent = d.name;
      group.appendChild(opt);
    }
    els.displaySelect.appendChild(group);
  }
  els.displaySelect.value = state.display.id;
}

function populateDither() {
  for (const method of DITHER_METHODS) {
    const opt = document.createElement("option");
    opt.value = method;
    opt.textContent = DITHER_LABELS[method] ?? method;
    els.ditherSelect.appendChild(opt);
  }
  els.ditherSelect.value = "floyd-steinberg";
}

// ---------------------------------------------------------------------------
// Panel geometry
// ---------------------------------------------------------------------------

function panelDimensions() {
  const d = state.display;
  return els.rotate.checked
    ? { width: d.height, height: d.width }
    : { width: d.width, height: d.height };
}

// ---------------------------------------------------------------------------
// Display info panel
// ---------------------------------------------------------------------------

function paletteSummary(display) {
  const palette = getPalette(display);
  const count = paletteColorCount(palette);
  if (palette.kind === "list") {
    return `${count} inks`;
  }
  if (palette.grayscale) {
    return `${count} gray levels`;
  }
  return `${count.toLocaleString()} colors`;
}

function swatchesFor(display) {
  const palette = getPalette(display);
  const response = getResponse(display);
  let colors;
  if (palette.kind === "list") {
    colors = palette.colors;
  } else if (palette.grayscale) {
    const n = Math.min(palette.levels, 16);
    colors = Array.from({ length: n }, (_, i) => {
      const v = Math.round((i / (n - 1)) * 255);
      return [v, v, v];
    });
  } else {
    colors = [
      [0, 0, 0],
      [255, 0, 0],
      [255, 255, 0],
      [0, 255, 0],
      [0, 255, 255],
      [0, 0, 255],
      [255, 0, 255],
      [255, 255, 255],
    ];
  }
  // Render swatches through the (muted) panel response so they match output.
  return colors.map((c) => {
    if (!els.realism.checked) return rgbToHex(c[0], c[1], c[2]);
    const l = 0.2126 * c[0] + 0.7152 * c[1] + 0.0722 * c[2];
    const sat = response.saturation;
    const rr = l + (c[0] - l) * sat;
    const gg = l + (c[1] - l) * sat;
    const bb = l + (c[2] - l) * sat;
    const map = (v, w, b) => b + ((w - b) * v) / 255;
    return rgbToHex(
      map(rr, response.white[0], response.black[0]),
      map(gg, response.white[1], response.black[1]),
      map(bb, response.white[2], response.black[2]),
    );
  });
}

function updateDisplayInfo() {
  const d = state.display;
  const { width, height } = panelDimensions();
  const wMm = (width / d.ppi) * 25.4;
  const hMm = (height / d.ppi) * 25.4;
  const rows = [
    ["Panel", `${d.inches}″ · ${d.category}`],
    ["Resolution", `${width} × ${height} px`],
    [
      "Density",
      d.colorPpi
        ? `${d.ppi} ppi mono · ${d.colorPpi} ppi color`
        : `${d.ppi} ppi`,
    ],
    ["Active area", `${wMm.toFixed(0)} × ${hMm.toFixed(0)} mm`],
    ["Palette", paletteSummary(d)],
    ["Refresh", d.refresh],
  ];
  els.displayInfo.innerHTML = "";
  for (const [k, v] of rows) {
    const key = document.createElement("dt");
    key.textContent = k;
    const val = document.createElement("dd");
    val.textContent = v;
    els.displayInfo.append(key, val);
  }
  const swatchWrap = document.createElement("div");
  swatchWrap.className = "swatches";
  for (const hex of swatchesFor(d)) {
    const sw = document.createElement("span");
    sw.className = "swatch";
    sw.style.background = hex;
    sw.title = hex;
    swatchWrap.appendChild(sw);
  }
  const key = document.createElement("dt");
  key.textContent = "Colors";
  const val = document.createElement("dd");
  val.appendChild(swatchWrap);
  els.displayInfo.append(key, val);

  els.stageTitle.textContent = `${d.name} — ${width} × ${height}`;
}

// ---------------------------------------------------------------------------
// Image loading
// ---------------------------------------------------------------------------

function loadImageFromDataURL(url) {
  const img = new Image();
  img.onload = () => {
    state.source = img;
    render();
  };
  img.src = url;
}

function handleFile(file) {
  if (!file || !file.type.startsWith("image/")) return;
  const reader = new FileReader();
  reader.onload = () => loadImageFromDataURL(reader.result);
  reader.readAsDataURL(file);
}

// ---------------------------------------------------------------------------
// Sample / test-pattern generators
// ---------------------------------------------------------------------------

function makeSample(kind) {
  const c = document.createElement("canvas");
  c.width = 1024;
  c.height = 768;
  const ctx = c.getContext("2d");

  if (kind === "bars") {
    const bars = [
      "#ffffff",
      "#ffff00",
      "#00ffff",
      "#00ff00",
      "#ff00ff",
      "#ff0000",
      "#0000ff",
      "#000000",
    ];
    const bw = c.width / bars.length;
    bars.forEach((color, i) => {
      ctx.fillStyle = color;
      ctx.fillRect(i * bw, 0, bw + 1, c.height * 0.7);
    });
    const grad = ctx.createLinearGradient(0, 0, c.width, 0);
    grad.addColorStop(0, "#000");
    grad.addColorStop(1, "#fff");
    ctx.fillStyle = grad;
    ctx.fillRect(0, c.height * 0.7, c.width, c.height * 0.3);
  } else if (kind === "wheel") {
    ctx.fillStyle = "#ffffff";
    ctx.fillRect(0, 0, c.width, c.height);
    const cx = c.width / 2;
    const cy = c.height / 2;
    const radius = Math.min(cx, cy) - 20;
    const img = ctx.createImageData(c.width, c.height);
    for (let y = 0; y < c.height; y++) {
      for (let x = 0; x < c.width; x++) {
        const dx = x - cx;
        const dy = y - cy;
        const dist = Math.hypot(dx, dy);
        const i = (y * c.width + x) * 4;
        if (dist <= radius) {
          const hue = ((Math.atan2(dy, dx) * 180) / Math.PI + 360) % 360;
          const sat = dist / radius;
          const [r, g, b] = hslToRgb(hue / 360, sat, 0.5);
          img.data[i] = r;
          img.data[i + 1] = g;
          img.data[i + 2] = b;
          img.data[i + 3] = 255;
        } else {
          img.data[i] = 255;
          img.data[i + 1] = 255;
          img.data[i + 2] = 255;
          img.data[i + 3] = 255;
        }
      }
    }
    ctx.putImageData(img, 0, 0);
  } else if (kind === "gradient") {
    const img = ctx.createImageData(c.width, c.height);
    for (let y = 0; y < c.height; y++) {
      for (let x = 0; x < c.width; x++) {
        const i = (y * c.width + x) * 4;
        const hue = x / c.width;
        const light = 1 - y / c.height;
        const [r, g, b] = hslToRgb(hue, 0.9, light * 0.85 + 0.08);
        img.data[i] = r;
        img.data[i + 1] = g;
        img.data[i + 2] = b;
        img.data[i + 3] = 255;
      }
    }
    ctx.putImageData(img, 0, 0);
  } else if (kind === "text") {
    ctx.fillStyle = "#f4f2ea";
    ctx.fillRect(0, 0, c.width, c.height);
    ctx.fillStyle = "#161616";
    ctx.font = "bold 44px Georgia, serif";
    ctx.fillText("The Quick Brown Fox", 60, 90);
    ctx.font = "20px Georgia, serif";
    const lines = [
      "E-ink displays are reflective: they use ambient light instead of a",
      "backlight, so text stays crisp in sunlight and sips power. This test",
      "page checks how legible fine type stays after quantization and",
      "dithering. Grayscale panels reproduce this well; color panels trade",
      "resolution for a limited palette of pigment inks.",
    ];
    lines.forEach((line, i) => ctx.fillText(line, 60, 150 + i * 34));
    ctx.fillStyle = "#b02a2a";
    ctx.fillRect(60, 360, 380, 60);
    ctx.fillStyle = "#fff";
    ctx.font = "bold 30px Georgia, serif";
    ctx.fillText("SALE  $3.99", 90, 400);
    for (let i = 0; i < 6; i++) {
      ctx.fillStyle = hslToCss((i / 6) * 360, 70, 45);
      ctx.fillRect(60 + i * 150, 460, 130, 130);
    }
  } else {
    // "photo": a synthetic landscape with sky, sun, hills, water — lots of
    // gradients and skin/earth tones to stress the palette + dithering.
    drawSyntheticPhoto(ctx, c.width, c.height);
  }
  return c;
}

function drawSyntheticPhoto(ctx, w, h) {
  const sky = ctx.createLinearGradient(0, 0, 0, h * 0.6);
  sky.addColorStop(0, "#2a5b9c");
  sky.addColorStop(0.6, "#8fb6d6");
  sky.addColorStop(1, "#f3c98b");
  ctx.fillStyle = sky;
  ctx.fillRect(0, 0, w, h * 0.62);

  // sun
  const sun = ctx.createRadialGradient(
    w * 0.72,
    h * 0.24,
    5,
    w * 0.72,
    h * 0.24,
    120,
  );
  sun.addColorStop(0, "#fff6dc");
  sun.addColorStop(0.5, "#ffd27a");
  sun.addColorStop(1, "rgba(255,210,122,0)");
  ctx.fillStyle = sun;
  ctx.fillRect(0, 0, w, h * 0.62);

  // distant hills
  ctx.fillStyle = "#6f7f5a";
  hill(ctx, w, h * 0.55, h * 0.12, 3);
  ctx.fillStyle = "#566a45";
  hill(ctx, w, h * 0.6, h * 0.16, 5);

  // water
  const water = ctx.createLinearGradient(0, h * 0.62, 0, h);
  water.addColorStop(0, "#c98f5a");
  water.addColorStop(0.3, "#5b7fa6");
  water.addColorStop(1, "#25415f");
  ctx.fillStyle = water;
  ctx.fillRect(0, h * 0.62, w, h * 0.38);

  // sun reflection shimmer
  ctx.fillStyle = "rgba(255, 220, 150, 0.35)";
  for (let y = h * 0.64; y < h; y += 10) {
    const ww = 90 + Math.random() * 60;
    ctx.fillRect(w * 0.72 - ww / 2, y, ww, 4);
  }

  // foreground rock (earthy tones)
  ctx.fillStyle = "#3a2f26";
  ctx.beginPath();
  ctx.moveTo(0, h);
  ctx.lineTo(0, h * 0.82);
  ctx.quadraticCurveTo(w * 0.2, h * 0.72, w * 0.42, h * 0.9);
  ctx.lineTo(w * 0.42, h);
  ctx.closePath();
  ctx.fill();
}

function hill(ctx, w, baseY, amp, bumps) {
  ctx.beginPath();
  ctx.moveTo(0, baseY);
  for (let x = 0; x <= w; x += 8) {
    const y = baseY - Math.sin((x / w) * Math.PI * bumps) * amp * 0.5 - amp * 0.2;
    ctx.lineTo(x, y);
  }
  ctx.lineTo(w, ctx.canvas.height);
  ctx.lineTo(0, ctx.canvas.height);
  ctx.closePath();
  ctx.fill();
}

function hslToRgb(h, s, l) {
  let r, g, b;
  if (s === 0) {
    r = g = b = l;
  } else {
    const hue2rgb = (p, q, t) => {
      if (t < 0) t += 1;
      if (t > 1) t -= 1;
      if (t < 1 / 6) return p + (q - p) * 6 * t;
      if (t < 1 / 2) return q;
      if (t < 2 / 3) return p + (q - p) * (2 / 3 - t) * 6;
      return p;
    };
    const q = l < 0.5 ? l * (1 + s) : l + s - l * s;
    const p = 2 * l - q;
    r = hue2rgb(p, q, h + 1 / 3);
    g = hue2rgb(p, q, h);
    b = hue2rgb(p, q, h - 1 / 3);
  }
  return [Math.round(r * 255), Math.round(g * 255), Math.round(b * 255)];
}

function hslToCss(h, s, l) {
  return `hsl(${h}, ${s}%, ${l}%)`;
}

// ---------------------------------------------------------------------------
// Core render pipeline
// ---------------------------------------------------------------------------

function fitSourceToPanel(width, height) {
  const canvas = document.createElement("canvas");
  canvas.width = width;
  canvas.height = height;
  const ctx = canvas.getContext("2d");
  ctx.imageSmoothingEnabled = true;
  ctx.imageSmoothingQuality = "high";
  // Paper-white background for letterboxing.
  ctx.fillStyle = "#ffffff";
  ctx.fillRect(0, 0, width, height);

  const src = state.source;
  const sw = src.width || src.naturalWidth;
  const sh = src.height || src.naturalHeight;
  const fit = els.fitSelect.value;

  if (fit === "stretch") {
    ctx.drawImage(src, 0, 0, width, height);
  } else {
    const scale =
      fit === "cover"
        ? Math.max(width / sw, height / sh)
        : Math.min(width / sw, height / sh);
    const dw = sw * scale;
    const dh = sh * scale;
    ctx.drawImage(src, (width - dw) / 2, (height - dh) / 2, dw, dh);
  }
  return { canvas, ctx };
}

let renderQueued = false;
function scheduleRender() {
  if (renderQueued) return;
  renderQueued = true;
  requestAnimationFrame(() => {
    renderQueued = false;
    render();
  });
}

function render() {
  updateDisplayInfo();
  if (!state.source) {
    els.emptyHint.hidden = false;
    els.viewCanvas.style.display = "none";
    els.download.disabled = true;
    return;
  }
  els.emptyHint.hidden = true;
  els.viewCanvas.style.display = "block";
  els.download.disabled = false;

  const { width, height } = panelDimensions();
  const { canvas: fitCanvas, ctx: fitCtx } = fitSourceToPanel(width, height);

  // Source preview (fitted, pre-processing).
  els.sourceCanvas.width = width;
  els.sourceCanvas.height = height;
  els.sourceCanvas.getContext("2d").drawImage(fitCanvas, 0, 0);

  const srcData = fitCtx.getImageData(0, 0, width, height);
  const display = state.display;
  const palette = getPalette(display);
  const response = getResponse(display);

  const processed = renderPipeline(srcData, palette, {
    adjust: state.adjust,
    dither: {
      method: els.ditherSelect.value,
      serpentine: els.serpentine.checked,
    },
    response,
    realism: els.realism.checked,
  });

  // Draw native pixels onto the offscreen panel canvas.
  const panel = state.panelCanvas;
  panel.width = width;
  panel.height = height;
  const panelCtx = panel.getContext("2d");
  const out = new ImageData(processed.data, width, height);
  panelCtx.putImageData(out, 0, 0);

  drawToView(width, height, response);
  updateRenderCaption(width, height, palette);
}

function computeScale(width, height) {
  const zoom = els.zoomSelect.value;
  if (zoom !== "fit") return Number(zoom);
  const rect = els.viewport.getBoundingClientRect();
  const maxW = Math.max(240, rect.width - 48);
  const maxH = Math.max(240, rect.height - 48);
  return Math.min(maxW / width, maxH / height);
}

function drawToView(width, height, response) {
  const scale = computeScale(width, height);
  const view = els.viewCanvas;
  const dpr = window.devicePixelRatio || 1;
  const cssW = Math.round(width * scale);
  const cssH = Math.round(height * scale);
  view.style.width = `${cssW}px`;
  view.style.height = `${cssH}px`;
  view.width = Math.round(cssW * dpr);
  view.height = Math.round(cssH * dpr);

  const ctx = view.getContext("2d");
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.imageSmoothingEnabled = false;
  ctx.clearRect(0, 0, cssW, cssH);

  const sourceCanvas = state.showOriginal ? els.sourceCanvas : state.panelCanvas;
  ctx.drawImage(sourceCanvas, 0, 0, cssW, cssH);

  // Bezel tint reflects the substrate color.
  els.device.style.setProperty(
    "--substrate",
    els.realism.checked
      ? rgbToHex(response.white[0], response.white[1], response.white[2])
      : "#ffffff",
  );

  if (els.paperTexture.checked && els.realism.checked && !state.showOriginal) {
    applyPaperTexture(ctx, cssW, cssH);
  }

  const effectiveScale = cssW / width;
  if (els.showGrid.checked && effectiveScale >= 5 && !state.showOriginal) {
    drawGrid(ctx, width, height, effectiveScale);
  }
}

let textureCanvas = null;
function getTexture() {
  if (textureCanvas) return textureCanvas;
  const size = 160;
  textureCanvas = document.createElement("canvas");
  textureCanvas.width = size;
  textureCanvas.height = size;
  const tctx = textureCanvas.getContext("2d");
  const img = tctx.createImageData(size, size);
  for (let i = 0; i < img.data.length; i += 4) {
    const n = 128 + (Math.random() - 0.5) * 46;
    img.data[i] = n;
    img.data[i + 1] = n;
    img.data[i + 2] = n;
    img.data[i + 3] = 255;
  }
  tctx.putImageData(img, 0, 0);
  return textureCanvas;
}

function applyPaperTexture(ctx, w, h) {
  const tex = getTexture();
  ctx.save();
  ctx.globalCompositeOperation = "overlay";
  ctx.globalAlpha = 0.09;
  ctx.imageSmoothingEnabled = true;
  const pattern = ctx.createPattern(tex, "repeat");
  ctx.fillStyle = pattern;
  ctx.fillRect(0, 0, w, h);
  ctx.restore();
}

function drawGrid(ctx, width, height, scale) {
  ctx.save();
  ctx.strokeStyle = "rgba(0,0,0,0.16)";
  ctx.lineWidth = 1;
  ctx.beginPath();
  for (let x = 0; x <= width; x++) {
    const px = Math.round(x * scale) + 0.5;
    ctx.moveTo(px, 0);
    ctx.lineTo(px, height * scale);
  }
  for (let y = 0; y <= height; y++) {
    const py = Math.round(y * scale) + 0.5;
    ctx.moveTo(0, py);
    ctx.lineTo(width * scale, py);
  }
  ctx.stroke();
  ctx.restore();
}

function updateRenderCaption(width, height, palette) {
  const method = DITHER_LABELS[els.ditherSelect.value];
  const count = paletteColorCount(palette);
  const colorLabel =
    palette.kind === "list"
      ? `${count}-ink palette`
      : palette.grayscale
        ? `${count} gray levels`
        : `${count.toLocaleString()} colors`;
  els.renderCaption.textContent =
    `${width}×${height} · ${colorLabel} · ${method}` +
    (els.realism.checked ? " · reflective response on" : " · ideal colors");
}

// ---------------------------------------------------------------------------
// Download
// ---------------------------------------------------------------------------

function download() {
  if (!state.source) return;
  const link = document.createElement("a");
  const name = `${state.display.id}-${els.ditherSelect.value}.png`;
  link.download = name;
  link.href = state.panelCanvas.toDataURL("image/png");
  link.click();
}

// ---------------------------------------------------------------------------
// Events
// ---------------------------------------------------------------------------

function wireEvents() {
  els.displaySelect.addEventListener("change", () => {
    state.display = getDisplay(els.displaySelect.value) ?? DISPLAYS[0];
    render();
  });

  els.dropZone.addEventListener("click", () => els.fileInput.click());
  els.dropZone.addEventListener("keydown", (e) => {
    if (e.key === "Enter" || e.key === " ") {
      e.preventDefault();
      els.fileInput.click();
    }
  });
  els.fileInput.addEventListener("change", (e) => {
    handleFile(e.target.files[0]);
  });
  ["dragover", "dragenter"].forEach((ev) =>
    els.dropZone.addEventListener(ev, (e) => {
      e.preventDefault();
      els.dropZone.classList.add("dragging");
    }),
  );
  ["dragleave", "dragend", "drop"].forEach((ev) =>
    els.dropZone.addEventListener(ev, (e) => {
      e.preventDefault();
      els.dropZone.classList.remove("dragging");
    }),
  );
  els.dropZone.addEventListener("drop", (e) => {
    handleFile(e.dataTransfer.files[0]);
  });
  // Allow dropping anywhere on the stage too.
  els.viewport.addEventListener("dragover", (e) => e.preventDefault());
  els.viewport.addEventListener("drop", (e) => {
    e.preventDefault();
    handleFile(e.dataTransfer.files[0]);
  });

  els.sampleRow.addEventListener("click", (e) => {
    const btn = e.target.closest("button[data-sample]");
    if (!btn) return;
    state.source = makeSample(btn.dataset.sample);
    render();
  });

  els.ditherSelect.addEventListener("change", render);
  els.serpentine.addEventListener("change", render);
  els.fitSelect.addEventListener("change", render);
  els.rotate.addEventListener("change", render);
  els.realism.addEventListener("change", render);
  els.paperTexture.addEventListener("change", render);
  els.showGrid.addEventListener("change", render);
  els.zoomSelect.addEventListener("change", render);

  document.querySelectorAll(".slider").forEach((slider) => {
    const key = slider.dataset.adjust;
    const input = slider.querySelector("input");
    const output = slider.querySelector("output");
    input.addEventListener("input", () => {
      state.adjust[key] = Number(input.value);
      output.textContent = Number(input.value).toFixed(2);
      scheduleRender();
    });
  });

  els.autoBoost.addEventListener("click", () => {
    setAdjust({ saturation: 1.7, contrast: 1.15, brightness: 1.02, gamma: 1 });
  });
  els.resetAdjust.addEventListener("click", () => {
    setAdjust({ saturation: 1, contrast: 1, brightness: 1, gamma: 1 });
  });

  // Press-and-hold compare with the original.
  const startCompare = () => {
    state.showOriginal = true;
    render();
  };
  const endCompare = () => {
    state.showOriginal = false;
    render();
  };
  els.compare.addEventListener("mousedown", startCompare);
  els.compare.addEventListener("touchstart", (e) => {
    e.preventDefault();
    startCompare();
  });
  ["mouseup", "mouseleave", "touchend", "touchcancel"].forEach((ev) =>
    els.compare.addEventListener(ev, endCompare),
  );

  els.download.addEventListener("click", download);

  window.addEventListener("resize", () => {
    if (els.zoomSelect.value === "fit") scheduleRender();
  });
}

function setAdjust(values) {
  state.adjust = { ...values };
  document.querySelectorAll(".slider").forEach((slider) => {
    const key = slider.dataset.adjust;
    const input = slider.querySelector("input");
    const output = slider.querySelector("output");
    input.value = String(values[key]);
    output.textContent = Number(values[key]).toFixed(2);
  });
  render();
}

// ---------------------------------------------------------------------------
// Init
// ---------------------------------------------------------------------------

// Optional deep-linking: ?device=<id>&sample=<name>&dither=<method> lets you
// share or bookmark a specific setup (and makes the app easy to smoke-test).
function applyUrlParams() {
  const params = new URLSearchParams(window.location.search);
  const device = params.get("device");
  if (device && getDisplay(device)) {
    state.display = getDisplay(device);
    els.displaySelect.value = device;
  }
  const dither = params.get("dither");
  if (dither && DITHER_METHODS.includes(dither)) {
    els.ditherSelect.value = dither;
  }
  return params.get("sample");
}

populateDisplays();
populateDither();
wireEvents();
const sample = applyUrlParams();
state.source = makeSample(sample || "photo");
render();
