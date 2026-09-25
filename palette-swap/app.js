"use strict";

const sampleWidth = 240;
const sampleHeight = 180;
const maxEdge = 320;
const budgetMs = 200;

const source = document.getElementById("source");
const status = document.getElementById("status");
const select = document.getElementById("palette");
const swatches = document.getElementById("swatches");
const times = document.getElementById("times");
const swapButton = document.getElementById("swap");
const benchButton = document.getElementById("bench");
const fileInput = document.getElementById("file");
const sampleButton = document.getElementById("sample");

const canvases = {
  scalar: document.getElementById("scalar"),
  portable: document.getElementById("portable"),
  arch: document.getElementById("arch"),
};

const palettes = new Map();
let api = null;

function setStatus(text) {
  status.textContent = text;
}

function clearResults() {
  for (const canvas of Object.values(canvases)) {
    canvas.width = source.width;
    canvas.height = source.height;
    canvas.getContext("2d").clearRect(0, 0, canvas.width, canvas.height);
  }
  times.replaceChildren();
}

function putPixel(data, width, height, x, y, r, g, b) {
  if (x < 0 || y < 0 || x >= width || y >= height) {
    return;
  }
  const i = (y * width + x) * 4;
  data[i] = r;
  data[i + 1] = g;
  data[i + 2] = b;
  data[i + 3] = 255;
}

function fillRect(data, width, height, x0, y0, x1, y1, r, g, b) {
  const xa = Math.max(0, x0);
  const ya = Math.max(0, y0);
  const xb = Math.min(width, x1);
  const yb = Math.min(height, y1);
  for (let y = ya; y < yb; y++) {
    for (let x = xa; x < xb; x++) {
      putPixel(data, width, height, x, y, r, g, b);
    }
  }
}

function fillCircle(data, width, height, cx, cy, radius, r, g, b) {
  const r2 = radius * radius;
  for (let y = cy - radius; y <= cy + radius; y++) {
    for (let x = cx - radius; x <= cx + radius; x++) {
      const dx = x - cx;
      const dy = y - cy;
      if (dx * dx + dy * dy <= r2) {
        putPixel(data, width, height, x, y, r, g, b);
      }
    }
  }
}

function drawSample() {
  source.width = sampleWidth;
  source.height = sampleHeight;
  const ctx = source.getContext("2d");
  const image = ctx.createImageData(sampleWidth, sampleHeight);
  const data = image.data;
  const horizon = 100;
  for (let y = 0; y < sampleHeight; y++) {
    let r = 70;
    let g = 140;
    let b = 210;
    if (y < horizon) {
      const t = y / horizon;
      r = 90 + t * 140;
      g = 150 + t * 70;
      b = 220 + t * 20;
    } else {
      const t = (y - horizon) / (sampleHeight - horizon);
      r = 70 + t * 40;
      g = 130 - t * 40;
      b = 60;
    }
    for (let x = 0; x < sampleWidth; x++) {
      putPixel(data, sampleWidth, sampleHeight, x, y, r, g, b);
    }
  }
  fillCircle(data, sampleWidth, sampleHeight, 180, 48, 22, 250, 210, 70);
  fillRect(data, sampleWidth, sampleHeight, 30, 110, 90, 165, 150, 70, 40);
  fillRect(data, sampleWidth, sampleHeight, 22, 88, 98, 115, 170, 40, 35);
  fillRect(data, sampleWidth, sampleHeight, 48, 125, 70, 165, 230, 180, 90);
  fillCircle(data, sampleWidth, sampleHeight, 140, 130, 16, 40, 110, 50);
  fillCircle(data, sampleWidth, sampleHeight, 168, 122, 20, 20, 80, 40);
  const flowers = [
    [40, 150, 220, 70, 90],
    [70, 145, 240, 180, 40],
    [200, 150, 190, 60, 170],
    [214, 140, 230, 120, 160],
    [110, 155, 230, 60, 50],
  ];
  for (const flower of flowers) {
    fillCircle(data, sampleWidth, sampleHeight, flower[0], flower[1], 7, flower[2], flower[3], flower[4]);
  }
  ctx.putImageData(image, 0, 0);
  return image;
}

function currentImage() {
  const ctx = source.getContext("2d");
  return ctx.getImageData(0, 0, source.width, source.height);
}

function bytesEqual(a, b) {
  if (a.length !== b.length) {
    return false;
  }
  for (let i = 0; i < a.length; i++) {
    if (a[i] !== b[i]) {
      return false;
    }
  }
  return true;
}

function paintResult(canvas, indices, rgb) {
  const width = source.width;
  const height = source.height;
  canvas.width = width;
  canvas.height = height;
  const ctx = canvas.getContext("2d");
  const image = ctx.createImageData(width, height);
  const dst = image.data;
  for (let i = 0; i < width * height; i++) {
    const index = indices[i * 2] + indices[i * 2 + 1] * 256;
    const c = index * 3;
    const p = i * 4;
    dst[p] = rgb[c];
    dst[p + 1] = rgb[c + 1];
    dst[p + 2] = rgb[c + 2];
    dst[p + 3] = 255;
  }
  ctx.putImageData(image, 0, 0);
}

function showSwatches(rgb) {
  swatches.replaceChildren();
  for (let i = 0; i < rgb.length; i += 3) {
    const chip = document.createElement("span");
    chip.style.background = "rgb(" + rgb[i] + ", " + rgb[i + 1] + ", " + rgb[i + 2] + ")";
    swatches.appendChild(chip);
  }
}

function renderTimes(rows) {
  times.replaceChildren();
  const table = document.createElement("table");
  const head = document.createElement("tr");
  for (const label of ["Method", "Time", "Per pixel", "Versus scalar"]) {
    const cell = document.createElement("th");
    cell.textContent = label;
    if (label !== "Method") {
      cell.className = "num";
    }
    head.appendChild(cell);
  }
  table.appendChild(head);
  const scalar = rows[0];
  for (const row of rows) {
    const tr = document.createElement("tr");
    const name = document.createElement("td");
    name.textContent = row.label;
    tr.appendChild(name);
    const time = document.createElement("td");
    time.className = "num";
    time.textContent = row.ms.toFixed(1) + " ms";
    tr.appendChild(time);
    const per = document.createElement("td");
    per.className = "num";
    per.textContent = row.nsPerPixel.toFixed(1) + " ns";
    tr.appendChild(per);
    const rel = document.createElement("td");
    rel.className = "num";
    const timesFaster = row.nsPerPixel === 0 ? 0 : scalar.nsPerPixel / row.nsPerPixel;
    rel.textContent = timesFaster.toFixed(2) + "x";
    tr.appendChild(rel);
    table.appendChild(tr);
  }
  times.appendChild(table);
}

function selectedPalette() {
  return palettes.get(select.value);
}

function runAll() {
  const palette = selectedPalette();
  if (!api || !palette) {
    return;
  }
  const image = currentImage();
  const loaded = api.load(image.data);
  if (loaded.error) {
    setStatus(loaded.error);
    return;
  }
  const order = ["scalar", "portable", "arch"];
  const labels = {
    scalar: "Scalar",
    portable: "Portable SIMD",
    arch: "Wasm archsimd",
  };
  const rows = [];
  let first = null;
  let match = true;
  for (const which of order) {
    const indices = new Uint8Array(image.data.length / 2);
    const stat = api.run(palette.id, which, indices);
    if (stat.error) {
      setStatus(stat.error);
      return;
    }
    if (first === null) {
      first = indices;
    } else if (!bytesEqual(first, indices)) {
      match = false;
    }
    paintResult(canvases[which], indices, palette.rgb);
    rows.push({
      label: labels[which],
      ms: stat.ms,
      nsPerPixel: stat.nsPerPixel,
    });
  }
  renderTimes(rows);
  const matchText = match ? "The index buffers match." : "The index buffers differ.";
  const simdText = api.emulated
    ? "Portable SIMD is emulated in this process."
    : "Portable SIMD is using " + api.lanes + " int32 lanes.";
  setStatus(matchText + " " + simdText);
}

function benchmark() {
  const palette = selectedPalette();
  if (!api || !palette) {
    return;
  }
  const image = currentImage();
  const loaded = api.load(image.data);
  if (loaded.error) {
    setStatus(loaded.error);
    return;
  }
  const order = ["scalar", "portable", "arch"];
  const labels = {
    scalar: "Scalar",
    portable: "Portable SIMD",
    arch: "Wasm archsimd",
  };
  const rows = [];
  let match = true;
  let scalarSum = null;
  for (const which of order) {
    const stat = api.bench(palette.id, which, budgetMs);
    if (stat.error) {
      setStatus(stat.error);
      return;
    }
    if (scalarSum === null) {
      scalarSum = stat.sum;
    } else if (stat.sum !== scalarSum) {
      match = false;
    }
    rows.push({
      label: labels[which],
      ms: stat.ms,
      nsPerPixel: stat.nsPerPixel,
      iters: stat.iters,
    });
  }
  renderTimes(rows);
  const matchText = match ? "Checksums match." : "Checksums differ.";
  setStatus(
    "Each method ran for at least " +
      budgetMs +
      " ms after one warmup, on " +
      image.width +
      " by " +
      image.height +
      " pixels and " +
      palette.count +
      " colors. " +
      matchText,
  );
}

// The Wasm call blocks the page, so paint the status line first.
function runSoon(label, work) {
  setStatus(label);
  swapButton.disabled = true;
  benchButton.disabled = true;
  setTimeout(function () {
    work();
    swapButton.disabled = false;
    benchButton.disabled = false;
  }, 0);
}

function loadPaletteList() {
  const list = api.list();
  select.replaceChildren();
  palettes.clear();
  for (const item of list) {
    const rgb = new Uint8Array(item.count * 3);
    const wrote = api.rgb(item.id, rgb);
    if (wrote.error) {
      setStatus(wrote.error);
      return;
    }
    palettes.set(item.id, { id: item.id, name: item.name, count: item.count, rgb: rgb });
    const option = document.createElement("option");
    option.value = item.id;
    option.textContent = item.name + " (" + item.count + ")";
    select.appendChild(option);
  }
  select.value = "floss";
  showSwatches(selectedPalette().rgb);
}

function paintFile(file) {
  const url = URL.createObjectURL(file);
  const image = new Image();
  image.onload = function () {
    URL.revokeObjectURL(url);
    let width = image.naturalWidth;
    let height = image.naturalHeight;
    const scale = Math.min(1, maxEdge / Math.max(width, height));
    width = Math.max(1, Math.round(width * scale));
    height = Math.max(1, Math.round(height * scale));
    source.width = width;
    source.height = height;
    source.getContext("2d").drawImage(image, 0, 0, width, height);
    clearResults();
    setStatus("Image is " + width + " by " + height + " pixels.");
  };
  image.onerror = function () {
    URL.revokeObjectURL(url);
    setStatus("That file could not be read as an image.");
  };
  image.src = url;
}

async function boot() {
  drawSample();
  if (typeof WebAssembly === "undefined") {
    setStatus("This browser has no WebAssembly.");
    return;
  }
  const go = new Go();
  let compiled;
  try {
    compiled = await WebAssembly.instantiateStreaming(fetch("wasm/palette.wasm"), go.importObject);
  } catch (err) {
    setStatus("Wasm did not start. " + err);
    return;
  }
  go.run(compiled.instance);
  api = globalThis.paletteSwap;
  if (!api) {
    setStatus("The Wasm module did not register paletteSwap.");
    return;
  }
  loadPaletteList();
  swapButton.disabled = false;
  benchButton.disabled = false;
  setStatus("Ready. Portable SIMD reports " + api.lanes + " int32 lanes.");
}

select.addEventListener("change", function () {
  const palette = selectedPalette();
  if (palette) {
    showSwatches(palette.rgb);
  }
});
swapButton.addEventListener("click", function () {
  runSoon("Swap is running.", runAll);
});
benchButton.addEventListener("click", function () {
  runSoon("Benchmark is running.", benchmark);
});
sampleButton.addEventListener("click", function () {
  drawSample();
  clearResults();
  setStatus("Sample picture is ready.");
});
fileInput.addEventListener("change", function () {
  const file = fileInput.files && fileInput.files[0];
  if (file) {
    paintFile(file);
  }
});

boot();
