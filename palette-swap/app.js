"use strict";

const maxEdge = 320;
const budgetMs = 200;
const methods = [
  { which: "scalar", label: "Scalar" },
  { which: "portable", label: "Portable SIMD" },
  { which: "arch", label: "Wasm archsimd" },
];

const source = document.getElementById("source");
const results = document.getElementById("results");
const status = document.getElementById("status");
const select = document.getElementById("palette");
const swatches = document.getElementById("swatches");
const times = document.getElementById("times");
const benchButton = document.getElementById("bench");
const fileInput = document.getElementById("file");

const canvases = {
  scalar: document.getElementById("scalar"),
  portable: document.getElementById("portable"),
  arch: document.getElementById("arch"),
};

const palettes = new Map();
let api = null;
let imageReady = false;
let working = false;

function setStatus(text) {
  status.textContent = text;
}

function setBusy(busy) {
  working = busy;
  benchButton.disabled = busy || !imageReady;
  select.disabled = busy || !api;
  fileInput.disabled = busy || !api;
}

function clearResults() {
  for (const canvas of Object.values(canvases)) {
    canvas.width = source.width;
    canvas.height = source.height;
    canvas.getContext("2d").clearRect(0, 0, canvas.width, canvas.height);
  }
  times.replaceChildren();
  for (const figure of results.querySelectorAll("figure")) {
    figure.classList.remove("fastest");
  }
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
    if (row.fastest) {
      tr.className = "fastest";
    }
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

function currentImage() {
  return source.getContext("2d").getImageData(0, 0, source.width, source.height);
}

function markFastest(rows) {
  let best = rows[0].nsPerPixel;
  for (const row of rows) {
    if (row.nsPerPixel < best) {
      best = row.nsPerPixel;
    }
  }
  for (const row of rows) {
    row.fastest = row.nsPerPixel === best;
    const figure = results.querySelector("[data-method='" + row.which + "']");
    figure.classList.toggle("fastest", row.fastest);
  }
}

function benchmark() {
  const palette = selectedPalette();
  if (!api || !palette || !imageReady) {
    return;
  }
  const image = currentImage();
  const loaded = api.load(image.data);
  if (loaded.error) {
    setStatus(loaded.error);
    return;
  }
  clearResults();
  const rows = [];
  let first = null;
  let match = true;
  for (const method of methods) {
    const indices = new Uint8Array(image.data.length / 2);
    const stat = api.bench(palette.id, method.which, budgetMs, indices);
    if (stat.error) {
      setStatus(stat.error);
      return;
    }
    if (first === null) {
      first = indices;
    } else if (!bytesEqual(first, indices)) {
      match = false;
    }
    paintResult(canvases[method.which], indices, palette.rgb);
    rows.push({
      which: method.which,
      label: method.label,
      ms: stat.ms,
      nsPerPixel: stat.nsPerPixel,
    });
  }
  markFastest(rows);
  renderTimes(rows);
  const matchText = match ? "The index buffers match." : "The index buffers differ.";
  const simdText = api.emulated
    ? "Portable SIMD is emulated in this process."
    : "Portable SIMD is using " + api.lanes + " int32 lanes.";
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
      matchText +
      " " +
      simdText,
  );
}

// The Wasm call blocks the page, so paint the status line first.
function runSoon() {
  if (!imageReady || !api || working) {
    return;
  }
  setStatus("Benchmark is running.");
  setBusy(true);
  setTimeout(function () {
    benchmark();
    setBusy(false);
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
    results.hidden = false;
    imageReady = true;
    clearResults();
    runSoon();
  };
  image.onerror = function () {
    URL.revokeObjectURL(url);
    setStatus("That file could not be read as an image.");
  };
  image.src = url;
}

async function boot() {
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
  setBusy(false);
  setStatus("Upload an image.");
}

select.addEventListener("change", function () {
  const palette = selectedPalette();
  if (palette) {
    showSwatches(palette.rgb);
  }
  runSoon();
});
benchButton.addEventListener("click", function () {
  runSoon();
});
fileInput.addEventListener("change", function () {
  const file = fileInput.files && fileInput.files[0];
  if (file) {
    paintFile(file);
  }
});

boot();
