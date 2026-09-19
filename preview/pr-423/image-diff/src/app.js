import {
  compareImages,
  cropOverlay,
  describeCompare,
  formatDimensions,
} from "./diff.js";

const slots = {
  a: bindSlot("a"),
  b: bindSlot("b"),
};

const resultEl = document.querySelector("#result");
const resultCanvas = document.querySelector("#diff-canvas");
const resultEmpty = document.querySelector("#result-empty");
const resultStatus = document.querySelector("#result-status");
const resultCtx = resultCanvas.getContext("2d", { willReadFrequently: true });

const state = { a: null, b: null };

function bindSlot(id) {
  const root = document.querySelector(`[data-slot="${id}"]`);
  return {
    id,
    root,
    input: root.querySelector("input[type='file']"),
    preview: root.querySelector(".preview"),
    image: root.querySelector(".preview img"),
    crop: root.querySelector(".crop"),
    meta: root.querySelector(".slot-meta"),
  };
}

function revoke(image) {
  if (image?.url) {
    URL.revokeObjectURL(image.url);
  }
}

function pixelsFromBitmap(bitmap) {
  const canvas = document.createElement("canvas");
  canvas.width = bitmap.width;
  canvas.height = bitmap.height;
  const ctx = canvas.getContext("2d", { willReadFrequently: true });
  ctx.drawImage(bitmap, 0, 0);
  return ctx.getImageData(0, 0, bitmap.width, bitmap.height);
}

async function decodeFile(file) {
  let bitmap;
  try {
    bitmap = await createImageBitmap(file, { imageOrientation: "from-image" });
  } catch {
    bitmap = await createImageBitmap(file);
  }
  try {
    const imageData = pixelsFromBitmap(bitmap);
    return {
      name: file.name,
      width: imageData.width,
      height: imageData.height,
      data: imageData.data,
      url: URL.createObjectURL(file),
    };
  } finally {
    bitmap.close();
  }
}

function setSlotError(slot, message) {
  slot.meta.hidden = false;
  slot.meta.textContent = message;
  slot.root.classList.add("is-error");
}

function showSlot(slot, image) {
  slot.root.classList.remove("is-error");
  slot.root.classList.add("has-image");
  slot.image.src = image.url;
  slot.image.alt = image.name;
  slot.preview.hidden = false;
  slot.meta.hidden = false;
  slot.meta.textContent = `${image.name} \u00b7 ${formatDimensions(image.width, image.height)}`;
}

function layoutCrops() {
  for (const id of ["a", "b"]) {
    const slot = slots[id];
    const image = state[id];
    const crop = state.compare?.[`crop${id === "a" ? "A" : "B"}`];
    const cropped = state.compare?.[`cropped${id === "a" ? "A" : "B"}`];
    if (!image || !crop || !cropped) {
      slot.crop.hidden = true;
      continue;
    }
    const box = slot.preview.getBoundingClientRect();
    if (box.width < 1 || box.height < 1) {
      slot.crop.hidden = true;
      continue;
    }
    const overlay = cropOverlay(
      box.width,
      box.height,
      image.width,
      image.height,
      crop,
    );
    slot.crop.hidden = false;
    slot.crop.style.left = `${overlay.x}px`;
    slot.crop.style.top = `${overlay.y}px`;
    slot.crop.style.width = `${overlay.width}px`;
    slot.crop.style.height = `${overlay.height}px`;
  }
}

function clearResult() {
  state.compare = null;
  resultCanvas.hidden = true;
  resultEmpty.hidden = false;
  resultStatus.textContent = "";
  resultEl.classList.remove("has-diff");
  layoutCrops();
}

function paintResult(result) {
  resultCanvas.width = result.width;
  resultCanvas.height = result.height;
  resultCtx.putImageData(
    new ImageData(result.image.data, result.width, result.height),
    0,
    0,
  );
  resultCanvas.hidden = false;
  resultEmpty.hidden = true;
  resultEl.classList.add("has-diff");
  resultStatus.textContent = describeCompare(result, state.a, state.b);
  state.compare = result;
  layoutCrops();
}

async function refreshDiff() {
  if (!state.a || !state.b) {
    clearResult();
    return;
  }
  resultStatus.textContent = "Comparing\u2026";
  resultEmpty.hidden = true;
  await new Promise((resolve) => {
    requestAnimationFrame(() => resolve());
  });
  paintResult(compareImages(state.a, state.b));
}

async function assignFile(id, file) {
  const slot = slots[id];
  if (!file || !looksLikeImage(file)) {
    setSlotError(slot, "That file is not an image.");
    return;
  }
  try {
    const image = await decodeFile(file);
    revoke(state[id]);
    state[id] = image;
    showSlot(slot, image);
    await refreshDiff();
  } catch {
    setSlotError(slot, "Could not read that image.");
  }
}

function looksLikeImage(file) {
  if (file.type.startsWith("image/")) {
    return true;
  }
  if (file.type === "") {
    return /\.(avif|bmp|gif|jpe?g|png|svg|webp)$/i.test(file.name);
  }
  return false;
}

function filesFromEvent(event) {
  if (event.dataTransfer?.files?.length) {
    return [...event.dataTransfer.files];
  }
  if (event.target?.files?.length) {
    return [...event.target.files];
  }
  return [];
}

function wireSlot(slot) {
  const openPicker = () => {
    slot.input.value = "";
    slot.input.click();
  };

  slot.root.addEventListener("click", (event) => {
    if (event.target === slot.input) {
      return;
    }
    openPicker();
  });
  slot.input.addEventListener("click", (event) => {
    event.stopPropagation();
  });
  slot.root.addEventListener("keydown", (event) => {
    if (event.key === "Enter" || event.key === " ") {
      event.preventDefault();
      openPicker();
    }
  });

  slot.input.addEventListener("change", (event) => {
    const [file] = filesFromEvent(event);
    assignFile(slot.id, file);
  });

  slot.root.addEventListener("dragenter", (event) => {
    event.preventDefault();
    slot.root.classList.add("is-drag");
  });
  slot.root.addEventListener("dragover", (event) => {
    event.preventDefault();
    event.dataTransfer.dropEffect = "copy";
    slot.root.classList.add("is-drag");
  });
  slot.root.addEventListener("dragleave", (event) => {
    if (!slot.root.contains(event.relatedTarget)) {
      slot.root.classList.remove("is-drag");
    }
  });
  slot.root.addEventListener("drop", (event) => {
    event.preventDefault();
    slot.root.classList.remove("is-drag");
    const files = filesFromEvent(event).filter((file) => looksLikeImage(file));
    if (files.length >= 2) {
      assignFile("a", files[0]);
      assignFile("b", files[1]);
      return;
    }
    assignFile(slot.id, files[0]);
  });
}

wireSlot(slots.a);
wireSlot(slots.b);
window.addEventListener("resize", layoutCrops);
slots.a.image.addEventListener("load", layoutCrops);
slots.b.image.addEventListener("load", layoutCrops);
