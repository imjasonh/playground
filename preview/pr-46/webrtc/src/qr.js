// Thin wrapper around the vendored qrcode-generator library.
//
// Renders a QR code into a <canvas>. Error-correction level "L" is used to
// maximize data capacity, since our compressed tokens push against the QR
// size limit. Throws QrCapacityError when the text is too large to fit even
// the largest QR version (~2953 bytes), so callers can fall back gracefully.

import qrcode from "./vendor/qrcode-generator.js";

export class QrCapacityError extends Error {
  constructor(message) {
    super(message);
    this.name = "QrCapacityError";
  }
}

// Build the QR module matrix for `text`. Returns { count, isDark }.
export function buildMatrix(text, ecLevel = "L") {
  const qr = qrcode(0, ecLevel); // typeNumber 0 = auto-select smallest version
  qr.addData(text); // default Byte mode handles arbitrary base64/URL text
  try {
    qr.make();
  } catch (err) {
    throw new QrCapacityError(
      `Data too large for a QR code (${text.length} chars): ${err}`,
    );
  }
  const count = qr.getModuleCount();
  return { count, isDark: (r, c) => qr.isDark(r, c) };
}

// Draw a QR for `text` onto a canvas sized to roughly `size` CSS pixels.
// Returns the canvas element. `quietZone` is the margin in modules (QR spec
// recommends 4).
export function renderToCanvas(text, { size = 320, quietZone = 4, ecLevel = "L" } = {}) {
  const { count, isDark } = buildMatrix(text, ecLevel);
  const total = count + quietZone * 2;

  // Integer module size keeps modules crisp; recompute the canvas to match.
  const scale = Math.max(1, Math.floor(size / total));
  const dim = total * scale;

  const canvas = document.createElement("canvas");
  canvas.width = dim;
  canvas.height = dim;
  const ctx = canvas.getContext("2d");
  ctx.fillStyle = "#ffffff";
  ctx.fillRect(0, 0, dim, dim);
  ctx.fillStyle = "#000000";
  for (let r = 0; r < count; r += 1) {
    for (let c = 0; c < count; c += 1) {
      if (isDark(r, c)) {
        ctx.fillRect((c + quietZone) * scale, (r + quietZone) * scale, scale, scale);
      }
    }
  }
  canvas.dataset.moduleCount = String(count);
  return canvas;
}
