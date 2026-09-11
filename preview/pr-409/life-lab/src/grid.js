// Pure grid helpers for the generation-0 editor (Node-testable).

/** Row-major byte grid, 1 = alive. */
export function makeCells(width, height) {
  return new Uint8Array(width * height);
}

/** Resize preserving content, anchored at the top-left. */
export function resizeCells(cells, oldW, oldH, newW, newH) {
  const out = new Uint8Array(newW * newH);
  const w = Math.min(oldW, newW);
  const h = Math.min(oldH, newH);
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      out[y * newW + x] = cells[y * oldW + x];
    }
  }
  return out;
}

export function setCell(cells, width, x, y, alive) {
  cells[y * width + x] = alive ? 1 : 0;
}

export function getCell(cells, width, x, y) {
  return cells[y * width + x] !== 0;
}

export function liveCount(cells) {
  let n = 0;
  for (const c of cells) n += c !== 0 ? 1 : 0;
  return n;
}

/** Map a pointer event position on the canvas to cell coords, or null. */
export function pointToCell(px, py, canvasW, canvasH, gridW, gridH) {
  const x = Math.floor((px / canvasW) * gridW);
  const y = Math.floor((py / canvasH) * gridH);
  if (x < 0 || y < 0 || x >= gridW || y >= gridH) return null;
  return { x, y };
}
