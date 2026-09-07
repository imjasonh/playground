// Hex-editor rendering and segment-colored content views.

import { decodeUtf8 } from "./hex.js";
import { shortOid } from "./format.js";

/** Distinct hues for copy instructions (inserts use white). */
export const COPY_PALETTE = [
  "#7ec8e3",
  "#f4a261",
  "#90be6d",
  "#e76f51",
  "#b8a9ff",
  "#ffd166",
];

const INSERT_TEXT = "#f8fafc";
const INSERT_HEX = "#e8eef2";

function escapeHtml(value) {
  return String(value)
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}

/** Map each byte index to the last region that covers it. */
export function byteRoles(length, regions) {
  const roles = new Array(length).fill(null);
  for (const region of regions) {
    for (let i = region.start; i < region.end && i < length; i += 1) {
      roles[i] = region;
    }
  }
  return roles;
}

function regionStyle(region) {
  if (!region) return { className: "hx-default", title: "" };
  const title = region.label || region.role || "";
  switch (region.role) {
    case "header":
    case "pack-header":
      return { className: "hx-header", title };
    case "base-oid":
    case "base-offset":
      return { className: "hx-pointer", title, baseOid: region.baseOid };
    case "zlib":
      return { className: "hx-zlib", title };
    case "opcode":
      if (region.op === "insert") return { className: "hx-opcode-insert", title };
      return {
        className: `hx-opcode-copy hx-copy-${region.copyIndex % COPY_PALETTE.length}`,
        title,
        copyIndex: region.copyIndex,
      };
    case "copy-offset":
    case "copy-size":
      return {
        className: `hx-copy-meta hx-copy-${region.copyIndex % COPY_PALETTE.length}`,
        title,
        copyIndex: region.copyIndex,
      };
    case "insert-data":
      return { className: "hx-insert", title };
    default:
      return { className: "hx-default", title };
  }
}

function asciiChar(byte) {
  if (byte >= 0x20 && byte < 0x7f) return String.fromCharCode(byte);
  return ".";
}

/**
 * Render a hex dump with per-byte highlighting. `baseOffset` is added to the
 * left-hand address column (for pack-absolute offsets).
 */
export function renderHexEditor(bytes, regions, { baseOffset = 0, maxBytes = 65536 } = {}) {
  const limit = Math.min(bytes.length, maxBytes);
  const roles = byteRoles(limit, regions);
  const rows = [];
  for (let row = 0; row < limit; row += 16) {
    const rowEnd = Math.min(row + 16, limit);
    const offsetLabel = (baseOffset + row).toString(16).padStart(8, "0");
    let hexCells = "";
    let asciiCells = "";
    for (let i = row; i < rowEnd; i += 1) {
      const style = regionStyle(roles[i]);
      const hex = bytes[i].toString(16).padStart(2, "0");
      hexCells +=
        `<span class="hex-byte ${style.className}" title="${escapeHtml(style.title)}">${hex}</span>`;
      asciiCells +=
        `<span class="hex-ascii-char ${style.className}" title="${escapeHtml(style.title)}">` +
        `${escapeHtml(asciiChar(bytes[i]))}</span>`;
    }
    const pad = (rowEnd - row) * 3;
    rows.push(
      `<div class="hex-row">` +
        `<span class="hex-offset">${offsetLabel}</span>` +
        `<span class="hex-bytes">${hexCells}<span class="hex-pad" aria-hidden="true">${"   ".repeat(16 - (rowEnd - row))}</span></span>` +
        `<span class="hex-ascii">${asciiCells}</span>` +
        `</div>`,
    );
  }
  const truncated =
    bytes.length > limit
      ? `<p class="hex-truncated">Showing first ${limit.toLocaleString()} of ${bytes.length.toLocaleString()} bytes.</p>`
      : "";
  return (
    `<div class="hex-editor">` +
    renderLegend(regions) +
    `<div class="hex-body" tabindex="0" role="group" aria-label="hex dump (arrow keys scroll)">${rows.join("")}</div>` +
    truncated +
    `</div>`
  );
}

function renderLegend(regions) {
  const copies = new Map();
  let hasInsert = false;
  let hasPointer = false;
  let hasHeader = false;
  let hasZlib = false;
  for (const r of regions) {
    if (r.role === "header" || r.role === "pack-header") hasHeader = true;
    if (r.role === "base-oid" || r.role === "base-offset") hasPointer = true;
    if (r.role === "zlib") hasZlib = true;
    if (r.op === "insert" || r.role === "insert-data") hasInsert = true;
    if (r.copyIndex != null && !copies.has(r.copyIndex)) {
      copies.set(r.copyIndex, r);
    }
  }
  const chips = [];
  if (hasHeader) chips.push(`<span class="hex-legend-chip hx-header">header</span>`);
  if (hasPointer) chips.push(`<span class="hex-legend-chip hx-pointer">base pointer</span>`);
  if (hasZlib) chips.push(`<span class="hex-legend-chip hx-zlib">zlib</span>`);
  for (const [idx] of [...copies.entries()].sort((a, b) => a[0] - b[0])) {
    const color = COPY_PALETTE[idx % COPY_PALETTE.length];
    chips.push(
      `<span class="hex-legend-chip hx-copy-${idx % COPY_PALETTE.length}" style="--copy-color:${color}">copy #${idx}</span>`,
    );
  }
  if (hasInsert) {
    chips.push(`<span class="hex-legend-chip hx-insert">insert (literal)</span>`);
  }
  if (chips.length === 0) return "";
  return `<div class="hex-legend">${chips.join("")}</div>`;
}

/** Render resolved content as colored text (one span per segment). */
export function renderSegmentedText(bytes, segments, { maxBytes = 200_000 } = {}) {
  const limit = Math.min(bytes.length, maxBytes);
  const parts = [];
  for (const seg of segments) {
    if (seg.start >= limit) break;
    const end = Math.min(seg.end, limit);
    if (end <= seg.start) continue;
    const chunk = bytes.subarray(seg.start, end);
    if (seg.kind === "insert") {
      parts.push(
        `<span class="seg-insert" title="inserted literal (${end - seg.start} B)">${escapeHtml(decodeUtf8(chunk))}</span>`,
      );
    } else {
      const idx = seg.copyIndex % COPY_PALETTE.length;
      const title =
        `copy #${seg.copyIndex} from ${seg.baseOid ? shortOid(seg.baseOid) : "base"}` +
        `@${seg.baseOffset} (${end - seg.start} B)`;
      parts.push(
        `<span class="seg-copy seg-copy-${idx}" title="${escapeHtml(title)}" style="--copy-color:${COPY_PALETTE[idx]}">${escapeHtml(decodeUtf8(chunk))}</span>`,
      );
    }
  }
  const truncated = bytes.length > limit ? `\n… truncated at ${limit.toLocaleString()} bytes` : "";
  return (
    `<div class="segment-legend">${renderSegmentLegend(segments)}</div>` +
    `<pre class="content segmented-text">${parts.join("")}${escapeHtml(truncated)}</pre>`
  );
}

/** Render resolved content as a hex dump colored by output segment. */
export function renderSegmentedHex(bytes, segments, { maxBytes = 65536 } = {}) {
  const limit = Math.min(bytes.length, maxBytes);
  const regions = [];
  for (const seg of segments) {
    if (seg.start >= limit) break;
    const end = Math.min(seg.end, limit);
    if (seg.kind === "insert") {
      regions.push({
        start: seg.start,
        end,
        role: "insert-data",
        label: `inserted literal (${end - seg.start} B)`,
      });
    } else {
      regions.push({
        start: seg.start,
        end,
        role: "copy-offset",
        copyIndex: seg.copyIndex,
        label:
          `copy #${seg.copyIndex} from ${seg.baseOid ? shortOid(seg.baseOid) : "base"}` +
          `@${seg.baseOffset} (${end - seg.start} B)`,
      });
    }
  }
  return (
    `<div class="segment-legend">${renderSegmentLegend(segments)}</div>` +
    renderHexEditor(bytes.subarray(0, limit), regions, { baseOffset: 0, maxBytes: limit })
  );
}

function renderSegmentLegend(segments) {
  const copies = new Map();
  let hasInsert = false;
  for (const seg of segments) {
    if (seg.kind === "insert") hasInsert = true;
    else if (!copies.has(seg.copyIndex)) copies.set(seg.copyIndex, seg);
  }
  const chips = [];
  for (const [idx, seg] of [...copies.entries()].sort((a, b) => a[0] - b[0])) {
    const color = COPY_PALETTE[idx % COPY_PALETTE.length];
    chips.push(
      `<span class="hex-legend-chip seg-copy-${idx % COPY_PALETTE.length}" style="--copy-color:${color}">` +
        `copy #${idx} · ${seg.baseOid ? shortOid(seg.baseOid) : "base"}@${seg.baseOffset}` +
        `</span>`,
    );
  }
  if (hasInsert) chips.push(`<span class="hex-legend-chip hx-insert">insert (white)</span>`);
  return chips.join("");
}
