/**
 * A small, dependency-free QR Code encoder.
 *
 * It exists so the app can turn the current deep-link URL into a scannable code
 * entirely on-device — no network, no third-party image service. The output is
 * a boolean matrix (`true` = a dark module); rendering it to SVG/canvas is left
 * to the caller (see ui/share.js).
 *
 * Scope, kept deliberately narrow for a "share this link" use:
 *   - Byte (8-bit) encoding mode only. URLs are UTF-8 bytes, and byte mode
 *     covers every character, so mode auto-selection buys nothing here.
 *   - Versions 1–10 (21×21 up to 61×61). Version 10 at error-correction level M
 *     holds 213 bytes, comfortably past any share URL this app produces.
 *   - Error-correction levels L / M / Q / H.
 *   - The smallest version that fits the payload is chosen automatically, and
 *     the mask pattern is picked by the standard penalty rules.
 *
 * Everything is pure and DOM-free so it can be unit-tested in isolation. The
 * encoding follows ISO/IEC 18004; the block/alignment tables below are the
 * version 1–10 rows of that standard.
 *
 * @typedef {'L'|'M'|'Q'|'H'} EcLevel
 *
 * @typedef {Object} QrCode
 * @property {number} version   QR version (1–10)
 * @property {number} size      module count per side (17 + 4·version)
 * @property {EcLevel} ecLevel  error-correction level used
 * @property {boolean[][]} modules  size×size grid; modules[y][x] true == dark
 */

const MODE_BYTE = 0b0100;

// GF(256) log / antilog tables under the QR primitive polynomial x^8+x^4+x^3+x^2+1.
const EXP = new Uint8Array(512);
const LOG = new Uint8Array(256);
(function initGaloisField() {
  let x = 1;
  for (let i = 0; i < 255; i += 1) {
    EXP[i] = x;
    LOG[x] = i;
    x <<= 1;
    if (x & 0x100) x ^= 0x11d;
  }
  for (let i = 255; i < 512; i += 1) EXP[i] = EXP[i - 255];
})();

function gfMul(a, b) {
  if (a === 0 || b === 0) return 0;
  return EXP[LOG[a] + LOG[b]];
}

/**
 * Per-version, per-level error-correction layout (versions 1–10).
 * Each entry: [ecCodewordsPerBlock, [group1Blocks, group1DataCodewords],
 * (optional) [group2Blocks, group2DataCodewords]].
 */
const EC_BLOCKS = {
  1: { L: [7, [1, 19]], M: [10, [1, 16]], Q: [13, [1, 13]], H: [17, [1, 9]] },
  2: { L: [10, [1, 34]], M: [16, [1, 28]], Q: [22, [1, 22]], H: [28, [1, 16]] },
  3: { L: [15, [1, 55]], M: [26, [1, 44]], Q: [18, [2, 17]], H: [22, [2, 13]] },
  4: { L: [20, [1, 80]], M: [18, [2, 32]], Q: [26, [2, 24]], H: [16, [4, 9]] },
  5: {
    L: [26, [1, 108]],
    M: [24, [2, 43]],
    Q: [18, [2, 15], [2, 16]],
    H: [22, [2, 11], [2, 12]],
  },
  6: { L: [18, [2, 68]], M: [16, [4, 27]], Q: [24, [4, 19]], H: [28, [4, 15]] },
  7: {
    L: [20, [2, 78]],
    M: [18, [4, 31]],
    Q: [18, [2, 14], [4, 15]],
    H: [26, [4, 13], [1, 14]],
  },
  8: {
    L: [24, [2, 97]],
    M: [22, [2, 38], [2, 39]],
    Q: [22, [4, 18], [2, 19]],
    H: [26, [4, 14], [2, 15]],
  },
  9: {
    L: [30, [2, 116]],
    M: [22, [3, 36], [2, 37]],
    Q: [20, [4, 16], [4, 17]],
    H: [24, [4, 12], [4, 13]],
  },
  10: {
    L: [18, [2, 68], [2, 69]],
    M: [26, [4, 43], [1, 44]],
    Q: [24, [6, 19], [2, 20]],
    H: [28, [6, 15], [2, 16]],
  },
};

// Alignment-pattern centre coordinates per version (versions 1–10). Version 1
// has none; the finder patterns carry the whole registration job there.
const ALIGN_POSITIONS = {
  1: [],
  2: [6, 18],
  3: [6, 22],
  4: [6, 26],
  5: [6, 30],
  6: [6, 34],
  7: [6, 22, 38],
  8: [6, 24, 42],
  9: [6, 26, 46],
  10: [6, 28, 50],
};

// Format-string 2-bit indicator per level (distinct from any "level order").
const FORMAT_EC_BITS = { L: 0b01, M: 0b00, Q: 0b11, H: 0b10 };

const MAX_VERSION = 10;

/** Number of data codewords available for a version + level. */
function dataCodewords(version, ecLevel) {
  const [ecPerBlock, g1, g2] = EC_BLOCKS[version][ecLevel];
  let total = 0;
  const groups = g2 ? [g1, g2] : [g1];
  for (const [blocks, codewords] of groups) total += blocks * codewords;
  // (ecPerBlock is unused for the data count but validates the table shape.)
  void ecPerBlock;
  return total;
}

/** Bit width of the byte-mode character-count field for a version. */
function charCountBits(version) {
  return version <= 9 ? 8 : 16;
}

/** Smallest version (1–10) that fits `byteLength` payload bytes, or null. */
function chooseVersion(byteLength, ecLevel) {
  for (let version = 1; version <= MAX_VERSION; version += 1) {
    const capacityBits = dataCodewords(version, ecLevel) * 8;
    const neededBits = 4 + charCountBits(version) + byteLength * 8;
    if (neededBits <= capacityBits) return version;
  }
  return null;
}

/** UTF-8 encode a string to a byte array (uses TextEncoder when present). */
function utf8Bytes(text) {
  if (typeof TextEncoder !== 'undefined') return Array.from(new TextEncoder().encode(text));
  // Minimal fallback for environments without TextEncoder.
  const out = [];
  for (const ch of unescape(encodeURIComponent(text))) out.push(ch.charCodeAt(0));
  return out;
}

/** A tiny append-only bit buffer backed by a bit array. */
function createBitBuffer() {
  const bits = [];
  return {
    bits,
    put(value, length) {
      for (let i = length - 1; i >= 0; i -= 1) bits.push((value >>> i) & 1);
    },
  };
}

/** Encode the byte payload into the final data-codeword stream for a version. */
function buildDataCodewords(bytes, version, ecLevel) {
  const capacityBits = dataCodewords(version, ecLevel) * 8;
  const buffer = createBitBuffer();
  buffer.put(MODE_BYTE, 4);
  buffer.put(bytes.length, charCountBits(version));
  for (const b of bytes) buffer.put(b, 8);

  // Terminator: up to four 0-bits, but never past capacity.
  const remaining = capacityBits - buffer.bits.length;
  buffer.put(0, Math.min(4, remaining));
  // Pad to a byte boundary.
  while (buffer.bits.length % 8 !== 0) buffer.bits.push(0);

  const codewords = [];
  for (let i = 0; i < buffer.bits.length; i += 8) {
    let byte = 0;
    for (let j = 0; j < 8; j += 1) byte = (byte << 1) | buffer.bits[i + j];
    codewords.push(byte);
  }
  // Fill any leftover data capacity with the standard alternating pad bytes.
  const padBytes = [0xec, 0x11];
  const totalData = dataCodewords(version, ecLevel);
  for (let i = 0; codewords.length < totalData; i += 1) codewords.push(padBytes[i % 2]);
  return codewords;
}

/** Reed–Solomon generator polynomial of the given degree (coeff[0] = 1). */
function rsGeneratorPoly(degree) {
  let poly = [1];
  for (let i = 0; i < degree; i += 1) {
    const next = new Array(poly.length + 1).fill(0);
    for (let j = 0; j < poly.length; j += 1) {
      next[j] ^= poly[j];
      next[j + 1] ^= gfMul(poly[j], EXP[i]);
    }
    poly = next;
  }
  return poly;
}

/** Reed–Solomon EC codewords for a block of data codewords. */
function rsEcCodewords(data, ecCount) {
  const gen = rsGeneratorPoly(ecCount);
  const res = new Array(ecCount).fill(0);
  for (const d of data) {
    const factor = d ^ res[0];
    res.shift();
    res.push(0);
    if (factor !== 0) {
      for (let j = 0; j < ecCount; j += 1) res[j] ^= gfMul(gen[j + 1], factor);
    }
  }
  return res;
}

/**
 * Split the data codewords into blocks, compute EC per block, and interleave
 * both data and EC codewords into the final message stream (§8.6).
 */
function interleaveCodewords(allData, version, ecLevel) {
  const [ecPerBlock, g1, g2] = EC_BLOCKS[version][ecLevel];
  const groups = g2 ? [g1, g2] : [g1];

  const dataBlocks = [];
  const ecBlocks = [];
  let offset = 0;
  for (const [blockCount, blockData] of groups) {
    for (let b = 0; b < blockCount; b += 1) {
      const block = allData.slice(offset, offset + blockData);
      offset += blockData;
      dataBlocks.push(block);
      ecBlocks.push(rsEcCodewords(block, ecPerBlock));
    }
  }

  const result = [];
  const maxData = Math.max(...dataBlocks.map((b) => b.length));
  for (let i = 0; i < maxData; i += 1) {
    for (const block of dataBlocks) if (i < block.length) result.push(block[i]);
  }
  for (let i = 0; i < ecPerBlock; i += 1) {
    for (const block of ecBlocks) result.push(block[i]);
  }
  return result;
}

/* ------------------------------------------------------------------ */
/* Matrix construction                                                 */
/* ------------------------------------------------------------------ */
/* This mirrors ISO/IEC 18004 §6.7–§8: function patterns, then data,   */
/* then the mask + format/version info. The placement order and the    */
/* reserved-module bookkeeping match a reference encoder module-for-    */
/* module, which the unit tests pin down exactly.                       */

/** A size×size matrix of {value, reserved} cells. */
function createMatrix(size) {
  const modules = new Array(size);
  const reserved = new Array(size);
  for (let i = 0; i < size; i += 1) {
    modules[i] = new Array(size).fill(false);
    reserved[i] = new Array(size).fill(false);
  }
  const set = (row, col, value, reserve) => {
    modules[row][col] = value;
    if (reserve) reserved[row][col] = true;
  };
  return { size, modules, reserved, set };
}

function setupFinder(m, size) {
  for (const [row, col] of [
    [0, 0],
    [0, size - 7],
    [size - 7, 0],
  ]) {
    for (let r = -1; r <= 7; r += 1) {
      if (row + r <= -1 || size <= row + r) continue;
      for (let c = -1; c <= 7; c += 1) {
        if (col + c <= -1 || size <= col + c) continue;
        const dark =
          (r >= 0 && r <= 6 && (c === 0 || c === 6)) ||
          (c >= 0 && c <= 6 && (r === 0 || r === 6)) ||
          (r >= 2 && r <= 4 && c >= 2 && c <= 4);
        m.set(row + r, col + c, dark, true);
      }
    }
  }
}

function setupTiming(m, size) {
  for (let r = 8; r < size - 8; r += 1) {
    const value = r % 2 === 0;
    m.set(r, 6, value, true);
    m.set(6, r, value, true);
  }
}

/** Alignment-pattern centres, minus the three finder-occupied corners. */
function alignmentPositions(version) {
  const centers = ALIGN_POSITIONS[version];
  const last = centers.length - 1;
  const coords = [];
  for (let i = 0; i < centers.length; i += 1) {
    for (let j = 0; j < centers.length; j += 1) {
      if ((i === 0 && j === 0) || (i === 0 && j === last) || (i === last && j === 0)) {
        continue;
      }
      coords.push([centers[i], centers[j]]);
    }
  }
  return coords;
}

function setupAlignment(m, version) {
  for (const [cy, cx] of alignmentPositions(version)) {
    for (let r = -2; r <= 2; r += 1) {
      for (let c = -2; c <= 2; c += 1) {
        const dark = r === -2 || r === 2 || c === -2 || c === 2 || (r === 0 && c === 0);
        m.set(cy + r, cx + c, dark, true);
      }
    }
  }
}

/** BCH(15,5) format information for a level + mask, XORed with the mask string. */
function formatBits(ecLevel, maskPattern) {
  const data = (FORMAT_EC_BITS[ecLevel] << 3) | maskPattern;
  let rem = data << 10;
  for (let i = 14; i >= 10; i -= 1) {
    if ((rem >>> i) & 1) rem ^= 0b10100110111 << (i - 10);
  }
  return ((data << 10) | rem) ^ 0b101010000010010;
}

/** BCH(18,6) version information for versions 7+. */
function versionBits(version) {
  let rem = version << 12;
  for (let i = 17; i >= 12; i -= 1) {
    if ((rem >>> i) & 1) rem ^= 0b1111100100101 << (i - 12);
  }
  return (version << 12) | rem;
}

/**
 * Write the 15 format-info modules (two copies) plus the fixed dark module.
 * Called once with mask 0 to reserve the cells, then again per mask trial.
 */
function setupFormatInfo(m, size, ecLevel, maskPattern) {
  const bits = formatBits(ecLevel, maskPattern);
  for (let i = 0; i < 15; i += 1) {
    const on = ((bits >> i) & 1) === 1;
    // Vertical copy, down the left of the top-left finder then up the bottom-left.
    if (i < 6) m.set(i, 8, on, true);
    else if (i < 8) m.set(i + 1, 8, on, true);
    else m.set(size - 15 + i, 8, on, true);
    // Horizontal copy, along the top of the top-right finder then the top-left.
    if (i < 8) m.set(8, size - i - 1, on, true);
    else if (i < 9) m.set(8, 15 - i - 1 + 1, on, true);
    else m.set(8, 15 - i - 1, on, true);
  }
  // The module that is always dark.
  m.set(size - 8, 8, true, true);
}

function setupVersionInfo(m, size, version) {
  if (version < 7) return;
  const bits = versionBits(version);
  for (let i = 0; i < 18; i += 1) {
    const on = ((bits >> i) & 1) === 1;
    const row = Math.floor(i / 3);
    const col = (i % 3) + size - 8 - 3;
    m.set(row, col, on, true);
    m.set(col, row, on, true);
  }
}

/** Lay the interleaved message bits into the matrix in the zigzag order. */
function setupData(m, size, bits) {
  let bitIndex = 0;
  let inc = -1;
  let row = size - 1;
  for (let col = size - 1; col > 0; col -= 2) {
    if (col === 6) col -= 1; // skip the vertical timing column
    for (;;) {
      for (let c = 0; c < 2; c += 1) {
        const x = col - c;
        if (!m.reserved[row][x]) {
          m.modules[row][x] = bitIndex < bits.length && bits[bitIndex] === 1;
          bitIndex += 1;
        }
      }
      row += inc;
      if (row < 0 || row >= size) {
        row -= inc;
        inc = -inc;
        break;
      }
    }
  }
}

function maskFn(pattern, row, col) {
  switch (pattern) {
    case 0:
      return (row + col) % 2 === 0;
    case 1:
      return row % 2 === 0;
    case 2:
      return col % 3 === 0;
    case 3:
      return (row + col) % 3 === 0;
    case 4:
      return (Math.floor(row / 2) + Math.floor(col / 3)) % 2 === 0;
    case 5:
      return ((row * col) % 2) + ((row * col) % 3) === 0;
    case 6:
      return (((row * col) % 2) + ((row * col) % 3)) % 2 === 0;
    case 7:
      return (((row + col) % 2) + ((row * col) % 3)) % 2 === 0;
    default:
      return false;
  }
}

/** Penalty score of a finished matrix (§8.4), used to pick the best mask. */
function penalty(modules, size) {
  let score = 0;

  // Rule 1: runs of 5+ same-colour modules in a row/column.
  for (let i = 0; i < size; i += 1) {
    let runRow = 1;
    let runCol = 1;
    for (let j = 1; j < size; j += 1) {
      if (modules[i][j] === modules[i][j - 1]) runRow += 1;
      else {
        if (runRow >= 5) score += runRow - 2;
        runRow = 1;
      }
      if (modules[j][i] === modules[j - 1][i]) runCol += 1;
      else {
        if (runCol >= 5) score += runCol - 2;
        runCol = 1;
      }
    }
    if (runRow >= 5) score += runRow - 2;
    if (runCol >= 5) score += runCol - 2;
  }

  // Rule 2: 2×2 blocks of one colour.
  for (let r = 0; r < size - 1; r += 1) {
    for (let c = 0; c < size - 1; c += 1) {
      const v = modules[r][c];
      if (v === modules[r][c + 1] && v === modules[r + 1][c] && v === modules[r + 1][c + 1]) {
        score += 3;
      }
    }
  }

  // Rule 3: finder-like 1:1:3:1:1 patterns in rows and columns.
  const p1 = [true, false, true, true, true, false, true, false, false, false, false];
  const p2 = [false, false, false, false, true, false, true, true, true, false, true];
  const matches = (arr, off, pat) => pat.every((v, k) => arr[off + k] === v);
  for (let i = 0; i < size; i += 1) {
    for (let j = 0; j + 11 <= size; j += 1) {
      const row = modules[i];
      if (matches(row, j, p1) || matches(row, j, p2)) score += 40;
      const col = (k) => modules[j + k][i];
      const colArr = [];
      for (let k = 0; k < 11; k += 1) colArr.push(col(k));
      if (matches(colArr, 0, p1) || matches(colArr, 0, p2)) score += 40;
    }
  }

  // Rule 4: overall dark-module balance, in 5% steps away from 50%.
  let dark = 0;
  for (let r = 0; r < size; r += 1) for (let c = 0; c < size; c += 1) if (modules[r][c]) dark += 1;
  const total = size * size;
  const k = Math.abs(Math.ceil(((dark * 100) / total) / 5) - 10);
  score += k * 10;

  return score;
}

/**
 * Encode text into a QR Code matrix.
 *
 * @param {string} text
 * @param {{ecLevel?: EcLevel}} [options]
 * @returns {QrCode}
 */
export function encodeQr(text, options = {}) {
  const ecLevel = options.ecLevel || 'M';
  if (!FORMAT_EC_BITS.hasOwnProperty(ecLevel)) {
    throw new Error(`Unknown error-correction level: ${ecLevel}`);
  }
  const bytes = utf8Bytes(String(text));
  const version = chooseVersion(bytes.length, ecLevel);
  if (version === null) {
    throw new Error('Data too long for a version-10 QR code.');
  }

  const size = 17 + 4 * version;
  const data = buildDataCodewords(bytes, version, ecLevel);
  const message = interleaveCodewords(data, version, ecLevel);
  const bits = [];
  for (const byte of message) for (let i = 7; i >= 0; i -= 1) bits.push((byte >>> i) & 1);

  // Build the function patterns and data once. Format cells are reserved by
  // laying a dummy copy (mask 0); they're overwritten per mask trial below.
  const m = createMatrix(size);
  setupFinder(m, size);
  setupTiming(m, size);
  setupAlignment(m, version);
  setupFormatInfo(m, size, ecLevel, 0);
  setupVersionInfo(m, size, version);
  setupData(m, size, bits);

  const { reserved } = m;
  const base = m.modules;

  // Try every mask, re-apply the real format/version info, and keep the mask
  // with the lowest penalty (§8.8.2).
  let best = null;
  for (let pattern = 0; pattern < 8; pattern += 1) {
    const trial = createMatrix(size);
    for (let r = 0; r < size; r += 1) {
      for (let c = 0; c < size; c += 1) {
        let value = base[r][c];
        if (!reserved[r][c] && maskFn(pattern, r, c)) value = !value;
        trial.modules[r][c] = value;
      }
    }
    setupFormatInfo(trial, size, ecLevel, pattern);
    setupVersionInfo(trial, size, version);
    const score = penalty(trial.modules, size);
    if (best === null || score < best.score) best = { score, modules: trial.modules };
  }

  return { version, size, ecLevel, modules: best.modules };
}

// Exposed for tests that want to exercise the pure sub-steps directly.
export const _internals = {
  chooseVersion,
  dataCodewords,
  buildDataCodewords,
  rsGeneratorPoly,
  rsEcCodewords,
  interleaveCodewords,
  formatBits,
  versionBits,
  MAX_VERSION,
};
