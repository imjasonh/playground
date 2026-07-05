/**
 * Tests for the pure QR encoder.
 *
 * Correctness is pinned down three ways:
 *   1. Structural invariants (size, finder patterns, determinism, limits).
 *   2. Frozen known-answer matrices, so an accidental change to placement or
 *      masking is caught even without any dependency installed.
 *   3. A bit-exact cross-check against the `qrcode` reference library (a dev
 *      dependency) across a spread of payloads and error-correction levels.
 *      This is the strongest guard: two independent spec implementations must
 *      agree module-for-module.
 */
import QRCode from 'qrcode';
import { encodeQr, _internals } from '../src/qrcode.js';

/** Render a matrix to an array of "0"/"1" row strings. */
function toRows(qr) {
  return qr.modules.map((row) => row.map((v) => (v ? '1' : '0')).join(''));
}

describe('encodeQr — structure', () => {
  test('size follows the version formula (17 + 4·version)', () => {
    const qr = encodeQr('hello', { ecLevel: 'M' });
    expect(qr.size).toBe(17 + 4 * qr.version);
    expect(qr.modules.length).toBe(qr.size);
    expect(qr.modules.every((row) => row.length === qr.size)).toBe(true);
  });

  test('cells are booleans', () => {
    const qr = encodeQr('abc');
    for (const row of qr.modules) for (const cell of row) expect(typeof cell).toBe('boolean');
  });

  test('finder patterns sit in the three corners', () => {
    const qr = encodeQr('https://example.com', { ecLevel: 'Q' });
    const { modules, size } = qr;
    // Finder signature down each centre column: dark border (0), light
    // separator ring (1), dark 3×3 core (2–4), light ring (5), dark border (6).
    for (const [r, c] of [
      [3, 3],
      [3, size - 4],
      [size - 4, 3],
    ]) {
      expect(modules[r][c]).toBe(true); // core centre
      expect(modules[r - 2][c]).toBe(false); // light separator ring
      expect(modules[r - 3][c]).toBe(true); // outer dark border
    }
  });

  test('is deterministic for the same input', () => {
    const a = toRows(encodeQr('deterministic?', { ecLevel: 'H' }));
    const b = toRows(encodeQr('deterministic?', { ecLevel: 'H' }));
    expect(a).toEqual(b);
  });

  test('defaults to error-correction level M', () => {
    expect(encodeQr('x').ecLevel).toBe('M');
    expect(encodeQr('x', {}).ecLevel).toBe('M');
  });

  test('rejects an unknown error-correction level', () => {
    expect(() => encodeQr('x', { ecLevel: 'Z' })).toThrow(/error-correction/i);
  });

  test('rejects data too large for the supported versions', () => {
    // Version 10 at level H holds 119 bytes; 200 must overflow.
    expect(() => encodeQr('z'.repeat(200), { ecLevel: 'H' })).toThrow(/too long/i);
  });

  test('picks a larger version as the payload grows', () => {
    const small = encodeQr('a', { ecLevel: 'M' }).version;
    const big = encodeQr('a'.repeat(120), { ecLevel: 'M' }).version;
    expect(big).toBeGreaterThan(small);
  });
});

describe('encodeQr — frozen known answers', () => {
  // Captured from the verified encoder; independent of the reference library.
  test('demo / L is version 1', () => {
    const qr = encodeQr('demo', { ecLevel: 'L' });
    expect(qr.version).toBe(1);
    expect(toRows(qr)).toEqual([
      '111111101111101111111',
      '100000101101101000001',
      '101110100111001011101',
      '101110100101101011101',
      '101110101000101011101',
      '100000101010001000001',
      '111111101010101111111',
      '000000001111000000000',
      '111001101111111110011',
      '011000011000000001001',
      '110111110010001000101',
      '010101010010100011000',
      '001000100010001001001',
      '000000001111011101101',
      '111111100001110110101',
      '100000101011011101000',
      '101110100011111111001',
      '101110100110000001100',
      '101110101110001000011',
      '100000101000100010000',
      '111111101100001001101',
    ]);
  });

  test('a GitHub URL / M is version 3', () => {
    const qr = encodeQr('https://github.com/octocat/Hello-World', { ecLevel: 'M' });
    expect(qr.version).toBe(3);
    expect(qr.size).toBe(29);
    // Spot-check a full round-trip via the string form to keep the anchor tight.
    expect(toRows(qr)[0]).toBe('11111110000111001111101111111');
    expect(toRows(qr)[28]).toBe('11111110100100000101001110100');
  });
});

describe('_internals — building blocks', () => {
  test('chooseVersion selects the smallest version that fits', () => {
    const { chooseVersion, dataCodewords } = _internals;
    // 16 data codewords at v1-M → 16 bytes minus overhead fits at v1.
    expect(chooseVersion(1, 'M')).toBe(1);
    expect(chooseVersion(14, 'M')).toBe(1);
    // One byte past v1-M capacity spills into v2.
    const v1mBytes = dataCodewords(1, 'M') - 2; // 4-bit mode + 8-bit count ≈ 2 bytes
    expect(chooseVersion(v1mBytes, 'M')).toBe(1);
    expect(chooseVersion(v1mBytes + 1, 'M')).toBe(2);
  });

  test('chooseVersion returns null past version 10', () => {
    expect(_internals.chooseVersion(10000, 'H')).toBeNull();
  });

  test('the Reed–Solomon generator polynomial is monic', () => {
    for (const degree of [7, 10, 13, 30]) {
      const gen = _internals.rsGeneratorPoly(degree);
      expect(gen.length).toBe(degree + 1);
      expect(gen[0]).toBe(1);
    }
  });

  test('EC codeword count matches the generator degree', () => {
    const data = [0x40, 0x64, 0x86, 0x56, 0xc6, 0xc6, 0xf0, 0xec, 0x11];
    expect(_internals.rsEcCodewords(data, 10)).toHaveLength(10);
  });

  test('data + EC codeword counts fill the symbol', () => {
    // version 3 level M: 55 data + 26 ec = 70 total codewords (1 block).
    const { dataCodewords, buildDataCodewords, interleaveCodewords } = _internals;
    expect(dataCodewords(3, 'M')).toBe(44);
    const bytes = Array.from({ length: 10 }, (_, i) => i + 1);
    const data = buildDataCodewords(bytes, 3, 'M');
    expect(data).toHaveLength(44);
    const message = interleaveCodewords(data, 3, 'M');
    expect(message).toHaveLength(44 + 26);
  });
});

describe('encodeQr — cross-check against the reference encoder', () => {
  const levels = ['L', 'M', 'Q', 'H'];
  const samples = [
    'demo',
    'a',
    'AB',
    'hello world',
    '0123456789',
    'The quick brown fox 0123456789',
    'https://github.com/octocat/Hello-World',
    '#repo=https://github.com/owner/repo&ref=branch:main&file=src/app.js&lines=10-20',
    'https://imjasonh.github.io/playground/git/#repo=https://github.com/owner/repo&ref=branch:main&file=src/app.js',
    'x'.repeat(100),
  ];

  function referenceRows(text, ecLevel) {
    // Force byte mode so both encoders make the same segmentation choice.
    const qr = QRCode.create([{ data: text, mode: 'byte' }], {
      errorCorrectionLevel: ecLevel.toLowerCase(),
    });
    const { size, data } = qr.modules;
    const rows = [];
    for (let r = 0; r < size; r += 1) {
      let row = '';
      for (let c = 0; c < size; c += 1) row += data[r * size + c] ? '1' : '0';
      rows.push(row);
    }
    return rows;
  }

  const cases = [];
  for (const text of samples) for (const ecLevel of levels) cases.push([text, ecLevel]);

  test.each(cases)('matches reference for %j @ %s', (text, ecLevel) => {
    let mine;
    try {
      mine = encodeQr(text, { ecLevel });
    } catch (err) {
      // The reference goes to version 40; ours caps at 10. Only accept a throw
      // when the payload genuinely exceeds our version-10 capacity.
      expect(err.message).toMatch(/too long/i);
      expect(_internals.chooseVersion(new TextEncoder().encode(text).length, ecLevel)).toBeNull();
      return;
    }
    expect(toRows(mine)).toEqual(referenceRows(text, ecLevel));
  });
});
