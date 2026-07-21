import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import {
  STORAGE_KEY,
  resolvePrintApiBase,
  savePrintApiBase,
  sculptureSizeMm,
  fitsSlantBed,
  requestQuote,
  formatPrice,
} from '../src/quote.js';

function memoryStorage(seed = {}) {
  const map = new Map(Object.entries(seed));
  return {
    getItem: (k) => (map.has(k) ? map.get(k) : null),
    setItem: (k, v) => map.set(k, String(v)),
    removeItem: (k) => map.delete(k),
  };
}

describe('resolvePrintApiBase', () => {
  it('prefers ?printApi= and persists it', () => {
    const storage = memoryStorage();
    const base = resolvePrintApiBase({
      search: '?printApi=https://life-print.example.workers.dev/',
      storage,
    });
    assert.equal(base, 'https://life-print.example.workers.dev');
    assert.equal(storage.getItem(STORAGE_KEY), 'https://life-print.example.workers.dev');
  });

  it('falls back to localStorage then default', () => {
    const storage = memoryStorage({ [STORAGE_KEY]: 'https://stored.example' });
    assert.equal(resolvePrintApiBase({ search: '', storage }), 'https://stored.example');
    assert.equal(
      resolvePrintApiBase({ search: '', storage: memoryStorage(), fallback: 'https://fb.example/' }),
      'https://fb.example',
    );
  });
});

describe('savePrintApiBase', () => {
  it('stores cleaned URL and clears on empty', () => {
    const storage = memoryStorage();
    assert.equal(savePrintApiBase('https://x.example/', storage), 'https://x.example');
    assert.equal(storage.getItem(STORAGE_KEY), 'https://x.example');
    savePrintApiBase('', storage);
    assert.equal(storage.getItem(STORAGE_KEY), null);
  });
});

describe('bed fit', () => {
  it('computes mm extents including base layer on Z', () => {
    assert.deepEqual(
      sculptureSizeMm({ width: 24, height: 24, depth: 24, cellMm: 4 }),
      { x: 96, y: 96, z: 100 },
    );
  });

  it('accepts default life-lab size and rejects oversize Z', () => {
    assert.equal(fitsSlantBed({ x: 96, y: 96, z: 100 }), true);
    assert.equal(fitsSlantBed({ x: 176, y: 176, z: 180 }), true);
    assert.equal(fitsSlantBed({ x: 176, y: 176, z: 221 }), false);
  });
});

describe('requestQuote', () => {
  it('posts STL bytes and returns JSON price', async () => {
    const calls = [];
    const fetchImpl = async (url, opts) => {
      calls.push({ url, opts });
      return {
        ok: true,
        status: 200,
        async text() {
          return JSON.stringify({ price: 5.2, currency: 'USD', triangles: 12 });
        },
      };
    };
    const stl = new Uint8Array([1, 2, 3]);
    const quote = await requestQuote('https://life-print.example/', stl, fetchImpl);
    assert.equal(quote.price, 5.2);
    assert.equal(calls[0].url, 'https://life-print.example/quote');
    assert.equal(calls[0].opts.method, 'POST');
    assert.equal(calls[0].opts.headers['Content-Type'], 'model/stl');
    assert.equal(calls[0].opts.body, stl);
  });

  it('surfaces Worker error messages', async () => {
    const fetchImpl = async () => ({
      ok: false,
      status: 503,
      async text() {
        return JSON.stringify({ error: 'SLANT_API_KEY is not configured' });
      },
    });
    await assert.rejects(
      () => requestQuote('https://life-print.example', new Uint8Array([1]), fetchImpl),
      /SLANT_API_KEY/,
    );
  });
});

describe('formatPrice', () => {
  it('formats USD', () => {
    const s = formatPrice(5.2, 'USD');
    assert.match(s, /5\.20/);
  });
});
