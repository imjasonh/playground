import { createContentSearchClient } from '../src/contentSearchClient.js';
import { buildPattern, searchContent } from '../src/contentSearch.js';

const enc = new TextEncoder();
const dec = new TextDecoder();

const FILES = {
  'README.md': '# Title\nfind the needle here\n',
  'src/app.js': 'import x;\nconst needle = 1;\nneedle();\n',
  'src/util.js': 'export const ok = true;\n',
  'logo.png': 'needle-in-a-binary-by-extension\n', // skipped by extension
};
const PATHS = Object.keys(FILES);
const readFile = (path) => Promise.resolve(enc.encode(FILES[path] ?? ''));

/** A minimal in-memory index-persistence store for the persistence tests. */
function fakeStore() {
  const map = new Map();
  return {
    available: true,
    saves: 0,
    loads: 0,
    async load(repoId, oid) {
      this.loads += 1;
      const rec = map.get(repoId);
      return rec && rec.oid === oid ? rec.data : null;
    },
    async save(repoId, oid, data) {
      this.saves += 1;
      map.set(repoId, { oid, data });
      return true;
    },
    async remove(repoId) {
      map.delete(repoId);
      return true;
    },
  };
}

/**
 * Faithful stand-in for contentSearchWorker.js that runs the real pure logic but
 * lets the test control *when* replies are delivered (so we can kill the worker
 * mid-flight deterministically).
 */
class FakeWorker {
  constructor({ autoDeliver = true } = {}) {
    this.onmessage = null;
    this.onerror = null;
    this.onmessageerror = null;
    this.terminated = false;
    this.fileMessages = 0;
    this._re = null;
    this._id = -1;
    this._dead = false;
    this._autoDeliver = autoDeliver;
    this._queue = [];
  }

  postMessage(msg) {
    if (this._dead) return;
    if (msg.type === 'begin') {
      this._re = buildPattern(msg.query, msg.options || {}).re;
      this._id = msg.id;
      return;
    }
    if (msg.type === 'file') {
      this.fileMessages += 1;
      const re = msg.id === this._id ? this._re : null;
      const matches = re ? searchContent(dec.decode(msg.bytes), re, msg.limits) : [];
      const reply = { type: 'matches', id: msg.id, reqId: msg.reqId, path: msg.path, matches };
      if (this._autoDeliver) Promise.resolve().then(() => this._deliver(reply));
      else this._queue.push(reply);
    }
  }

  _deliver(reply) {
    if (!this._dead && this.onmessage) this.onmessage({ data: reply });
  }

  flush() {
    const queued = this._queue.splice(0);
    for (const reply of queued) this._deliver(reply);
  }

  fail() {
    this._dead = true;
    if (this.onerror) this.onerror(new Error('boom'));
  }

  terminate() {
    this.terminated = true;
    this._dead = true;
  }
}

const tick = () => new Promise((r) => setTimeout(r, 0));

describe('createContentSearchClient — synchronous fallback', () => {
  test('is not using a worker and still searches + streams results', async () => {
    const client = createContentSearchClient({ useWorker: false });
    expect(client.usingWorker).toBe(false);

    const results = [];
    const summary = await client.search(PATHS, 'needle', {}, { readFile, onResult: (r) => results.push(r) });

    const paths = results.map((r) => r.path).sort();
    expect(paths).toEqual(['README.md', 'src/app.js']);
    const app = results.find((r) => r.path === 'src/app.js');
    expect(app.matches.map((m) => m.line)).toEqual([2, 3]);
    expect(summary).toMatchObject({ files: 2, matches: 3, cancelled: false });
    expect(summary.error).toBeUndefined();
  });

  test('skips files binary by extension (never reads them, even while indexing)', async () => {
    const client = createContentSearchClient({ useWorker: false });
    const reads = [];
    const read = (p) => {
      reads.push(p);
      return readFile(p);
    };
    const results = [];
    await client.search(PATHS, 'needle', {}, { readFile: read, onResult: (r) => results.push(r) });
    expect(reads).not.toContain('logo.png');
    expect(results.some((r) => r.path === 'logo.png')).toBe(false);
  });

  test('skips content that looks binary (NUL bytes)', async () => {
    const client = createContentSearchClient({ useWorker: false });
    const read = (p) => Promise.resolve(enc.encode(p === 'bin.dat' ? 'needle\u0000here' : ''));
    const results = [];
    await client.search(['bin.dat'], 'needle', {}, { readFile: read, onResult: (r) => results.push(r) });
    expect(results).toHaveLength(0);
  });

  test('skips files over the byte cap', async () => {
    const client = createContentSearchClient({ useWorker: false, maxFileBytes: 8 });
    const read = () => Promise.resolve(enc.encode('needle needle needle'));
    const summary = await client.search(['big.js'], 'needle', {}, { readFile: read });
    expect(summary.matches).toBe(0);
  });

  test('returns an error for an invalid regex (reads nothing, builds nothing)', async () => {
    const client = createContentSearchClient({ useWorker: false });
    let called = false;
    const read = (p) => {
      called = true;
      return readFile(p);
    };
    const summary = await client.search(PATHS, '(', { regex: true }, { readFile: read });
    expect(typeof summary.error).toBe('string');
    expect(called).toBe(false);
  });

  test('bounds the number of concurrent reads (during the index build)', async () => {
    let active = 0;
    let peak = 0;
    const slowRead = (path) =>
      new Promise((resolve) => {
        active += 1;
        peak = Math.max(peak, active);
        setTimeout(() => {
          active -= 1;
          resolve(enc.encode(FILES[path] ?? ''));
        }, 5);
      });
    const many = Array.from({ length: 40 }, (_, i) => `f${i}.txt`);
    const client = createContentSearchClient({ useWorker: false, concurrency: 4 });
    await client.search(many, 'zzz', {}, { readFile: slowRead });
    expect(peak).toBeLessThanOrEqual(4);
    expect(peak).toBeGreaterThan(0);
  });

  test('truncates at the total match cap', async () => {
    const client = createContentSearchClient({ useWorker: false, maxTotalMatches: 3 });
    const map = { 'a.txt': 'needle\nneedle\n', 'b.txt': 'needle\nneedle\n', 'c.txt': 'needle\nneedle\n' };
    const read = (p) => Promise.resolve(enc.encode(map[p] ?? ''));
    const summary = await client.search(Object.keys(map), 'needle', {}, { readFile: read });
    expect(summary.truncated).toBe(true);
    expect(summary.matches).toBeGreaterThanOrEqual(3);
  });

  test('scan progress advances over the candidate set and reaches total/total', async () => {
    const client = createContentSearchClient({ useWorker: false });
    const progress = [];
    // Only README.md and src/app.js contain "needle"; those are the candidates,
    // so the scan progress runs over 2 files, not the whole corpus.
    await client.search(PATHS, 'needle', {}, {
      readFile,
      onProgress: (processed, total) => progress.push([processed, total]),
    });
    expect(progress).toHaveLength(2);
    expect(progress.every(([, total]) => total === 2)).toBe(true);
    expect(progress.at(-1)).toEqual([2, 2]);
  });

  test('a newer search supersedes the previous one', async () => {
    const client = createContentSearchClient({ useWorker: false });
    const slowRead = (p) => new Promise((r) => setTimeout(() => r(enc.encode(FILES[p] ?? '')), 5));
    const first = client.search(PATHS, 'needle', {}, { readFile: slowRead });
    const second = client.search(PATHS, 'needle', {}, { readFile: slowRead });
    const [s1, s2] = await Promise.all([first, second]);
    expect(s1.cancelled).toBe(true);
    expect(s2.cancelled).toBe(false);
  });

  test('respects an abort signal', async () => {
    const client = createContentSearchClient({ useWorker: false });
    const signal = { aborted: false };
    const slowRead = (p) => new Promise((r) => setTimeout(() => r(enc.encode(FILES[p] ?? '')), 5));
    const pending = client.search(PATHS, 'needle', {}, { readFile: slowRead, signal });
    signal.aborted = true;
    const summary = await pending;
    expect(summary.cancelled).toBe(true);
  });
});

describe('createContentSearchClient — index reuse', () => {
  test('builds the index once, then only reads candidate files on later searches', async () => {
    const client = createContentSearchClient({ useWorker: false });
    const reads = [];
    const read = (p) => {
      reads.push(p);
      return readFile(p);
    };

    // First search builds the index (reads all text files) then scans candidates.
    await client.search(PATHS, 'needle', {}, { readFile: read, repoId: 'r', oid: '1' });
    const buildReads = reads.length;
    expect(buildReads).toBeGreaterThanOrEqual(3); // README, src/app.js, src/util.js

    reads.length = 0;
    // A different query on the same corpus reuses the cached index: it must only
    // read the candidate files, not re-scan the entire repo.
    await client.search(PATHS, 'const', {}, { readFile: read, repoId: 'r', oid: '1' });
    expect(reads.sort()).toEqual(['src/app.js', 'src/util.js']);
  });

  test('reports a one-time building phase, absent on reuse', async () => {
    const client = createContentSearchClient({ useWorker: false });
    const first = [];
    await client.search(PATHS, 'needle', {}, {
      readFile,
      repoId: 'r',
      oid: '1',
      onStatus: (info) => first.push(info.phase),
    });
    expect(first).toContain('building');

    const second = [];
    await client.search(PATHS, 'needle', {}, {
      readFile,
      repoId: 'r',
      oid: '1',
      onStatus: (info) => second.push(info.phase),
    });
    expect(second).not.toContain('building');
  });

  test('prepareIndex warms the index so a later search reuses it', async () => {
    const client = createContentSearchClient({ useWorker: false });
    expect(client.hasIndex('r', '1')).toBe(false);
    const ready = await client.prepareIndex({ files: PATHS, readFile, repoId: 'r', oid: '1' });
    expect(ready).toBe(true);
    expect(client.hasIndex('r', '1')).toBe(true);
  });

  test('regex queries scan every indexed file (no trigram narrowing)', async () => {
    const client = createContentSearchClient({ useWorker: false });
    const results = [];
    await client.search(PATHS, 'export|needle', { regex: true }, {
      readFile,
      repoId: 'r',
      oid: '1',
      onResult: (r) => results.push(r),
    });
    expect(results.map((r) => r.path).sort()).toEqual(['README.md', 'src/app.js', 'src/util.js']);
  });

  test('sub-trigram queries scan every indexed file', async () => {
    const client = createContentSearchClient({ useWorker: false });
    const results = [];
    await client.search(PATHS, 'x', {}, {
      readFile,
      repoId: 'r',
      oid: '1',
      onResult: (r) => results.push(r),
    });
    // "x" appears in "import x;" and in "export const ok".
    expect(results.map((r) => r.path).sort()).toEqual(['src/app.js', 'src/util.js']);
  });
});

describe('createContentSearchClient — persistence', () => {
  test('persists the built index and reuses it on a fresh client (no rebuild)', async () => {
    const store = fakeStore();
    const first = createContentSearchClient({ useWorker: false, store });
    await first.search(PATHS, 'needle', {}, { readFile, repoId: 'r', oid: '1' });
    expect(store.saves).toBe(1);

    // A brand-new client with the same store loads the persisted index instead of
    // rebuilding: it reads only candidate files, never the whole corpus.
    const second = createContentSearchClient({ useWorker: false, store });
    const reads = [];
    const read = (p) => {
      reads.push(p);
      return readFile(p);
    };
    const results = [];
    await second.search(PATHS, 'needle', {}, {
      readFile: read,
      repoId: 'r',
      oid: '1',
      onResult: (r) => results.push(r),
    });
    expect(reads.sort()).toEqual(['README.md', 'src/app.js']);
    expect(results.map((r) => r.path).sort()).toEqual(['README.md', 'src/app.js']);
    expect(store.saves).toBe(1); // no second build/save
  });

  test('rebuilds and re-persists when the oid moves (content changed)', async () => {
    const store = fakeStore();
    const client = createContentSearchClient({ useWorker: false, store });
    await client.search(PATHS, 'needle', {}, { readFile, repoId: 'r', oid: '1' });
    expect(store.saves).toBe(1);
    await client.search(PATHS, 'needle', {}, { readFile, repoId: 'r', oid: '2' });
    expect(store.saves).toBe(2);
  });
});

describe('createContentSearchClient — worker backend', () => {
  test('uses the worker: posts begin + a file per candidate, streams matches', async () => {
    const fake = new FakeWorker();
    const client = createContentSearchClient({ createWorker: () => fake });
    expect(client.usingWorker).toBe(true);

    const results = [];
    const summary = await client.search(PATHS, 'needle', {}, { readFile, onResult: (r) => results.push(r) });

    // Only the two candidates (README.md, src/app.js) reach the worker; the index
    // build reads files directly and never messages the worker.
    expect(fake.fileMessages).toBe(2);
    expect(results.map((r) => r.path).sort()).toEqual(['README.md', 'src/app.js']);
    expect(summary).toMatchObject({ files: 2, matches: 3 });
  });

  test('degrades to synchronous search if the worker dies mid-search', async () => {
    const fake = new FakeWorker({ autoDeliver: false });
    const client = createContentSearchClient({ createWorker: () => fake });

    const results = [];
    const pending = client.search(PATHS, 'needle', {}, { readFile, onResult: (r) => results.push(r) });
    await tick(); // index built, candidates read + posted; replies queued
    fake.fail(); // unblock the in-flight files → they recompute synchronously

    const summary = await pending;
    expect(client.usingWorker).toBe(false);
    expect(fake.terminated).toBe(true);
    expect(summary.matches).toBe(3);
    expect(results.map((r) => r.path).sort()).toEqual(['README.md', 'src/app.js']);
  });

  test('dispose terminates the worker', () => {
    const fake = new FakeWorker();
    const client = createContentSearchClient({ createWorker: () => fake });
    client.dispose();
    expect(fake.terminated).toBe(true);
    expect(client.usingWorker).toBe(false);
  });

  test('dispose mid-search settles the in-flight promise instead of hanging', async () => {
    const fake = new FakeWorker({ autoDeliver: false });
    const client = createContentSearchClient({ createWorker: () => fake });

    const pending = client.search(PATHS, 'needle', {}, { readFile });
    await tick(); // lanes have posted file messages and are awaiting replies
    client.dispose(); // worker gone with requests outstanding

    const summary = await pending; // must resolve — the lanes fall back to sync
    expect(fake.terminated).toBe(true);
    expect(summary.matches).toBe(3);
  });
});
