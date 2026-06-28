/**
 * @jest-environment jsdom
 *
 * Focused unit tests for GitStorage's localStorage-backed registry:
 * `_upsert` / `_touch` / `listRepos` and the persisted `{version, repos}`
 * envelope. These paths never touch the git engine (fs/git/http), so no clone
 * is performed and no engine is injected. `normalizeRegistry`'s migration logic
 * is covered separately in gitClient.test.js.
 */
import { GitStorage } from '../src/gitClient.js';

const REGISTRY_KEY = 'git-browser:repos';

function stored() {
  return JSON.parse(localStorage.getItem(REGISTRY_KEY));
}

function entry(dir, extra = {}) {
  return {
    dir,
    url: `https://example.com${dir}.git`,
    fullName: dir.replace(/^\//, ''),
    addedAt: 1,
    lastUsed: 1,
    singleBranch: true,
    depth: 0,
    corsProxy: '',
    ...extra,
  };
}

describe('GitStorage registry (localStorage)', () => {
  let storage;

  beforeEach(() => {
    localStorage.clear();
    storage = new GitStorage(); // no engine: registry paths don't need one
  });

  test('listRepos is empty when nothing is stored', () => {
    expect(storage.listRepos()).toEqual([]);
  });

  test('_upsert appends an entry and persists the versioned envelope', () => {
    storage._upsert(entry('/a'));

    const raw = stored();
    expect(raw.version).toBe(1);
    expect(raw.repos).toHaveLength(1);
    expect(raw.repos[0]).toMatchObject({ dir: '/a', fullName: 'a' });
  });

  test('_upsert replaces an existing entry for the same dir (no duplicates)', () => {
    storage._upsert(entry('/a', { fullName: 'old', lastUsed: 1 }));
    storage._upsert(entry('/a', { fullName: 'new', lastUsed: 2 }));

    const repos = storage.listRepos();
    expect(repos).toHaveLength(1);
    expect(repos[0].fullName).toBe('new');
  });

  test('listRepos returns most-recently-used first', () => {
    storage._upsert(entry('/old', { lastUsed: 10 }));
    storage._upsert(entry('/mid', { lastUsed: 20 }));
    storage._upsert(entry('/new', { lastUsed: 30 }));

    expect(storage.listRepos().map((r) => r.dir)).toEqual(['/new', '/mid', '/old']);
  });

  test('_touch bumps lastUsed for an existing entry and reorders it to the front', () => {
    // Seed tiny lastUsed values so a real Date.now() is unambiguously newer.
    storage._upsert(entry('/a', { lastUsed: 10 }));
    storage._upsert(entry('/b', { lastUsed: 20 }));

    storage._touch('/a');

    const repos = storage.listRepos();
    expect(repos[0].dir).toBe('/a');
    expect(repos[0].lastUsed).toBeGreaterThan(20);
    expect(repos[1]).toMatchObject({ dir: '/b', lastUsed: 20 }); // untouched
  });

  test('_touch is a no-op for an unknown dir', () => {
    storage._upsert(entry('/a', { lastUsed: 10 }));
    const before = JSON.stringify(stored());

    storage._touch('/missing');

    expect(JSON.stringify(stored())).toBe(before);
  });

  test('reads a legacy bare-array registry written by an older build', () => {
    localStorage.setItem(REGISTRY_KEY, JSON.stringify([entry('/legacy', { lastUsed: 5 })]));
    expect(storage.listRepos().map((r) => r.dir)).toEqual(['/legacy']);
  });

  test('tolerates a corrupt registry value', () => {
    localStorage.setItem(REGISTRY_KEY, '{not json');
    expect(storage.listRepos()).toEqual([]);
    // A subsequent write heals the stored value back to the envelope shape.
    storage._upsert(entry('/a'));
    expect(stored().version).toBe(1);
  });
});
