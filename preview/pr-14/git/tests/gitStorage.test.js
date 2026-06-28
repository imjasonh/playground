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

/** A tiny in-memory POSIX-ish FS implementing the slice GitStorage uses. */
function createMemFs() {
  const nodes = new Map([['/', 'dir']]); // path -> 'dir' | 'file'
  const norm = (p) => String(p).replace(/\/+/g, '/').replace(/(.)\/$/, '$1') || '/';
  const childrenOf = (dir) => {
    const d = norm(dir);
    const prefix = d === '/' ? '/' : `${d}/`;
    const names = new Set();
    for (const key of nodes.keys()) {
      if (key === d || !key.startsWith(prefix)) continue;
      const rest = key.slice(prefix.length);
      if (rest && !rest.includes('/')) names.add(rest);
    }
    return [...names];
  };
  const fail = (code) => Object.assign(new Error(code), { code });
  const promises = {
    async readdir(p) {
      if (nodes.get(norm(p)) !== 'dir') throw fail('ENOENT');
      return childrenOf(p);
    },
    async mkdir(p) {
      if (nodes.has(norm(p))) throw fail('EEXIST');
      nodes.set(norm(p), 'dir');
    },
    async rmdir(p) {
      if (childrenOf(p).length) throw fail('ENOTEMPTY');
      nodes.delete(norm(p));
    },
    async unlink(p) {
      if (!nodes.has(norm(p))) throw fail('ENOENT');
      nodes.delete(norm(p));
    },
    async writeFile(p) {
      nodes.set(norm(p), 'file');
    },
    async lstat(p) {
      if (!nodes.has(norm(p))) throw fail('ENOENT');
      const type = nodes.get(norm(p));
      return { isDirectory: () => type === 'dir', isFile: () => type === 'file' };
    },
  };
  promises.stat = promises.lstat;
  return { nodes, promises };
}

/** Create `path` (and ancestor dirs) in a mem FS; the leaf gets `type`. */
function mkTree(fs, path, type = 'dir') {
  const parts = String(path).split('/').filter(Boolean);
  let cur = '';
  parts.forEach((part, i) => {
    cur += `/${part}`;
    fs.nodes.set(cur, i === parts.length - 1 ? type : 'dir');
  });
}

/** Make `dir` look like a cloned repo (working dir + .git + a file). */
function makeRepo(fs, dir) {
  mkTree(fs, dir);
  mkTree(fs, `${dir}/.git`);
  mkTree(fs, `${dir}/README.md`, 'file');
}

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

describe('GitStorage.repair (FS vs registry reconciliation)', () => {
  beforeEach(() => localStorage.clear());

  test('removes repo dirs absent from the registry, keeps the known ones', async () => {
    const fs = createMemFs();
    const storage = new GitStorage({ fs, git: {}, http: {} });

    makeRepo(fs, '/github.com/acme/keep');
    makeRepo(fs, '/github.com/acme/orphan');
    storage._upsert(entry('/github.com/acme/keep'));

    const removed = await storage.repair();

    expect(removed).toEqual(['/github.com/acme/orphan']);
    expect(fs.nodes.has('/github.com/acme/keep/.git')).toBe(true);
    expect(fs.nodes.has('/github.com/acme/orphan')).toBe(false);
    // The shared owner container is still in use by "keep", so it survives.
    expect(fs.nodes.has('/github.com/acme')).toBe(true);
  });

  test('prunes empty container dirs left by a failed clone (no .git)', async () => {
    const fs = createMemFs();
    const storage = new GitStorage({ fs, git: {}, http: {} });
    mkTree(fs, '/gitlab.com/foo/bar'); // dir chain but never populated

    const removed = await storage.repair();

    expect(removed).toEqual([]); // not a repo, so not reported as an orphan repo
    expect(fs.nodes.has('/gitlab.com')).toBe(false); // empty chain pruned away
  });

  test('with an empty registry, every repo dir is an orphan', async () => {
    const fs = createMemFs();
    const storage = new GitStorage({ fs, git: {}, http: {} });
    makeRepo(fs, '/github.com/a/one');
    makeRepo(fs, '/github.com/b/two');

    const removed = await storage.repair();

    expect(removed.sort()).toEqual(['/github.com/a/one', '/github.com/b/two']);
    expect(fs.nodes.has('/github.com')).toBe(false);
  });
});

describe('GitStorage.clone failure cleanup', () => {
  beforeEach(() => localStorage.clear());

  test('removes the half-written dir and records nothing when clone throws', async () => {
    const fs = createMemFs();
    const git = {
      clone: async () => {
        throw new Error('network boom');
      },
    };
    const storage = new GitStorage({ fs, git, http: {} });

    await expect(
      storage.clone({ url: 'https://x/y.git', dir: '/x/y', fullName: 'x/y', singleBranch: true })
    ).rejects.toThrow(/network boom/);

    expect(fs.nodes.has('/x/y')).toBe(false);
    expect(storage.listRepos()).toEqual([]);
  });

  test('records the repo when clone succeeds', async () => {
    const fs = createMemFs();
    const git = {
      clone: async ({ dir }) => makeRepo(fs, dir),
    };
    const storage = new GitStorage({ fs, git, http: {} });

    // open() builds a GitRepoSource and calls init(); stub the bits it needs.
    git.currentBranch = async () => 'main';

    await storage.clone({
      url: 'https://x/y.git',
      dir: '/x/y',
      fullName: 'x/y',
      singleBranch: true,
    });

    expect(storage.listRepos().map((r) => r.dir)).toEqual(['/x/y']);
    expect(fs.nodes.has('/x/y/.git')).toBe(true);
  });
});
