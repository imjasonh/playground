import { GitRepoSource, normalizeRegistry } from '../src/gitClient.js';

const enc = (s) => new TextEncoder().encode(s);
const dec = new TextDecoder();

/**
 * A tiny fake of the isomorphic-git surface GitRepoSource uses. It models a
 * clone where the local refs/heads/* deliberately lag behind the
 * refs/remotes/origin/* tips (exactly the situation a read-only clone is in
 * after `fetch`), so we can pin down which ref the adapter resolves.
 */
function makeFakeGit(model) {
  model.fetchCalls = [];
  model.resolveCounts = {};
  return {
    async currentBranch() {
      return model.current;
    },
    async listBranches({ remote }) {
      return remote
        ? Object.keys(model.remoteHeads)
        : Object.keys(model.localHeads);
    },
    async resolveRef({ ref }) {
      model.resolveCounts[ref] = (model.resolveCounts[ref] || 0) + 1;
      if (ref === 'HEAD') {
        const oid = model.localHeads[model.current];
        if (oid) return oid;
        throw new Error('no HEAD');
      }
      let m = /^refs\/remotes\/origin\/(.+)$/.exec(ref);
      if (m) {
        if (model.remoteHeads[m[1]]) return model.remoteHeads[m[1]];
        throw new Error(`no remote ref ${ref}`);
      }
      m = /^refs\/heads\/(.+)$/.exec(ref);
      if (m) {
        if (model.localHeads[m[1]]) return model.localHeads[m[1]];
        throw new Error(`no local ref ${ref}`);
      }
      // A bare name resolves to a local branch, like real isomorphic-git.
      if (model.localHeads[ref]) return model.localHeads[ref];
      throw new Error(`cannot resolve ${ref}`);
    },
    async listFiles({ ref }) {
      return model.trees[ref] || [];
    },
    async readBlob({ oid, filepath }) {
      const blob = model.blobs[oid] && model.blobs[oid][filepath];
      if (!blob) throw new Error(`not found: ${filepath}`);
      return { blob, oid };
    },
    async log({ ref, depth }) {
      return (model.logs[ref] || []).slice(0, depth);
    },
    async fetch(opts) {
      model.fetchCalls.push(opts);
      if (model.onFetch) model.onFetch();
    },
  };
}

function baseModel() {
  return {
    current: 'main',
    // Local heads lag behind origin (stale, as in a fetched-but-not-merged clone).
    localHeads: { main: 'oid_local_main' },
    remoteHeads: { main: 'oid_origin_main', dev: 'oid_origin_dev' },
    trees: {
      oid_local_main: ['stale-only.txt'],
      oid_origin_main: ['README.md', 'src/index.js'],
      oid_origin_dev: ['README.md', 'src/dev.js'],
    },
    blobs: {
      oid_origin_main: { 'README.md': enc('# main') },
      oid_origin_dev: { 'README.md': enc('# dev') },
    },
    logs: {
      oid_origin_main: [
        {
          oid: 'oid_origin_main',
          commit: { message: 'main tip\n\nbody', author: { name: 'Ann', email: 'a@x', timestamp: 100 } },
        },
      ],
      oid_origin_dev: [
        {
          oid: 'oid_origin_dev',
          commit: { message: 'dev tip', author: { name: 'Dee', email: 'd@x', timestamp: 200 } },
        },
      ],
    },
  };
}

async function makeSource(model, opts = {}) {
  const source = new GitRepoSource({
    fs: {},
    http: {},
    git: makeFakeGit(model),
    dir: '/repo',
    url: 'https://example.com/acme/widget',
    fullName: 'acme/widget',
    ...opts,
  });
  await source.init();
  return source;
}

describe('GitRepoSource ref resolution', () => {
  test('init adopts the checked-out branch and stays read-only', async () => {
    const source = await makeSource(baseModel());
    expect(source.getCurrentBranch()).toBe('main');
    expect(source.readOnly).toBe(true);
    expect(source.fullName).toBe('acme/widget');
  });

  test('advertises fetch capability but not write/push', async () => {
    const source = await makeSource(baseModel());
    expect(source.capabilities).toEqual({
      read: true,
      fetch: true,
      write: false,
      push: false,
    });
  });

  test('resolves the remote-tracking ref, not the stale local head', async () => {
    // This is the Pull/Update regression guard: a read-only clone never moves
    // refs/heads/*, so reading must follow refs/remotes/origin/*.
    const source = await makeSource(baseModel());
    const files = await source.listFiles();
    expect(files.sort()).toEqual(['README.md', 'src/index.js']);
    expect(files).not.toContain('stale-only.txt');
    expect(dec.decode(await source.readFile('README.md'))).toBe('# main');
  });

  test('falls back to the local head when there is no remote ref', async () => {
    const model = baseModel();
    delete model.remoteHeads.main; // e.g. a local-only branch
    const source = await makeSource(model);
    expect((await source.listFiles()).sort()).toEqual(['stale-only.txt']);
  });

  test('caches a resolved oid until the cache is cleared', async () => {
    const model = baseModel();
    const source = await makeSource(model);
    await source.listFiles();
    await source.readFile('README.md');
    await source.log(1);
    // All three reads share one resolve of refs/remotes/origin/main.
    expect(model.resolveCounts['refs/remotes/origin/main']).toBe(1);
  });

  test('headCommit and log map raw entries to the Commit shape', async () => {
    const source = await makeSource(baseModel());
    const head = await source.headCommit();
    expect(head).toEqual({
      oid: 'oid_origin_main',
      message: 'main tip\n\nbody',
      author: { name: 'Ann', email: 'a@x' },
      timestamp: 100,
    });
    const log = await source.log(5);
    expect(log).toHaveLength(1);
    expect(log[0].oid).toBe('oid_origin_main');
  });
});

describe('GitRepoSource branches', () => {
  test('merges local + remote branches, dedupes, sorts, flags current', async () => {
    const source = await makeSource(baseModel());
    expect(await source.listBranches()).toEqual([
      { name: 'dev', current: false },
      { name: 'main', current: true },
    ]);
  });

  test('switching branches reads the new branch tip and clears the cache', async () => {
    const source = await makeSource(baseModel());
    await source.setBranch('dev');
    expect(source.getCurrentBranch()).toBe('dev');
    expect((await source.listFiles()).sort()).toEqual(['README.md', 'src/dev.js']);
    expect(dec.decode(await source.readFile('README.md'))).toBe('# dev');
  });
});

describe('GitRepoSource update', () => {
  test('fetches with the cloned scope and reports a real change', async () => {
    const model = baseModel();
    model.onFetch = () => {
      model.remoteHeads.main = 'oid_origin_main_2';
      model.trees.oid_origin_main_2 = ['README.md', 'src/index.js', 'NEW.md'];
    };
    const source = await makeSource(model, { singleBranch: true, depth: 5 });

    const result = await source.update();
    expect(result).toMatchObject({
      updated: true,
      changed: true,
      oldOid: 'oid_origin_main',
      newOid: 'oid_origin_main_2',
    });

    expect(model.fetchCalls).toHaveLength(1);
    expect(model.fetchCalls[0]).toMatchObject({
      ref: 'main',
      singleBranch: true,
      depth: 5,
      prune: false,
    });

    // The freshly fetched tip is what we now read.
    expect(await source.listFiles()).toContain('NEW.md');
  });

  test('reports changed:false when the tip does not move', async () => {
    const source = await makeSource(baseModel(), { singleBranch: true });
    const result = await source.update();
    expect(result.updated).toBe(true);
    expect(result.changed).toBe(false);
  });

  test('a full clone fetches all branches without a depth and prunes', async () => {
    const model = baseModel();
    const source = await makeSource(model, { singleBranch: false, depth: 0 });
    await source.update();
    expect(model.fetchCalls[0]).toMatchObject({
      ref: undefined,
      singleBranch: false,
      depth: undefined,
      prune: true,
    });
  });
});

describe('normalizeRegistry', () => {
  test('reads the versioned envelope', () => {
    const repos = [{ dir: '/a', fullName: 'a' }, { dir: '/b' }];
    expect(normalizeRegistry({ version: 1, repos })).toEqual(repos);
  });

  test('migrates a legacy bare array', () => {
    const repos = [{ dir: '/a' }];
    expect(normalizeRegistry(repos)).toEqual(repos);
  });

  test('drops entries without a usable dir', () => {
    const parsed = {
      version: 1,
      repos: [{ dir: '/keep' }, { fullName: 'no-dir' }, null, { dir: '' }, 42],
    };
    expect(normalizeRegistry(parsed)).toEqual([{ dir: '/keep' }]);
  });

  test('returns [] for junk', () => {
    expect(normalizeRegistry(null)).toEqual([]);
    expect(normalizeRegistry(undefined)).toEqual([]);
    expect(normalizeRegistry(42)).toEqual([]);
    expect(normalizeRegistry({})).toEqual([]);
    expect(normalizeRegistry({ repos: 'nope' })).toEqual([]);
  });
});
