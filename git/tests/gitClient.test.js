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
  test('init adopts the checked-out branch; editable, pushable with a url', async () => {
    const source = await makeSource(baseModel());
    expect(source.getCurrentBranch()).toBe('main');
    expect(source.readOnly).toBe(false);
    expect(source.canPush).toBe(true);
    expect(source.fullName).toBe('acme/widget');
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

/* ------------------------------------------------------------------ */
/* Write surface: edit -> stage -> commit -> push                      */
/* ------------------------------------------------------------------ */

function bytesEq(a, b) {
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i += 1) if (a[i] !== b[i]) return false;
  return true;
}

/** A starting point with one commit (`c1`) checked out on `main`. */
function writableModel() {
  return {
    current: 'main',
    headOid: 'c1',
    localHeads: { main: 'c1' },
    remoteHeads: { main: 'c1' },
    commitTrees: { c1: { 'README.md': '# hi', 'src/a.js': 'a' } },
    trees: { c1: ['README.md', 'src/a.js'] },
    logs: { c1: [{ oid: 'c1', commit: { message: 'init', author: { name: 'I', email: 'i@x', timestamp: 1 } } }] },
    workdir: null,
    index: null,
    checkedOut: null,
    pushCalls: [],
    commitSeq: 0,
    pushResult: null,
    ancestors: {},
  };
}

/** Fake lightning-fs whose working directory is a shared Map on the model. */
function makeFakeFs(model) {
  const strip = (full) => full.replace(/^\/repo\//, '');
  return {
    promises: {
      async writeFile(full, bytes) {
        model.workdir.set(strip(full), bytes);
      },
      async readFile(full) {
        const p = strip(full);
        if (!model.workdir || !model.workdir.has(p)) {
          const err = new Error(`ENOENT: ${p}`);
          err.code = 'ENOENT';
          throw err;
        }
        return model.workdir.get(p);
      },
      async unlink(full) {
        if (model.workdir) model.workdir.delete(strip(full));
      },
      async mkdir() {
        /* directories are implicit in the Map model */
      },
    },
  };
}

/**
 * Fake isomorphic-git that shares a working tree + index with makeFakeFs so the
 * adapter's checkout / add / remove / statusMatrix / commit / push sequence can
 * be exercised end to end without a real repo.
 */
function makeWritableGit(model) {
  const tree = (oid) => model.commitTrees[oid] || {};
  return {
    async currentBranch() {
      return model.current;
    },
    async listBranches({ remote }) {
      return remote ? Object.keys(model.remoteHeads) : Object.keys(model.localHeads);
    },
    async resolveRef({ ref }) {
      if (ref === 'HEAD') return model.localHeads[model.current];
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
      if (model.localHeads[ref]) return model.localHeads[ref];
      throw new Error(`cannot resolve ${ref}`);
    },
    async listFiles({ ref }) {
      return model.trees[ref] || [];
    },
    async readBlob({ oid, filepath }) {
      const t = tree(oid);
      if (!(filepath in t)) throw new Error(`not found: ${filepath}`);
      return { blob: enc(t[filepath]), oid };
    },
    async log({ ref, depth }) {
      return (model.logs[ref] || []).slice(0, depth);
    },
    async writeRef({ ref, value }) {
      const m = /^refs\/heads\/(.+)$/.exec(ref);
      if (m) model.localHeads[m[1]] = value;
    },
    async checkout({ ref }) {
      const oid = model.localHeads[ref];
      model.current = ref;
      model.headOid = oid;
      model.checkedOut = ref;
      const t = tree(oid);
      model.workdir = new Map(Object.entries(t).map(([p, c]) => [p, enc(c)]));
      model.index = new Map(model.workdir);
    },
    async add({ filepath }) {
      model.index.set(filepath, model.workdir.get(filepath));
    },
    async remove({ filepath }) {
      model.index.delete(filepath);
    },
    async statusMatrix() {
      const headTree = tree(model.headOid);
      const paths = new Set([
        ...Object.keys(headTree),
        ...model.workdir.keys(),
        ...model.index.keys(),
      ]);
      const rows = [];
      for (const p of paths) {
        const inHead = p in headTree;
        const head = inHead ? 1 : 0;
        let workdir = 0;
        if (model.workdir.has(p)) {
          workdir = inHead && bytesEq(model.workdir.get(p), enc(headTree[p])) ? 1 : 2;
        }
        let stage = 0;
        if (model.index.has(p)) {
          stage = inHead && bytesEq(model.index.get(p), enc(headTree[p])) ? 1 : 2;
        }
        rows.push([p, head, workdir, stage]);
      }
      rows.sort((a, b) => a[0].localeCompare(b[0]));
      return rows;
    },
    async commit({ message, author }) {
      const newOid = `commit_${++model.commitSeq}`;
      const newTree = {};
      for (const [p, bytes] of model.index.entries()) newTree[p] = dec.decode(bytes);
      const parentOid = model.headOid;
      model.commitTrees[newOid] = newTree;
      model.trees[newOid] = Object.keys(newTree);
      model.localHeads[model.current] = newOid;
      model.headOid = newOid;
      model.logs[newOid] = [{ oid: newOid, commit: { message, author } }, ...(model.logs[parentOid] || [])];
      return newOid;
    },
    async isDescendent({ oid, ancestor }) {
      return (model.ancestors[oid] || []).includes(ancestor);
    },
    async push(opts) {
      model.pushCalls.push({
        ref: opts.ref,
        remote: opts.remote,
        force: opts.force,
        auth: opts.onAuth(),
      });
      return model.pushResult || { ok: true, error: null };
    },
  };
}

async function makeWritableSource(model, opts = {}) {
  const source = new GitRepoSource({
    fs: makeFakeFs(model),
    http: {},
    git: makeWritableGit(model),
    dir: '/repo',
    url: 'https://example.com/acme/widget',
    fullName: 'acme/widget',
    ...opts,
  });
  await source.init();
  return source;
}

describe('GitRepoSource editing', () => {
  test('canPush tracks whether there is a remote url', async () => {
    expect((await makeWritableSource(writableModel())).canPush).toBe(true);
    expect((await makeWritableSource(writableModel(), { url: null })).canPush).toBe(false);
  });

  test('first edit checks out the branch and stages the change', async () => {
    const model = writableModel();
    const source = await makeWritableSource(model);

    await source.writeFile('README.md', '# edited');

    expect(model.checkedOut).toBe('main');
    // The local head was reset to the displayed (remote-tracking) commit.
    expect(model.localHeads.main).toBe('c1');
    expect(await source.status()).toEqual([{ path: 'README.md', status: 'modified' }]);
    // Reads now reflect the uncommitted working-tree edit.
    expect(dec.decode(await source.readFile('README.md'))).toBe('# edited');
  });

  test('new and deleted files surface in status and the file list', async () => {
    const model = writableModel();
    const source = await makeWritableSource(model);

    await source.writeFile('docs/new.md', 'x');
    await source.deleteFile('src/a.js');

    const status = await source.status();
    expect(status).toContainEqual({ path: 'docs/new.md', status: 'new' });
    expect(status).toContainEqual({ path: 'src/a.js', status: 'deleted' });

    const files = await source.listFiles();
    expect(files).toContain('docs/new.md');
    expect(files).not.toContain('src/a.js');
  });

  test('commit advances the local head, and reads then follow it', async () => {
    const model = writableModel();
    const source = await makeWritableSource(model);
    await source.writeFile('README.md', '# v2');

    const { oid } = await source.commit({
      message: 'Update readme',
      author: { name: 'Dev', email: 'd@x' },
    });

    expect(oid).toBe('commit_1');
    expect(model.localHeads.main).toBe('commit_1');
    expect(await source.status()).toEqual([]);

    const head = await source.headCommit();
    expect(head.oid).toBe('commit_1');
    expect(head.message).toBe('Update readme');
    expect((await source.log(5)).map((c) => c.oid)).toEqual(['commit_1', 'c1']);
  });

  test('commit rejects an empty tree and a blank message', async () => {
    const source = await makeWritableSource(writableModel());
    await expect(source.commit({ message: 'noop' })).rejects.toThrow(/nothing to commit/i);
    await source.writeFile('a.txt', '1');
    await expect(source.commit({ message: '   ' })).rejects.toThrow(/message/i);
  });

  test('push sends the current branch with token auth and reports success', async () => {
    const model = writableModel();
    const source = await makeWritableSource(model);

    const res = await source.push({ token: 'ghp_secret' });
    expect(res.ok).toBe(true);
    expect(model.pushCalls).toHaveLength(1);
    expect(model.pushCalls[0]).toMatchObject({ ref: 'main', remote: 'origin' });
    // A bare token authenticates as the username (GitHub-style).
    expect(model.pushCalls[0].auth).toEqual({ username: 'ghp_secret', password: '' });
  });

  test('push uses username + token when a username is supplied', async () => {
    const model = writableModel();
    const source = await makeWritableSource(model);
    await source.push({ token: 'tok', username: 'octocat' });
    expect(model.pushCalls[0].auth).toEqual({ username: 'octocat', password: 'tok' });
  });

  test('push surfaces a remote rejection and refuses without a remote', async () => {
    const model = writableModel();
    model.pushResult = { ok: false, error: 'non-fast-forward' };
    const source = await makeWritableSource(model);
    await expect(source.push({ token: 't' })).rejects.toThrow(/non-fast-forward/);

    const noRemote = await makeWritableSource(writableModel(), { url: null });
    await expect(noRemote.push({ token: 't' })).rejects.toThrow(/no remote/i);
  });

  test('reopening adopts local commits that are ahead of origin', async () => {
    // Simulate a repo whose local head carries a commit (c2) not on origin (c1).
    const model = writableModel();
    model.localHeads.main = 'c2';
    model.commitTrees.c2 = { 'README.md': '# committed locally', 'src/a.js': 'a' };
    model.trees.c2 = ['README.md', 'src/a.js'];
    model.logs.c2 = [
      { oid: 'c2', commit: { message: 'local work', author: { name: 'Me', email: 'm@x' } } },
      ...model.logs.c1,
    ];
    model.ancestors = { c2: ['c1'] }; // c2 descends from the remote tip c1

    const source = await makeWritableSource(model);
    // Reads follow the local head, not the stale remote-tracking tip.
    expect(dec.decode(await source.readFile('README.md'))).toBe('# committed locally');
    expect((await source.headCommit()).oid).toBe('c2');
    expect((await source.log(5)).map((c) => c.oid)).toEqual(['c2', 'c1']);
  });

  test('does not adopt a local head that is merely behind origin', async () => {
    // Plain fetched-but-not-merged clone: origin (c2) is ahead of local (c1).
    const model = writableModel();
    model.remoteHeads.main = 'c2';
    model.commitTrees.c2 = { 'README.md': '# newer on origin', 'src/a.js': 'a' };
    model.trees.c2 = ['README.md', 'src/a.js'];
    model.logs.c2 = [
      { oid: 'c2', commit: { message: 'origin work', author: { name: 'O', email: 'o@x' } } },
      ...model.logs.c1,
    ];
    model.ancestors = { c2: ['c1'] }; // local c1 is NOT a descendant of remote c2

    const source = await makeWritableSource(model);
    expect(dec.decode(await source.readFile('README.md'))).toBe('# newer on origin');
    expect((await source.headCommit()).oid).toBe('c2');
  });
});
