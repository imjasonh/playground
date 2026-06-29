/**
 * Integration test for the *real* clone/fetch path — the biggest gap called
 * out in future-work.md. CI can't reach external git hosts, so instead we
 * stand up a local smart-HTTP git server (`git http-backend`) on 127.0.0.1,
 * serving a throwaway repository, and drive GitStorage.clone / open / update
 * through the genuine isomorphic-git network protocol with no external egress.
 *
 * GitStorage normally lazy-loads the vendored browser bundles + lightning-fs;
 * here we inject Node's `fs` and isomorphic-git's Node `git`/`http`, which is
 * exactly the injection seam the constructor exposes.
 *
 * If `git http-backend` isn't available, the suite skips rather than fails, so
 * it never breaks unrelated environments. Standard CI runners ship it.
 */
import fs from 'node:fs';
import { mkdtempSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import git from 'isomorphic-git';
import http from 'isomorphic-git/http/node';
import { GitStorage } from '../src/gitClient.js';
import {
  hasGitHttpBackend,
  createServedRepo,
  startGitHttpServer,
  SUBMODULE_OID,
} from './helpers/gitHttpServer.js';

const decoder = new TextDecoder();

/** Minimal in-memory localStorage so GitStorage's registry round-trips in Node. */
function memoryLocalStorage() {
  const map = new Map();
  return {
    getItem: (k) => (map.has(k) ? map.get(k) : null),
    setItem: (k, v) => map.set(k, String(v)),
    removeItem: (k) => map.delete(k),
    clear: () => map.clear(),
  };
}

const describeMaybe = hasGitHttpBackend() ? describe : describe.skip;

describeMaybe('GitStorage real clone/fetch over local git http-backend', () => {
  let repo;
  let server;
  let cloneRoot;
  let dir;
  let storage;
  let source;
  const hadLocalStorage = 'localStorage' in globalThis;
  const prevLocalStorage = globalThis.localStorage;

  beforeAll(async () => {
    globalThis.localStorage = memoryLocalStorage();
    repo = createServedRepo();
    server = await startGitHttpServer({ projectRoot: repo.root });

    cloneRoot = mkdtempSync(join(tmpdir(), 'git-clone-'));
    dir = join(cloneRoot, 'clone');

    storage = new GitStorage({ fs, git, http });
    source = await storage.clone({
      url: `${server.url}/repo.git`,
      dir,
      fullName: 'acme/widget',
      depth: 0,
      singleBranch: false,
      corsProxy: '',
    });
  }, 60000);

  afterAll(async () => {
    if (server) await server.close();
    if (repo) repo.cleanup();
    if (cloneRoot) rmSync(cloneRoot, { recursive: true, force: true });
    if (hadLocalStorage) globalThis.localStorage = prevLocalStorage;
    else delete globalThis.localStorage;
  });

  test('clone produces a working read-only source on the default branch', async () => {
    expect(source.fullName).toBe('acme/widget');
    expect(source.readOnly).toBe(true);
    expect(source.getCurrentBranch()).toBe('main');

    await source.setBranch('main');
    expect((await source.listFiles()).sort()).toEqual(['README.md', 'src/index.js']);
    expect(decoder.decode(await source.readFile('README.md'))).toMatch(/# Widget/);
  });

  test('lists both branches fetched from the remote', async () => {
    const names = (await source.listBranches()).map((b) => b.name);
    expect(names).toContain('main');
    expect(names).toContain('dev');
  });

  test('headCommit and log come from the real history', async () => {
    await source.setBranch('main');
    const head = await source.headCommit();
    expect(head.oid).toMatch(/^[0-9a-f]{40}$/);
    expect(head.message).toMatch(/Initial commit/);

    const log = await source.log(10);
    expect(log.length).toBeGreaterThanOrEqual(1);
    expect(log[0].author.name).toBe('Integration Tester');
  });

  test('switching branches reads the other branch tip', async () => {
    await source.setBranch('dev');
    expect((await source.listFiles()).sort()).toEqual([
      'README.md',
      'src/dev.js',
      'src/index.js',
    ]);
  });

  test('browses the tree at an arbitrary commit (detached HEAD)', async () => {
    await source.setBranch('main');
    const [head] = await source.log(1);
    expect(head.oid).toMatch(/^[0-9a-f]{40}$/);

    await source.setRef({ type: 'commit', name: head.oid });
    expect(source.getCurrentRef()).toEqual({ type: 'commit', name: head.oid });
    expect((await source.listFiles()).sort()).toEqual(['README.md', 'src/index.js']);

    // A short oid resolves to the same tree.
    await source.setRef({ type: 'commit', name: head.oid.slice(0, 8) });
    expect((await source.listFiles()).sort()).toEqual(['README.md', 'src/index.js']);

    await source.setBranch('main');
  });

  test('lists and browses tags fetched from the remote', async () => {
    const tags = await source.listTags();
    expect(tags).toContain('v1.0');

    await source.setRef({ type: 'tag', name: 'v1.0' });
    expect(source.getCurrentRef()).toEqual({ type: 'tag', name: 'v1.0' });
    // v1.0 points at the initial commit (before src/dev.js existed on dev).
    expect((await source.listFiles()).sort()).toEqual(['README.md', 'src/index.js']);

    await source.setBranch('main');
  });

  test('fileLog returns only commits that touched a given file', async () => {
    await source.setBranch('dev');
    // src/dev.js was introduced on the dev branch in a single commit.
    const devLog = await source.fileLog('src/dev.js');
    expect(devLog.length).toBe(1);
    expect(devLog[0].message).toMatch(/Add dev module/);

    // README.md existed from the initial commit.
    const readmeLog = await source.fileLog('README.md');
    expect(readmeLog.length).toBeGreaterThanOrEqual(1);
    await source.setBranch('main');
  });

  test('changedFiles diffs two refs by walking their trees', async () => {
    // main -> dev introduced src/dev.js (added), nothing else changed.
    const changes = await source.changedFiles('main', 'dev');
    const byPath = Object.fromEntries(changes.map((c) => [c.path, c.status]));
    expect(byPath['src/dev.js']).toBe('added');
    expect(Object.keys(byPath)).not.toContain('README.md');
  });

  test('changedFiles of a commit vs its parent (and the root commit)', async () => {
    await source.setBranch('main');
    const log = await source.log(10);
    const root = log[log.length - 1];
    expect(root.parent).toEqual([]);

    // The root commit compared against an empty base: everything added.
    const rootChanges = await source.changedFiles(null, { type: 'commit', name: root.oid });
    expect(rootChanges.map((c) => c.path).sort()).toEqual(['README.md', 'src/index.js']);
    expect(rootChanges.every((c) => c.status === 'added')).toBe(true);
  });

  test('classifies a real symlink and submodule from the tree', async () => {
    await source.setBranch('special');
    const files = await source.listFiles();
    // Both the symlink (a blob) and the submodule (a gitlink) are listed.
    expect(files).toContain('latest.js');
    expect(files).toContain('vendor/widget');

    // The symlink resolves to the path it points at.
    const link = await source.entryMeta('latest.js');
    expect(link.kind).toBe('symlink');
    expect(link.target).toBe('src/index.js');

    // The submodule reports its pinned oid and URL (from .gitmodules).
    const sub = await source.entryMeta('vendor/widget');
    expect(sub.kind).toBe('submodule');
    expect(sub.oid).toBe(SUBMODULE_OID);
    expect(sub.url).toBe('https://github.com/acme/widget.git');

    // An ordinary file is just a file.
    expect((await source.entryMeta('README.md')).kind).toBe('file');

    await source.setBranch('main');
  });

  test('the clone is recorded in the registry and can be reopened', async () => {
    expect(storage.listRepos().map((r) => r.dir)).toContain(dir);

    const reopened = await storage.open(dir);
    expect(reopened.fullName).toBe('acme/widget');
    expect((await reopened.listFiles()).length).toBeGreaterThan(0);
  });

  test('update fetches a new commit pushed to the remote', async () => {
    await source.setBranch('main');
    const before = await source.listFiles();
    expect(before).not.toContain('NEW.md');

    repo.addCommitOnMain('NEW.md', '# new file\n', 'Add NEW.md');

    const result = await source.update();
    expect(result.updated).toBe(true);
    expect(result.changed).toBe(true);

    // The remote-tracking ref advanced, so reads now see the new tip.
    expect(await source.listFiles()).toContain('NEW.md');
  });
});
