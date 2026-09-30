import {
  InMemoryRepoSource,
  capabilitiesOf,
  isReadOnly,
} from '../src/repoSource.js';
import { createDemoSource } from '../src/demoRepo.js';

function makeSource() {
  return new InMemoryRepoSource({
    fullName: 'acme/widget',
    defaultBranch: 'main',
    branches: {
      main: {
        files: { 'README.md': '# Widget', 'src/index.js': 'export default 1;\n' },
        commits: [
          { oid: 'aaa', message: 'second', author: { name: 'A', email: 'a@x' }, timestamp: 2 },
          { oid: 'bbb', message: 'first', author: { name: 'B', email: 'b@x' }, timestamp: 1 },
        ],
      },
      dev: {
        files: { 'README.md': '# Widget dev', 'src/index.js': '', 'src/extra.js': '' },
        commits: [{ oid: 'ccc', message: 'dev', author: { name: 'C', email: 'c@x' }, timestamp: 3 }],
      },
    },
  });
}

const decoder = new TextDecoder();

describe('InMemoryRepoSource', () => {
  test('reports metadata and default branch', () => {
    const s = makeSource();
    expect(s.fullName).toBe('acme/widget');
    expect(s.getCurrentBranch()).toBe('main');
    expect(s.readOnly).toBe(true);
  });

  test('advertises read-only capabilities (no fetch/write/push)', () => {
    const s = makeSource();
    expect(s.capabilities).toEqual({
      read: true,
      fetch: false,
      write: false,
      push: false,
    });
  });

  test('lists branches with the current flag', async () => {
    const s = makeSource();
    const branches = await s.listBranches();
    expect(branches).toEqual([
      { name: 'main', current: true },
      { name: 'dev', current: false },
    ]);
  });

  test('lists and reads files for the current branch', async () => {
    const s = makeSource();
    expect((await s.listFiles()).sort()).toEqual(['README.md', 'src/index.js']);
    expect(decoder.decode(await s.readFile('README.md'))).toBe('# Widget');
  });

  test('switching branches changes the file set', async () => {
    const s = makeSource();
    await s.setBranch('dev');
    expect(s.getCurrentBranch()).toBe('dev');
    expect((await s.listFiles()).sort()).toEqual(['README.md', 'src/extra.js', 'src/index.js']);
    expect(decoder.decode(await s.readFile('README.md'))).toBe('# Widget dev');
  });

  test('throws for unknown branch and missing file', async () => {
    const s = makeSource();
    await expect(s.setBranch('nope')).rejects.toThrow(/Unknown branch/);
    await expect(s.readFile('missing.txt')).rejects.toThrow(/not found/i);
  });

  test('classifies symlinks and submodules via entryMeta', async () => {
    const s = new InMemoryRepoSource({
      defaultBranch: 'main',
      branches: {
        main: {
          files: {
            'README.md': '# Widget',
            'docs/latest.md': '../README.md', // symlink: content is the target
          },
          symlinks: { 'docs/latest.md': '../README.md' },
          submodules: {
            'vendor/widget': {
              name: 'widget',
              url: 'https://github.com/acme/widget.git',
              oid: 'c0ffee00',
            },
          },
          commits: [{ oid: 'm1', message: 'm' }],
        },
      },
    });

    // Submodules have no blob, but are still listed so they're navigable.
    expect((await s.listFiles()).sort()).toEqual([
      'README.md',
      'docs/latest.md',
      'vendor/widget',
    ]);

    expect(await s.entryMeta('README.md')).toEqual({ kind: 'file' });
    expect(await s.entryMeta('docs/latest.md')).toEqual({
      kind: 'symlink',
      target: '../README.md',
    });
    expect(await s.entryMeta('vendor/widget')).toEqual({
      kind: 'submodule',
      name: 'widget',
      url: 'https://github.com/acme/widget.git',
      oid: 'c0ffee00',
    });
  });

  test('the demo source exposes a symlink and a submodule', async () => {
    const demo = createDemoSource();
    const files = await demo.listFiles();
    expect(files).toContain('docs/latest.md');
    expect(files).toContain('vendor/widget');

    expect(await demo.entryMeta('docs/latest.md')).toMatchObject({ kind: 'symlink' });
    expect(await demo.entryMeta('vendor/widget')).toMatchObject({
      kind: 'submodule',
      url: 'https://github.com/acme/widget.git',
    });
    expect(await demo.entryMeta('README.md')).toEqual({ kind: 'file' });
  });

  test('getCurrentRef and setRef cover branches, tags, and commits', async () => {
    const s = new InMemoryRepoSource({
      defaultBranch: 'main',
      branches: {
        main: { files: { 'a.txt': 'A' }, commits: [{ oid: 'm1', message: 'm' }] },
        dev: { files: { 'a.txt': 'A', 'b.txt': 'B' }, commits: [{ oid: 'd1', message: 'd' }] },
      },
      tags: { 'v1.0': 'dev' },
    });

    expect(s.getCurrentRef()).toEqual({ type: 'branch', name: 'main' });
    expect(await s.listTags()).toEqual(['v1.0']);

    await s.setRef({ type: 'tag', name: 'v1.0' });
    expect(s.getCurrentRef()).toEqual({ type: 'tag', name: 'v1.0' });
    expect((await s.listFiles()).sort()).toEqual(['a.txt', 'b.txt']);
    // A tag is not a branch, so no branch is flagged current.
    expect((await s.listBranches()).every((b) => !b.current)).toBe(true);

    await s.setRef({ type: 'commit', name: 'd1' });
    expect(s.getCurrentRef()).toEqual({ type: 'commit', name: 'd1' });
    expect((await s.listFiles()).sort()).toEqual(['a.txt', 'b.txt']);

    await expect(s.setRef({ type: 'tag', name: 'nope' })).rejects.toThrow(/Unknown tag/);
  });

  test('headCommit and log come from newest-first commits', async () => {
    const s = makeSource();
    const head = await s.headCommit();
    expect(head.oid).toBe('aaa');
    const log = await s.log(1);
    expect(log).toHaveLength(1);
    expect(log[0].message).toBe('second');
  });

  test('fileLog filters by annotated changed paths, else falls back to full log', async () => {
    const annotated = new InMemoryRepoSource({
      branches: {
        main: {
          files: { 'a.txt': 'A', 'b.txt': 'B' },
          commits: [
            { oid: 'c2', message: 'edit a', changed: ['a.txt'] },
            { oid: 'c1', message: 'init', changed: ['a.txt', 'b.txt'] },
          ],
        },
      },
    });
    expect((await annotated.fileLog('a.txt')).map((c) => c.oid)).toEqual(['c2', 'c1']);
    expect((await annotated.fileLog('b.txt')).map((c) => c.oid)).toEqual(['c1']);

    // Unannotated commits: fall back to the full history.
    const plain = makeSource();
    expect((await plain.fileLog('README.md')).length).toBe(2);
  });

  test('blame attributes lines using per-commit fileVersions', async () => {
    const s = new InMemoryRepoSource({
      branches: {
        main: {
          files: { 'app.js': 'import x;\nconst a = 1;\nuse(a);\n' },
          fileVersions: {
            'app.js': [
              { oid: 'c3', content: 'import x;\nconst a = 1;\nuse(a);\n' },
              { oid: 'c2', content: 'const a = 1;\nuse(a);\n' },
              { oid: 'c1', content: 'const a = 1;\n' },
            ],
          },
          commits: [
            { oid: 'c3', message: 'add import', author: { name: 'A', email: 'a@x' }, timestamp: 3 },
            { oid: 'c2', message: 'use a', author: { name: 'B', email: 'b@x' }, timestamp: 2 },
            { oid: 'c1', message: 'init', author: { name: 'C', email: 'c@x' }, timestamp: 1 },
          ],
        },
      },
    });
    const rows = await s.blame('app.js');
    expect(rows.map((r) => r.line)).toEqual(['import x;', 'const a = 1;', 'use(a);']);
    // c3 introduced the import, c1 the declaration, c2 the use().
    expect(rows.map((r) => r.commit.oid)).toEqual(['c3', 'c1', 'c2']);
    // Full commit metadata rides along so the UI can label and link each chip.
    expect(rows[0].commit).toMatchObject({ oid: 'c3', message: 'add import', author: { name: 'A' } });
  });

  test('blame returns null for a file without per-commit history', async () => {
    const s = makeSource();
    expect(await s.blame('README.md')).toBeNull();
  });

  test('log derives linear parent oids; the root has none', async () => {
    const s = makeSource();
    const log = await s.log();
    expect(log[0]).toMatchObject({ oid: 'aaa', parent: ['bbb'] });
    expect(log[1]).toMatchObject({ oid: 'bbb', parent: [] });
  });

  test('changedFiles reports add/remove/modify between branches', async () => {
    const s = makeSource();
    const changes = await s.changedFiles('main', 'dev');
    const byPath = Object.fromEntries(changes.map((c) => [c.path, c.status]));
    // dev adds src/extra.js, modifies README.md and src/index.js vs main.
    expect(byPath['src/extra.js']).toBe('added');
    expect(byPath['README.md']).toBe('modified');
    expect(byPath['src/index.js']).toBe('modified');
  });

  test('changedFiles against a null base marks everything added', async () => {
    const s = makeSource();
    const changes = await s.changedFiles(null, 'main');
    expect(changes.every((c) => c.status === 'added')).toBe(true);
    expect(changes.map((c) => c.path).sort()).toEqual(['README.md', 'src/index.js']);
  });

  test('update is a no-op for in-memory data', async () => {
    const s = makeSource();
    await expect(s.update()).resolves.toEqual({ updated: false, changed: false });
  });

  test('checkForUpdates reports nothing to poll for in-memory data', async () => {
    const s = makeSource();
    await expect(s.checkForUpdates()).resolves.toEqual({
      supported: false,
      hasUpdates: false,
      localOid: null,
      remoteOid: null,
    });
  });
});

describe('capabilitiesOf / isReadOnly', () => {
  test('fills omitted flags with the read-only baseline', () => {
    expect(capabilitiesOf({})).toEqual({
      read: true,
      fetch: false,
      write: false,
      push: false,
    });
    expect(capabilitiesOf(null)).toEqual({
      read: true,
      fetch: false,
      write: false,
      push: false,
    });
  });

  test('honors explicit flags, including read:false', () => {
    expect(capabilitiesOf({ capabilities: { fetch: true } }).fetch).toBe(true);
    expect(capabilitiesOf({ capabilities: { read: false } }).read).toBe(false);
  });

  test('isReadOnly is true unless write or push is granted', () => {
    expect(isReadOnly({ read: true, fetch: true, write: false, push: false })).toBe(true);
    expect(isReadOnly({ write: true })).toBe(false);
    expect(isReadOnly({ push: true })).toBe(false);
  });
});

describe('createDemoSource', () => {
  test('exposes two branches that differ', async () => {
    const demo = createDemoSource();
    const names = (await demo.listBranches()).map((b) => b.name);
    expect(names).toContain('main');
    expect(names).toContain('feature/dark-mode');

    const mainFiles = await demo.listFiles('main');
    expect(mainFiles).not.toContain('src/theme.js');

    await demo.setBranch('feature/dark-mode');
    const darkFiles = await demo.listFiles();
    expect(darkFiles).toContain('src/theme.js');
    expect(darkFiles).toContain('styles/theme.css');
  });

  test('provides readable file content and history', async () => {
    const demo = createDemoSource();
    const readme = decoder.decode(await demo.readFile('README.md'));
    expect(readme).toMatch(/Tasklite/);
    const log = await demo.log();
    expect(log.length).toBeGreaterThan(0);
    expect(log[0]).toHaveProperty('oid');
  });

  test('blames src/app.js across its commits, matching the shown file', async () => {
    const demo = createDemoSource();
    const rows = await demo.blame('src/app.js');
    expect(rows).not.toBeNull();

    // Blame reproduces exactly the lines the viewer renders for the file.
    const shown = decoder.decode(await demo.readFile('src/app.js')).replace(/\n$/, '');
    expect(rows.map((r) => r.line).join('\n')).toBe(shown);

    // Spot-check unambiguous lines, each introduced by a different commit.
    const commitFor = new Map(rows.map((r) => [r.line, r.commit]));
    expect(commitFor.get("import { loadTasks, saveTasks } from './storage.js';").message).toMatch(
      /Persist tasks/
    );
    expect(commitFor.get("import { renderList } from './ui/render.js';").message).toMatch(
      /Render task list/
    );
    expect(commitFor.get("const list = document.getElementById('list');").message).toMatch(
      /Initial commit/
    );
    expect(commitFor.get('  saveTasks(tasks);').message).toMatch(/Persist tasks/);
  });

  test('blame is unavailable for demo files without snapshots', async () => {
    const demo = createDemoSource();
    expect(await demo.blame('README.md')).toBeNull();
  });
});
