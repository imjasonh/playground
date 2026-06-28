import { InMemoryRepoSource } from '../src/repoSource.js';
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
  test('reports metadata and default branch, and is editable but not pushable', () => {
    const s = makeSource();
    expect(s.fullName).toBe('acme/widget');
    expect(s.getCurrentBranch()).toBe('main');
    // In-memory sources are fully editable locally but have no remote.
    expect(s.readOnly).toBe(false);
    expect(s.canPush).toBe(false);
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

  test('headCommit and log come from newest-first commits', async () => {
    const s = makeSource();
    const head = await s.headCommit();
    expect(head.oid).toBe('aaa');
    const log = await s.log(1);
    expect(log).toHaveLength(1);
    expect(log[0].message).toBe('second');
  });

  test('update is a no-op for in-memory data', async () => {
    const s = makeSource();
    await expect(s.update()).resolves.toEqual({ updated: false, changed: false });
  });
});

describe('InMemoryRepoSource editing', () => {
  test('starts with a clean working tree', async () => {
    const s = makeSource();
    await expect(s.status()).resolves.toEqual([]);
  });

  test('writeFile modifies an existing file and shows it as modified', async () => {
    const s = makeSource();
    await s.writeFile('README.md', '# Changed');
    expect(decoder.decode(await s.readFile('README.md'))).toBe('# Changed');
    expect(await s.status()).toEqual([{ path: 'README.md', status: 'modified' }]);
  });

  test('writeFile creates a new (nested) file shown as new and listed', async () => {
    const s = makeSource();
    await s.writeFile('docs/guide.md', 'hello');
    expect((await s.listFiles())).toContain('docs/guide.md');
    expect(await s.status()).toEqual([{ path: 'docs/guide.md', status: 'new' }]);
  });

  test('deleteFile removes a file and shows it as deleted', async () => {
    const s = makeSource();
    await s.deleteFile('README.md');
    expect(await s.listFiles()).not.toContain('README.md');
    expect(await s.status()).toEqual([{ path: 'README.md', status: 'deleted' }]);
    await expect(s.deleteFile('nope.txt')).rejects.toThrow(/not found/i);
  });

  test('rewriting a file back to its original content clears the change', async () => {
    const s = makeSource();
    const original = decoder.decode(await s.readFile('README.md'));
    await s.writeFile('README.md', '# temporary');
    expect(await s.status()).toHaveLength(1);
    await s.writeFile('README.md', original);
    expect(await s.status()).toEqual([]);
  });

  test('commit records a newest-first commit and clears status', async () => {
    const s = makeSource();
    await s.writeFile('NEW.md', 'x');
    const { oid } = await s.commit({
      message: 'Add NEW.md',
      author: { name: 'Dev', email: 'dev@x' },
    });
    expect(oid).toMatch(/^[0-9a-f]{40}$/);
    expect(await s.status()).toEqual([]);
    const head = await s.headCommit();
    expect(head.oid).toBe(oid);
    expect(head.message).toBe('Add NEW.md');
    expect(head.author).toEqual({ name: 'Dev', email: 'dev@x' });
  });

  test('commit rejects an empty tree or a blank message', async () => {
    const s = makeSource();
    await expect(s.commit({ message: 'nothing changed' })).rejects.toThrow(/nothing to commit/i);
    await s.writeFile('a.txt', '1');
    await expect(s.commit({ message: '   ' })).rejects.toThrow(/message/i);
  });

  test('edits are isolated per branch', async () => {
    const s = makeSource();
    await s.writeFile('README.md', '# main edit');
    await s.setBranch('dev');
    // The dev branch is untouched and clean.
    expect(decoder.decode(await s.readFile('README.md'))).toBe('# Widget dev');
    expect(await s.status()).toEqual([]);
  });

  test('cannot be pushed', async () => {
    const s = makeSource();
    await expect(s.push()).rejects.toThrow(/local-only/i);
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
});
