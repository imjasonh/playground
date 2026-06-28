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
});
