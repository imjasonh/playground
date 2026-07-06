import {
  ancestors,
  basename,
  dirname,
  extname,
  joinPath,
  normalizePath,
  resolveSymlinkTarget,
  splitPath,
} from '../src/pathUtils.js';

describe('pathUtils', () => {
  test('normalizePath strips slashes and ./', () => {
    expect(normalizePath('/a/b/')).toBe('a/b');
    expect(normalizePath('./a//b')).toBe('a/b');
    expect(normalizePath('a\\b\\c')).toBe('a/b/c');
    expect(normalizePath('')).toBe('');
  });

  test('splitPath returns segments', () => {
    expect(splitPath('src/app.js')).toEqual(['src', 'app.js']);
    expect(splitPath('')).toEqual([]);
  });

  test('basename and dirname', () => {
    expect(basename('src/ui/render.js')).toBe('render.js');
    expect(dirname('src/ui/render.js')).toBe('src/ui');
    expect(dirname('README.md')).toBe('');
    expect(basename('')).toBe('');
  });

  test('extname matches node semantics', () => {
    expect(extname('index.html')).toBe('.html');
    expect(extname('archive.tar.gz')).toBe('.gz');
    expect(extname('.gitignore')).toBe('');
    expect(extname('Makefile')).toBe('');
    expect(extname('a/b/c.JS')).toBe('.js');
  });

  test('joinPath joins and normalizes', () => {
    expect(joinPath('src', 'ui', 'render.js')).toBe('src/ui/render.js');
    expect(joinPath('a/', '/b/', 'c')).toBe('a/b/c');
    expect(joinPath('', 'a')).toBe('a');
  });

  test('ancestors lists parent directories root-first', () => {
    expect(ancestors('a/b/c.txt')).toEqual(['a', 'a/b']);
    expect(ancestors('README.md')).toEqual([]);
  });

  describe('resolveSymlinkTarget', () => {
    test('resolves relative to the link’s directory', () => {
      expect(resolveSymlinkTarget('a/b/link', 'target.txt')).toBe('a/b/target.txt');
      expect(resolveSymlinkTarget('a/b/link', './target.txt')).toBe('a/b/target.txt');
      expect(resolveSymlinkTarget('link', 'target.txt')).toBe('target.txt');
    });

    test('collapses .. segments', () => {
      expect(resolveSymlinkTarget('a/b/link', '../c/file.txt')).toBe('a/c/file.txt');
      expect(resolveSymlinkTarget('a/b/c/link', '../../x')).toBe('a/x');
      expect(resolveSymlinkTarget('a/b/link', '../b/../d/e')).toBe('a/d/e');
    });

    test('returns null for empty, absolute, or repo-escaping targets', () => {
      expect(resolveSymlinkTarget('a/link', '')).toBeNull();
      expect(resolveSymlinkTarget('a/link', '   ')).toBeNull();
      expect(resolveSymlinkTarget('a/link', '/etc/hosts')).toBeNull();
      expect(resolveSymlinkTarget('a/link', '../../outside')).toBeNull();
      expect(resolveSymlinkTarget('link', '..')).toBeNull();
    });

    test('tolerates backslashes and null target', () => {
      expect(resolveSymlinkTarget('a/b/link', 'sub\\file.txt')).toBe('a/b/sub/file.txt');
      expect(resolveSymlinkTarget('a/link', null)).toBeNull();
    });
  });
});
