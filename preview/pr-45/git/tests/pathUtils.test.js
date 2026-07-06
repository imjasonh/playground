import {
  ancestors,
  basename,
  dirname,
  extname,
  joinPath,
  normalizePath,
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
});
