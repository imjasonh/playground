import { buildFileTree, countFiles, flattenVisible, sortNodes } from '../src/fileTree.js';

describe('buildFileTree', () => {
  const tree = buildFileTree([
    'src/app.js',
    'src/ui/render.js',
    'README.md',
    'src/storage.js',
    'styles/main.css',
  ]);

  test('nests files under their directories', () => {
    const top = tree.children.map((n) => `${n.type}:${n.name}`);
    // directories first (src, styles), then files (README.md)
    expect(top).toEqual(['dir:src', 'dir:styles', 'file:README.md']);
  });

  test('directory paths are full repo-relative paths', () => {
    const src = tree.children.find((n) => n.name === 'src');
    const ui = src.children.find((n) => n.name === 'ui');
    expect(ui.path).toBe('src/ui');
    expect(ui.children[0].path).toBe('src/ui/render.js');
  });

  test('sorts directories before files alphabetically', () => {
    const src = tree.children.find((n) => n.name === 'src');
    expect(src.children.map((n) => n.name)).toEqual(['ui', 'app.js', 'storage.js']);
  });

  test('counts leaf files', () => {
    expect(countFiles(tree)).toBe(5);
  });

  test('ignores empty input', () => {
    expect(buildFileTree([]).children).toEqual([]);
    expect(buildFileTree(undefined).children).toEqual([]);
  });
});

describe('flattenVisible', () => {
  const tree = buildFileTree(['src/app.js', 'src/ui/render.js', 'README.md']);

  test('hides children of collapsed directories', () => {
    const rows = flattenVisible(tree, new Set());
    expect(rows.map((r) => r.node.name)).toEqual(['src', 'README.md']);
  });

  test('reveals children of expanded directories with depth', () => {
    const rows = flattenVisible(tree, new Set(['src']));
    expect(rows.map((r) => `${r.depth}:${r.node.name}`)).toEqual([
      '0:src',
      '1:ui',
      '1:app.js',
      '0:README.md',
    ]);
  });
});

describe('sortNodes', () => {
  test('is case-insensitive and dirs first', () => {
    const nodes = [
      { name: 'Zebra', type: 'file' },
      { name: 'apple', type: 'file' },
      { name: 'lib', type: 'dir' },
    ];
    expect(sortNodes(nodes).map((n) => n.name)).toEqual(['lib', 'apple', 'Zebra']);
  });
});
