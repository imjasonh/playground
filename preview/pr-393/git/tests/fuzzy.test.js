import {
  fuzzyMatch,
  fuzzyFilter,
  fuzzyFilterIndex,
  buildIndex,
  highlightSegments,
} from '../src/fuzzy.js';

describe('fuzzyMatch', () => {
  test('empty query matches everything with score 0', () => {
    expect(fuzzyMatch('', 'anything')).toEqual({ matched: true, score: 0, positions: [] });
  });

  test('subsequence matches and records positions', () => {
    const result = fuzzyMatch('app', 'src/app.js');
    expect(result.matched).toBe(true);
    expect(result.positions).toEqual([4, 5, 6]);
  });

  test('non-subsequence does not match', () => {
    expect(fuzzyMatch('xyz', 'src/app.js').matched).toBe(false);
  });

  test('is case-insensitive', () => {
    expect(fuzzyMatch('APP', 'src/app.js').matched).toBe(true);
  });

  test('contiguous and boundary matches score higher than scattered', () => {
    const contiguous = fuzzyMatch('app', 'app.js');
    const scattered = fuzzyMatch('app', 'a-p-p.js');
    expect(contiguous.score).toBeGreaterThan(scattered.score);
  });
});

describe('fuzzyFilter', () => {
  const files = [
    'src/app.js',
    'src/ui/render.js',
    'README.md',
    'styles/main.css',
    'package.json',
  ];

  test('ranks a basename match above a deep path match', () => {
    const results = fuzzyFilter('render', files);
    expect(results[0].item).toBe('src/ui/render.js');
  });

  test('returns all items for an empty query in original order', () => {
    const results = fuzzyFilter('', files);
    expect(results.map((r) => r.item)).toEqual(files);
  });

  test('respects the limit option', () => {
    const results = fuzzyFilter('s', files, { limit: 2 });
    expect(results.length).toBeLessThanOrEqual(2);
  });

  test('supports a key accessor for objects', () => {
    const items = files.map((path) => ({ path }));
    const results = fuzzyFilter('main', items, { key: (i) => i.path });
    expect(results[0].item.path).toBe('styles/main.css');
  });
});

describe('buildIndex / fuzzyFilterIndex', () => {
  const files = [
    'src/app.js',
    'src/ui/render.js',
    'README.md',
    'styles/main.css',
    'package.json',
  ];

  test('index-based filtering matches fuzzyFilter exactly', () => {
    const index = buildIndex(files);
    for (const query of ['', 'app', 'render', 'main', 's', 'zzz']) {
      expect(fuzzyFilterIndex(query, index)).toEqual(fuzzyFilter(query, files));
    }
  });

  test('precomputes lowercased targets once', () => {
    const index = buildIndex(['Src/App.JS']);
    expect(index.targets).toEqual(['Src/App.JS']);
    expect(index.lowers).toEqual(['src/app.js']);
  });

  test('supports a key accessor', () => {
    const items = files.map((path) => ({ path }));
    const index = buildIndex(items, (i) => i.path);
    const results = fuzzyFilterIndex('main', index);
    expect(results[0].item.path).toBe('styles/main.css');
  });

  test('tolerates an empty corpus', () => {
    expect(fuzzyFilterIndex('anything', buildIndex([]))).toEqual([]);
    expect(buildIndex().items).toEqual([]);
  });
});

describe('highlightSegments', () => {
  test('splits a target into matched and unmatched runs', () => {
    const segments = highlightSegments('app.js', [0, 1, 2]);
    expect(segments).toEqual([
      { text: 'app', match: true },
      { text: '.js', match: false },
    ]);
  });

  test('no positions yields a single unmatched run', () => {
    expect(highlightSegments('abc', [])).toEqual([{ text: 'abc', match: false }]);
  });
});
