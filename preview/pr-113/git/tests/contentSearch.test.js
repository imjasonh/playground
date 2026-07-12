import { buildPattern, searchContent, escapeRegExp } from '../src/contentSearch.js';

const SAMPLE = `import { loadTasks } from './storage.js';
const KEY = 'tasklite.tasks';
export function loadTasks() {
  return JSON.parse(localStorage.getItem(KEY)) || [];
}
`;

describe('escapeRegExp', () => {
  test('escapes regex metacharacters', () => {
    expect(escapeRegExp('a.b*c(')).toBe('a\\.b\\*c\\(');
    const re = new RegExp(escapeRegExp('a.b'));
    expect(re.test('aXb')).toBe(false);
    expect(re.test('a.b')).toBe(true);
  });
});

describe('buildPattern', () => {
  test('empty query compiles to null (nothing to search), no error', () => {
    expect(buildPattern('')).toEqual({ re: null, error: null });
  });

  test('plain query is a literal, case-insensitive substring by default', () => {
    const { re } = buildPattern('loadtasks');
    expect(re.flags).toContain('i');
    expect(re.test('LoadTasks')).toBe(true);
  });

  test('caseSensitive drops the i flag', () => {
    const { re } = buildPattern('loadTasks', { caseSensitive: true });
    expect(re.flags).not.toContain('i');
    expect('loadTasks function'.match(re)).not.toBeNull();
    expect('LOADTASKS'.match(buildPattern('loadTasks', { caseSensitive: true }).re)).toBeNull();
  });

  test('plain query escapes metacharacters', () => {
    const { re } = buildPattern('a.b');
    expect(re.test('axb')).toBe(false);
    expect(re.test('a.b')).toBe(true);
  });

  test('regex mode honors the pattern', () => {
    const { re } = buildPattern('load\\w+', { regex: true });
    expect('loadTasks'.match(re)[0]).toBe('loadTasks');
  });

  test('invalid regex returns an error message, not a throw', () => {
    const { re, error } = buildPattern('(', { regex: true });
    expect(re).toBeNull();
    expect(typeof error).toBe('string');
    expect(error.length).toBeGreaterThan(0);
  });

  test('always global so searchContent can find every span', () => {
    expect(buildPattern('x').re.global).toBe(true);
  });
});

describe('searchContent', () => {
  test('returns one entry per matching line with 1-based positions', () => {
    const { re } = buildPattern('loadTasks');
    const hits = searchContent(SAMPLE, re);
    expect(hits.map((h) => h.line)).toEqual([1, 3]);
    expect(hits[0].column).toBe(10); // "loadTasks" inside the import on line 1
    expect(hits[0].text).toContain('loadTasks');
  });

  test('records every match span on a line for highlighting', () => {
    const { re } = buildPattern('a');
    const hits = searchContent('banana', re);
    expect(hits).toHaveLength(1);
    expect(hits[0].ranges).toEqual([
      [1, 2],
      [3, 4],
      [5, 6],
    ]);
  });

  test('empty / no-regex inputs yield no matches', () => {
    expect(searchContent('', buildPattern('x').re)).toEqual([]);
    expect(searchContent('text', null)).toEqual([]);
  });

  test('respects maxMatches (lines)', () => {
    const text = Array.from({ length: 100 }, (_, i) => `line ${i} hit`).join('\n');
    const hits = searchContent(text, buildPattern('hit').re, { maxMatches: 5 });
    expect(hits).toHaveLength(5);
  });

  test('caps spans per line', () => {
    const { re } = buildPattern('a');
    const hits = searchContent('a'.repeat(100), re, { maxPerLine: 10 });
    expect(hits[0].ranges).toHaveLength(10);
  });

  test('clamps a very long line and the ranges past the cut', () => {
    const line = `${'x'.repeat(20)}NEEDLE${'y'.repeat(1000)}NEEDLE`;
    const hits = searchContent(line, buildPattern('NEEDLE').re, { maxLineLength: 30 });
    expect(hits[0].text).toHaveLength(30);
    // Only the first NEEDLE (at col 21) survives the 30-char cut.
    expect(hits[0].ranges).toEqual([[20, 26]]);
  });

  test('terminates on a zero-width (regex) match', () => {
    const { re } = buildPattern('x*', { regex: true });
    // Should not hang; produces bounded results.
    const hits = searchContent('abc', re, { maxPerLine: 5 });
    expect(Array.isArray(hits)).toBe(true);
  });
});
