import { diffLines, splitLines } from '../src/diff.js';

describe('splitLines', () => {
  test('empty string is no lines', () => {
    expect(splitLines('')).toEqual([]);
  });

  test('drops the trailing newline\'s empty line', () => {
    expect(splitLines('a\nb\n')).toEqual(['a', 'b']);
    expect(splitLines('a\nb')).toEqual(['a', 'b']);
  });

  test('keeps internal blank lines', () => {
    expect(splitLines('a\n\nb\n')).toEqual(['a', '', 'b']);
  });
});

describe('diffLines', () => {
  test('identical text is all context', () => {
    const { rows, added, removed } = diffLines('a\nb\nc\n', 'a\nb\nc\n');
    expect(added).toBe(0);
    expect(removed).toBe(0);
    expect(rows.every((r) => r.type === 'context')).toBe(true);
    expect(rows.map((r) => r.text)).toEqual(['a', 'b', 'c']);
  });

  test('a changed middle line is a del followed by an add', () => {
    const { rows, added, removed } = diffLines('a\nb\nc\n', 'a\nB\nc\n');
    expect(added).toBe(1);
    expect(removed).toBe(1);
    expect(rows).toEqual([
      { type: 'context', text: 'a', oldLine: 1, newLine: 1 },
      { type: 'del', text: 'b', oldLine: 2, newLine: null },
      { type: 'add', text: 'B', oldLine: null, newLine: 2 },
      { type: 'context', text: 'c', oldLine: 3, newLine: 3 },
    ]);
  });

  test('pure additions and removals number correctly', () => {
    const added = diffLines('a\n', 'a\nb\nc\n');
    expect(added.added).toBe(2);
    expect(added.removed).toBe(0);
    expect(added.rows.filter((r) => r.type === 'add').map((r) => r.newLine)).toEqual([2, 3]);

    const removed = diffLines('a\nb\nc\n', 'a\n');
    expect(removed.removed).toBe(2);
    expect(removed.added).toBe(0);
  });

  test('a file created from empty is all additions', () => {
    const { rows, added } = diffLines('', 'x\ny\n');
    expect(added).toBe(2);
    expect(rows.every((r) => r.type === 'add')).toBe(true);
  });

  test('refuses to diff inputs beyond the cell budget', () => {
    const big = Array.from({ length: 50 }, (_, i) => `l${i}`).join('\n');
    const res = diffLines(big, big.toUpperCase(), { maxCells: 100 });
    expect(res.truncated).toBe(true);
    expect(res.rows).toEqual([]);
  });
});
