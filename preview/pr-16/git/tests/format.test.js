import { commitSummary, formatBytes, relativeTime, shortOid } from '../src/format.js';

describe('formatBytes', () => {
  test('formats across units', () => {
    expect(formatBytes(0)).toBe('0 B');
    expect(formatBytes(512)).toBe('512 B');
    expect(formatBytes(1536)).toBe('1.5 KB');
    expect(formatBytes(1048576)).toBe('1 MB');
  });

  test('handles invalid input', () => {
    expect(formatBytes(-1)).toBe('');
    expect(formatBytes(NaN)).toBe('');
  });
});

describe('shortOid', () => {
  test('truncates to default 7 chars', () => {
    expect(shortOid('9f1c0a7e2b5d4c8a')).toBe('9f1c0a7');
    expect(shortOid('abc', 7)).toBe('abc');
    expect(shortOid('')).toBe('');
  });
});

describe('commitSummary', () => {
  test('returns the first line', () => {
    expect(commitSummary('Add feature\n\nLong body')).toBe('Add feature');
    expect(commitSummary('')).toBe('');
  });
});

describe('relativeTime', () => {
  const now = 1_000_000_000 * 1000; // fixed "now" in ms

  test('reports recent times', () => {
    expect(relativeTime(1_000_000_000 - 10, now)).toBe('just now');
    expect(relativeTime(1_000_000_000 - 120, now)).toBe('2 minutes ago');
    expect(relativeTime(1_000_000_000 - 3600, now)).toBe('1 hour ago');
  });

  test('reports days and years', () => {
    expect(relativeTime(1_000_000_000 - 2 * 86400, now)).toBe('2 days ago');
    expect(relativeTime(1_000_000_000 - 2 * 365 * 86400, now)).toBe('2 years ago');
  });

  test('handles future and invalid', () => {
    expect(relativeTime(1_000_000_000 + 500, now)).toBe('in the future');
    expect(relativeTime(NaN, now)).toBe('');
  });
});
