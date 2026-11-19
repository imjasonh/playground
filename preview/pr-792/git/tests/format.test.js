import {
  commitSummary,
  countNewCommits,
  formatBytes,
  newCommitsPhrase,
  relativeTime,
  shortOid,
} from '../src/format.js';

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

describe('countNewCommits', () => {
  const log = [{ oid: 'd' }, { oid: 'c' }, { oid: 'b' }, { oid: 'a' }];

  test('counts commits newer than the old tip (exact when found)', () => {
    expect(countNewCommits(log, 'b')).toEqual({ count: 2, exact: true });
    expect(countNewCommits(log, 'd')).toEqual({ count: 0, exact: true });
  });

  test('is inexact when the old tip is not in the (capped) list', () => {
    expect(countNewCommits(log, 'zzz')).toEqual({ count: 4, exact: false });
    // A null old tip (couldn't resolve before fetch) is never "found".
    expect(countNewCommits(log, null)).toEqual({ count: 4, exact: false });
  });

  test('tolerates a non-array', () => {
    expect(countNewCommits(undefined, 'x')).toEqual({ count: 0, exact: false });
  });
});

describe('newCommitsPhrase', () => {
  test('pluralizes and marks inexact counts', () => {
    expect(newCommitsPhrase({ count: 1, exact: true })).toBe('1 new commit');
    expect(newCommitsPhrase({ count: 3, exact: true })).toBe('3 new commits');
    expect(newCommitsPhrase({ count: 5, exact: false })).toBe('5+ new commits');
  });

  test('is empty when there is nothing new', () => {
    expect(newCommitsPhrase({ count: 0, exact: true })).toBe('');
    expect(newCommitsPhrase()).toBe('');
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
