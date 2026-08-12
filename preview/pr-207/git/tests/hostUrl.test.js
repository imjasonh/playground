import { fileWebUrl } from '../src/hostUrl.js';

describe('fileWebUrl', () => {
  test('builds a GitHub blob URL (stripping .git)', () => {
    expect(
      fileWebUrl('https://github.com/owner/repo.git', { ref: 'main', path: 'src/app.js' })
    ).toBe('https://github.com/owner/repo/blob/main/src/app.js');
  });

  test('adds a GitHub line anchor for a single line and a range', () => {
    expect(
      fileWebUrl('https://github.com/o/r', { ref: 'main', path: 'a.js', lines: { start: 10, end: 10 } })
    ).toBe('https://github.com/o/r/blob/main/a.js#L10');
    expect(
      fileWebUrl('https://github.com/o/r', { ref: 'main', path: 'a.js', lines: { start: 10, end: 20 } })
    ).toBe('https://github.com/o/r/blob/main/a.js#L10-L20');
  });

  test('builds a GitLab URL with the /-/blob/ segment and its anchor form', () => {
    expect(
      fileWebUrl('https://gitlab.com/group/proj', {
        ref: 'main',
        path: 'a.js',
        lines: { start: 3, end: 7 },
      })
    ).toBe('https://gitlab.com/group/proj/-/blob/main/a.js#L3-7');
  });

  test('supports self-managed GitLab hosts', () => {
    expect(
      fileWebUrl('https://gitlab.example.com/g/p', { ref: 'main', path: 'a.js' })
    ).toBe('https://gitlab.example.com/g/p/-/blob/main/a.js');
  });

  test('builds a Bitbucket src URL with its line anchor', () => {
    expect(
      fileWebUrl('https://bitbucket.org/team/repo', {
        ref: 'main',
        path: 'a.js',
        lines: { start: 4, end: 9 },
      })
    ).toBe('https://bitbucket.org/team/repo/src/main/a.js#lines-4:9');
  });

  test('keeps slashes in refs and paths but encodes other characters', () => {
    expect(
      fileWebUrl('https://github.com/o/r', { ref: 'feature/dark mode', path: 'src/a b.js' })
    ).toBe('https://github.com/o/r/blob/feature/dark%20mode/src/a%20b.js');
  });

  test('uses a commit oid as the ref', () => {
    expect(
      fileWebUrl('https://github.com/o/r', { ref: 'abc1234', path: 'a.js' })
    ).toBe('https://github.com/o/r/blob/abc1234/a.js');
  });

  test('returns null for unknown hosts and missing inputs', () => {
    expect(fileWebUrl('https://example.com/o/r', { ref: 'main', path: 'a.js' })).toBeNull();
    expect(fileWebUrl(null, { ref: 'main', path: 'a.js' })).toBeNull();
    expect(fileWebUrl('https://github.com/o/r', { path: 'a.js' })).toBeNull();
    expect(fileWebUrl('https://github.com/o/r', { ref: 'main' })).toBeNull();
    expect(fileWebUrl('not a url', { ref: 'main', path: 'a.js' })).toBeNull();
    expect(fileWebUrl('https://github.com/owner', { ref: 'main', path: 'a.js' })).toBeNull();
  });
});
