import {
  parseHash,
  encodeHashState,
  parseLines,
  formatLines,
  sameHashState,
} from '../src/hashState.js';

describe('parseLines / formatLines', () => {
  test('single line', () => {
    expect(parseLines('10')).toEqual({ start: 10, end: 10 });
    expect(formatLines({ start: 10, end: 10 })).toBe('10');
  });

  test('range', () => {
    expect(parseLines('10-20')).toEqual({ start: 10, end: 20 });
    expect(formatLines({ start: 10, end: 20 })).toBe('10-20');
  });

  test('normalizes a reversed range', () => {
    expect(parseLines('20-10')).toEqual({ start: 10, end: 20 });
  });

  test('rejects junk and zero', () => {
    expect(parseLines('')).toBeNull();
    expect(parseLines('abc')).toBeNull();
    expect(parseLines('0')).toBeNull();
    expect(parseLines('1-')).toBeNull();
    expect(parseLines('1.5')).toBeNull();
  });
});

describe('parseHash', () => {
  test('empty / no repo', () => {
    expect(parseHash('')).toBeNull();
    expect(parseHash('#')).toBeNull();
    expect(parseHash('#ref=branch:main')).toBeNull();
  });

  test('legacy bare demo', () => {
    expect(parseHash('#demo')).toEqual({ repo: 'demo' });
    expect(parseHash('demo')).toEqual({ repo: 'demo' });
  });

  test('full state', () => {
    const state = parseHash(
      '#repo=https://github.com/owner/repo&ref=branch:main&file=src/app.js&lines=10-20'
    );
    expect(state).toEqual({
      repo: 'https://github.com/owner/repo',
      ref: 'branch:main',
      file: 'src/app.js',
      lines: { start: 10, end: 20 },
    });
  });

  test('decodes percent-encoded values', () => {
    const state = parseHash('#repo=demo&file=a%20b/c.js');
    expect(state.file).toBe('a b/c.js');
  });

  test('ignores an unparseable lines value', () => {
    const state = parseHash('#repo=demo&file=x.js&lines=nope');
    expect(state).toEqual({ repo: 'demo', file: 'x.js' });
  });
});

describe('encodeHashState', () => {
  test('empty', () => {
    expect(encodeHashState(null)).toBe('');
    expect(encodeHashState({})).toBe('');
  });

  test('demo collapses to the short form', () => {
    expect(encodeHashState({ repo: 'demo' })).toBe('demo');
  });

  test('demo with a file uses the long form', () => {
    expect(encodeHashState({ repo: 'demo', file: 'src/app.js' })).toBe(
      'repo=demo&file=src/app.js'
    );
  });

  test('keeps slashes and colons readable', () => {
    const encoded = encodeHashState({
      repo: 'https://github.com/owner/repo',
      ref: 'branch:main',
      file: 'src/app.js',
      lines: { start: 5, end: 5 },
    });
    expect(encoded).toBe(
      'repo=https://github.com/owner/repo&ref=branch:main&file=src/app.js&lines=5'
    );
  });

  test('escapes ambiguous characters', () => {
    const encoded = encodeHashState({ repo: 'demo', file: 'a b&c.js' });
    expect(encoded).toBe('repo=demo&file=a%20b%26c.js');
  });
});

describe('round-trips', () => {
  test('parse(encode(state)) === state', () => {
    const states = [
      { repo: 'demo' },
      { repo: 'demo', file: 'src/app.js' },
      { repo: 'demo', ref: 'tag:v0.3.0', file: 'styles/main.css', lines: { start: 3, end: 8 } },
      { repo: 'https://example.com/x/y.git', ref: 'commit:abcdef1', file: 'a/b/c.txt', lines: { start: 1, end: 1 } },
    ];
    for (const state of states) {
      expect(parseHash(`#${encodeHashState(state)}`)).toEqual(state);
    }
  });

  test('sameHashState ignores key insertion order', () => {
    expect(
      sameHashState({ repo: 'demo', file: 'x.js' }, { file: 'x.js', repo: 'demo' })
    ).toBe(true);
    expect(sameHashState({ repo: 'demo' }, { repo: 'demo', file: 'x.js' })).toBe(false);
  });
});
