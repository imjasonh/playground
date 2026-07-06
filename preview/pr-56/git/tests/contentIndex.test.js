import {
  extractTrigrams,
  queryTrigrams,
  buildTrigramIndex,
  candidatePaths,
  serializeIndex,
  deserializeIndex,
  INDEX_FORMAT_VERSION,
} from '../src/contentIndex.js';

describe('extractTrigrams', () => {
  test('yields distinct lowercased trigrams', () => {
    const grams = [...extractTrigrams('Abcabc')];
    // 'abcabc' -> abc, bca, cab, abc(dup) -> {abc, bca, cab}
    expect(new Set(grams)).toEqual(new Set(['abc', 'bca', 'cab']));
  });

  test('is empty for text shorter than a trigram', () => {
    expect([...extractTrigrams('')].length).toBe(0);
    expect([...extractTrigrams('ab')].length).toBe(0);
    expect([...extractTrigrams('abc')]).toEqual(['abc']);
  });

  test('accumulates into a provided set (per-file reuse)', () => {
    const set = new Set();
    extractTrigrams('abc', set);
    extractTrigrams('bcd', set);
    expect(set).toEqual(new Set(['abc', 'bcd']));
  });
});

describe('queryTrigrams', () => {
  test('returns the trigrams of the query', () => {
    expect(new Set(queryTrigrams('needle'))).toEqual(
      new Set(['nee', 'eed', 'edl', 'dle']),
    );
  });

  test('is empty for a sub-trigram query', () => {
    expect(queryTrigrams('ab')).toEqual([]);
  });
});

describe('buildTrigramIndex + candidatePaths', () => {
  const entries = [
    { path: 'a.txt', text: 'the needle in the haystack' },
    { path: 'b.txt', text: 'no matches here at all' },
    { path: 'c.txt', text: 'another needle nearby' },
  ];
  const index = buildTrigramIndex(entries);

  test('narrows to files that contain all of the query trigrams', () => {
    expect(candidatePaths(index, 'needle').sort()).toEqual(['a.txt', 'c.txt']);
  });

  test('is case-insensitive (candidates are a superset; scan confirms case)', () => {
    expect(candidatePaths(index, 'NEEDLE').sort()).toEqual(['a.txt', 'c.txt']);
  });

  test('returns nothing when a required trigram is absent from every file', () => {
    expect(candidatePaths(index, 'zzz')).toEqual([]);
  });

  test('returns every path for a sub-trigram query (cannot narrow)', () => {
    expect(candidatePaths(index, 'a').sort()).toEqual(['a.txt', 'b.txt', 'c.txt']);
  });

  test('a candidate can be a false positive (trigrams present but not contiguous)', () => {
    const idx = buildTrigramIndex([{ path: 'p', text: 'xabcy zbcdw' }]);
    // 'abcd' -> trigrams abc, bcd; both exist separately in the text, so 'p' is a
    // candidate even though 'abcd' never appears. The scan is what rejects it.
    expect(candidatePaths(idx, 'abcd')).toEqual(['p']);
  });

  test('ignores malformed entries', () => {
    const idx = buildTrigramIndex([null, { text: 'no path' }, { path: 'ok', text: 'needle' }]);
    expect(idx.paths).toEqual(['ok']);
  });
});

describe('serialize / deserialize', () => {
  const index = buildTrigramIndex([
    { path: 'a.txt', text: 'hello world' },
    { path: 'b.txt', text: 'goodbye world' },
  ]);

  test('round-trips to an equivalent index', () => {
    const restored = deserializeIndex(serializeIndex(index));
    expect(restored.paths).toEqual(index.paths);
    expect(candidatePaths(restored, 'world').sort()).toEqual(['a.txt', 'b.txt']);
    expect(candidatePaths(restored, 'hello')).toEqual(['a.txt']);
  });

  test('serialized form is plain JSON with a version', () => {
    const obj = serializeIndex(index);
    expect(obj.version).toBe(INDEX_FORMAT_VERSION);
    expect(Array.isArray(obj.paths)).toBe(true);
    const clone = JSON.parse(JSON.stringify(obj));
    expect(deserializeIndex(clone).paths).toEqual(index.paths);
  });

  test('rejects missing, corrupt, or wrong-version payloads', () => {
    expect(deserializeIndex(null)).toBeNull();
    expect(deserializeIndex({})).toBeNull();
    expect(deserializeIndex({ version: 999, paths: [], trigrams: {} })).toBeNull();
    expect(deserializeIndex({ version: INDEX_FORMAT_VERSION, paths: 'no', trigrams: {} })).toBeNull();
  });
});
