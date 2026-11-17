import { isLfsPointer, parseLfsPointer } from '../src/lfs.js';

const enc = (s) => new TextEncoder().encode(s);

const VALID = `version https://git-lfs.github.com/spec/v1
oid sha256:4d7a214614ab2935c943f9e0ff69d22eadbb8f32b1258daaa5e2ca24d17e2393
size 12345
`;

describe('parseLfsPointer', () => {
  test('parses a well-formed pointer (string and bytes)', () => {
    const expected = {
      version: 'https://git-lfs.github.com/spec/v1',
      oid: 'sha256:4d7a214614ab2935c943f9e0ff69d22eadbb8f32b1258daaa5e2ca24d17e2393',
      size: 12345,
    };
    expect(parseLfsPointer(VALID)).toEqual(expected);
    expect(parseLfsPointer(enc(VALID))).toEqual(expected);
  });

  test('isLfsPointer agrees with parse', () => {
    expect(isLfsPointer(VALID)).toBe(true);
    expect(isLfsPointer(enc(VALID))).toBe(true);
  });

  test('rejects ordinary text, including text that mentions git-lfs', () => {
    expect(parseLfsPointer('# README\n\nThis project uses Git LFS for assets.\n')).toBeNull();
    expect(isLfsPointer('const x = 1;\n')).toBe(false);
    expect(isLfsPointer('')).toBe(false);
  });

  test('rejects a pointer missing the oid or size directive', () => {
    expect(parseLfsPointer('version https://git-lfs.github.com/spec/v1\nsize 10\n')).toBeNull();
    expect(
      parseLfsPointer('version https://git-lfs.github.com/spec/v1\noid sha256:abc\n')
    ).toBeNull();
  });

  test('requires the version line to come first', () => {
    const reordered = `oid sha256:abcdef
version https://git-lfs.github.com/spec/v1
size 10
`;
    expect(parseLfsPointer(reordered)).toBeNull();
  });

  test('rejects a non-numeric size', () => {
    const bad = `version https://git-lfs.github.com/spec/v1
oid sha256:abcdef
size lots
`;
    expect(parseLfsPointer(bad)).toBeNull();
  });

  test('ignores blobs larger than a real pointer', () => {
    const big = VALID + 'x'.repeat(2000);
    expect(parseLfsPointer(big)).toBeNull();
    expect(isLfsPointer(enc(big))).toBe(false);
  });
});
