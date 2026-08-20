import {
  GIT_MODE,
  classifyGitMode,
  symlinkTarget,
  parseGitmodules,
} from '../src/specialEntry.js';

const enc = (s) => new TextEncoder().encode(s);

describe('classifyGitMode', () => {
  test('classifies numeric modes (as walk() reports them)', () => {
    expect(classifyGitMode(GIT_MODE.TREE)).toBe('tree');
    expect(classifyGitMode(GIT_MODE.BLOB)).toBe('file');
    expect(classifyGitMode(GIT_MODE.EXECUTABLE)).toBe('executable');
    expect(classifyGitMode(GIT_MODE.SYMLINK)).toBe('symlink');
    expect(classifyGitMode(GIT_MODE.SUBMODULE)).toBe('submodule');
  });

  test('classifies octal string modes (as readTree() reports them)', () => {
    expect(classifyGitMode('40000')).toBe('tree');
    expect(classifyGitMode('100644')).toBe('file');
    expect(classifyGitMode('100755')).toBe('executable');
    expect(classifyGitMode('120000')).toBe('symlink');
    expect(classifyGitMode('160000')).toBe('submodule');
  });

  test('falls back to file for unknown or invalid modes', () => {
    expect(classifyGitMode('not-a-mode')).toBe('file');
    expect(classifyGitMode(undefined)).toBe('file');
    expect(classifyGitMode(null)).toBe('file');
  });
});

describe('symlinkTarget', () => {
  test('decodes the blob content as the target path', () => {
    expect(symlinkTarget(enc('../shared/config.json'))).toBe('../shared/config.json');
  });

  test('accepts a string and strips only trailing newlines', () => {
    expect(symlinkTarget('src/index.js\n')).toBe('src/index.js');
    expect(symlinkTarget('a/b\r\n')).toBe('a/b');
    // Interior characters (including spaces) are preserved.
    expect(symlinkTarget('dir with spaces/file')).toBe('dir with spaces/file');
  });

  test('handles empty/nullish input', () => {
    expect(symlinkTarget(enc(''))).toBe('');
    expect(symlinkTarget(null)).toBe('');
    expect(symlinkTarget(undefined)).toBe('');
  });
});

describe('parseGitmodules', () => {
  test('parses entries keyed by working-tree path', () => {
    const text = `[submodule "widget"]
\tpath = vendor/widget
\turl = https://github.com/acme/widget.git
[submodule "theme"]
\tpath = themes/dark
\turl = git@github.com:acme/theme.git
\tbranch = main
`;
    const mods = parseGitmodules(text);
    expect([...mods.keys()].sort()).toEqual(['themes/dark', 'vendor/widget']);
    expect(mods.get('vendor/widget')).toMatchObject({
      name: 'widget',
      path: 'vendor/widget',
      url: 'https://github.com/acme/widget.git',
    });
    expect(mods.get('themes/dark')).toMatchObject({
      url: 'git@github.com:acme/theme.git',
      branch: 'main',
    });
  });

  test('tolerates url declared before path, and comments/blank lines', () => {
    const text = `; a comment
# another

[submodule "lib"]
    url = https://example.com/lib.git
    path = third_party/lib
`;
    const mods = parseGitmodules(text);
    expect(mods.get('third_party/lib')).toMatchObject({
      url: 'https://example.com/lib.git',
      path: 'third_party/lib',
    });
  });

  test('ignores non-submodule sections', () => {
    const text = `[core]
\tbare = false
[submodule "x"]
\tpath = x
\turl = https://example.com/x.git
`;
    const mods = parseGitmodules(text);
    expect([...mods.keys()]).toEqual(['x']);
  });

  test('accepts a Uint8Array and returns an empty map for empty input', () => {
    expect(parseGitmodules(enc('')).size).toBe(0);
    expect(parseGitmodules('').size).toBe(0);
    const mods = parseGitmodules(enc('[submodule "x"]\npath = x\nurl = u\n'));
    expect(mods.get('x')).toMatchObject({ url: 'u' });
  });
});
