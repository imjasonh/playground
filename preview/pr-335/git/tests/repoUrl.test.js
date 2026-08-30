import { parseRepoUrl, DEFAULT_CORS_PROXY } from '../src/repoUrl.js';

describe('parseRepoUrl', () => {
  test('parses a full https GitHub URL', () => {
    const r = parseRepoUrl('https://github.com/owner/repo');
    expect(r.valid).toBe(true);
    expect(r.host).toBe('github.com');
    expect(r.owner).toBe('owner');
    expect(r.name).toBe('repo');
    expect(r.fullName).toBe('owner/repo');
    expect(r.url).toBe('https://github.com/owner/repo.git');
    expect(r.dir).toBe('/github.com/owner/repo');
  });

  test('strips a trailing .git and slash', () => {
    const r = parseRepoUrl('https://github.com/owner/repo.git/');
    expect(r.valid).toBe(true);
    expect(r.name).toBe('repo');
    expect(r.url).toBe('https://github.com/owner/repo.git');
  });

  test('expands owner/repo shorthand to GitHub', () => {
    const r = parseRepoUrl('facebook/react');
    expect(r.valid).toBe(true);
    expect(r.url).toBe('https://github.com/facebook/react.git');
    expect(r.host).toBe('github.com');
  });

  test('supports non-GitHub hosts and nested groups', () => {
    const r = parseRepoUrl('https://gitlab.com/group/sub/project');
    expect(r.valid).toBe(true);
    expect(r.host).toBe('gitlab.com');
    expect(r.name).toBe('project');
    expect(r.owner).toBe('sub');
    expect(r.dir).toBe('/gitlab.com/group/sub/project');
  });

  test('rejects empty input', () => {
    expect(parseRepoUrl('').valid).toBe(false);
    expect(parseRepoUrl('   ').valid).toBe(false);
  });

  test('rejects SSH URLs with a helpful message', () => {
    const r = parseRepoUrl('git@github.com:owner/repo.git');
    expect(r.valid).toBe(false);
    expect(r.error).toMatch(/SSH/i);
  });

  test('rejects nonsense that is neither URL nor slug', () => {
    expect(parseRepoUrl('not a url').valid).toBe(false);
    expect(parseRepoUrl('justonesegment').valid).toBe(false);
  });

  test('exposes a default CORS proxy', () => {
    expect(DEFAULT_CORS_PROXY).toMatch(/^https:\/\//);
  });
});
