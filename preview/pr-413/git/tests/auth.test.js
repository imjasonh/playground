/**
 * @jest-environment jsdom
 *
 * Session-token auth helpers. jsdom provides a real sessionStorage, so the
 * round-trip and the onAuth adapter are exercised end-to-end.
 */
import { hostOf, rememberToken, getToken, hasToken, makeOnAuth } from '../src/auth.js';

beforeEach(() => sessionStorage.clear());

describe('hostOf', () => {
  test('extracts the host, or returns empty for junk', () => {
    expect(hostOf('https://github.com/owner/repo')).toBe('github.com');
    expect(hostOf('https://example.com:8443/x')).toBe('example.com:8443');
    expect(hostOf('not a url')).toBe('');
  });
});

describe('token store (session-only)', () => {
  test('remember / get / has round-trips through sessionStorage', () => {
    expect(getToken('github.com')).toBe('');
    expect(hasToken('github.com')).toBe(false);

    rememberToken('github.com', 'secret-pat');
    expect(getToken('github.com')).toBe('secret-pat');
    expect(hasToken('github.com')).toBe(true);

    // It lives in sessionStorage, never localStorage.
    expect(sessionStorage.getItem('git-browser:token:github.com')).toBe('secret-pat');
    expect(localStorage.getItem('git-browser:token:github.com')).toBeNull();
  });

  test('an empty token clears any stored value', () => {
    rememberToken('github.com', 'secret');
    rememberToken('github.com', '');
    expect(getToken('github.com')).toBe('');
  });

  test('rememberToken ignores a missing host', () => {
    expect(() => rememberToken('', 'secret')).not.toThrow();
    expect(getToken('')).toBe('');
  });
});

describe('makeOnAuth', () => {
  test('supplies the host token as the Basic-auth username', () => {
    rememberToken('github.com', 'pat-123');
    const onAuth = makeOnAuth();
    expect(onAuth('https://github.com/owner/repo.git')).toEqual({
      username: 'pat-123',
      password: '',
    });
  });

  test('returns undefined when no token is stored for the host', () => {
    const onAuth = makeOnAuth();
    expect(onAuth('https://gitlab.com/owner/repo.git')).toBeUndefined();
  });
});
