/**
 * Session-only authentication for private repositories.
 *
 * A personal access token is held in `sessionStorage` (cleared when the tab
 * closes) keyed by host, never in the registry/localStorage and never logged.
 * `makeOnAuth` adapts it to isomorphic-git's `onAuth(url)` callback, which is
 * invoked when a fetch/clone needs credentials.
 *
 * Note: like all repo traffic, an authenticated request still passes through
 * the configured CORS proxy, which therefore sees the token. The UI says so.
 */

const PREFIX = 'git-browser:token:';

const key = (host) => `${PREFIX}${host}`;

/** Host portion of a URL, or '' if it can't be parsed. */
export function hostOf(url) {
  try {
    return new URL(url).host;
  } catch {
    return '';
  }
}

/** Store (or clear, when token is falsy) a token for a host, session-only. */
export function rememberToken(host, token) {
  if (!host) return;
  try {
    if (token) sessionStorage.setItem(key(host), token);
    else sessionStorage.removeItem(key(host));
  } catch {
    /* sessionStorage unavailable (private mode / disabled); auth just won't persist */
  }
}

/** The session token for a host, or '' when none is stored. */
export function getToken(host) {
  try {
    return sessionStorage.getItem(key(host)) || '';
  } catch {
    return '';
  }
}

export function hasToken(host) {
  return Boolean(getToken(host));
}

/**
 * An isomorphic-git `onAuth` callback backed by the session token store.
 * Returns credentials for the request's host, or `undefined` when none are
 * stored so the public path is used (and a private repo cleanly returns 401).
 *
 * GitHub accepts a PAT as the Basic-auth username; we send it that way.
 */
export function makeOnAuth() {
  return (url) => {
    const token = getToken(hostOf(url));
    if (!token) return undefined;
    return { username: token, password: '' };
  };
}
