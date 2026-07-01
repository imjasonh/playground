/**
 * Parse and validate the repository URLs the user can clone. Only HTTP(S)
 * remotes work in the browser (isomorphic-git speaks the smart-HTTP protocol
 * over fetch); SSH remotes are rejected with a helpful message.
 */

export const DEFAULT_CORS_PROXY = 'https://cors.isomorphic-git.org';

const SLUG_RE = /^[\w.-]+\/[\w.-]+$/;

function sanitizeSegment(segment) {
  return segment.replace(/[^\w.-]+/g, '-').replace(/^-+|-+$/g, '') || 'repo';
}

function stripGitSuffix(name) {
  return name.replace(/\.git$/i, '');
}

/**
 * @typedef {Object} ParsedRepoUrl
 * @property {boolean} valid
 * @property {string} [error]
 * @property {string} [url]       normalized clone URL
 * @property {string} [host]
 * @property {string} [owner]
 * @property {string} [name]      repository name (no .git)
 * @property {string} [fullName]  "owner/name" when known
 * @property {string} [dir]       storage directory key, e.g. "/github.com/owner/name"
 */

/**
 * @param {string} input
 * @returns {ParsedRepoUrl}
 */
export function parseRepoUrl(input) {
  const raw = (input || '').trim();
  if (!raw) {
    return { valid: false, error: 'Enter a repository URL.' };
  }

  if (/^git@/i.test(raw) || /^ssh:\/\//i.test(raw)) {
    return {
      valid: false,
      error: 'SSH URLs are not supported in the browser. Use an https:// URL.',
    };
  }

  let urlString = raw;

  // "owner/repo" shorthand -> GitHub https URL.
  if (!/^https?:\/\//i.test(raw)) {
    if (SLUG_RE.test(raw)) {
      urlString = `https://github.com/${stripGitSuffix(raw)}`;
    } else {
      return {
        valid: false,
        error: 'Use an https:// URL or "owner/repo" shorthand.',
      };
    }
  }

  let parsed;
  try {
    parsed = new URL(urlString);
  } catch {
    return { valid: false, error: 'That does not look like a valid URL.' };
  }

  if (parsed.protocol !== 'http:' && parsed.protocol !== 'https:') {
    return { valid: false, error: 'Only http and https URLs are supported.' };
  }

  const host = parsed.hostname;
  const segments = parsed.pathname.split('/').filter(Boolean).map(stripGitSuffix);
  if (segments.length === 0) {
    return { valid: false, error: 'URL is missing a repository path.' };
  }

  const name = segments[segments.length - 1];
  const owner = segments.length > 1 ? segments[segments.length - 2] : '';
  const fullName = owner ? `${owner}/${name}` : name;

  const dirSegments = [host, ...segments].map(sanitizeSegment);
  const dir = `/${dirSegments.join('/')}`;

  const normalizedUrl = `${parsed.protocol}//${parsed.host}/${segments.join('/')}.git`;

  return {
    valid: true,
    url: normalizedUrl,
    host,
    owner,
    name,
    fullName,
    dir,
  };
}
