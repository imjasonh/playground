/**
 * Build a "view this file on the host" web URL from a clone URL.
 *
 * The app browses a local clone, but when the origin is a recognized host we can
 * link the open file back to its page there (GitHub / GitLab / Bitbucket). This
 * is best-effort: an unknown host returns null and the UI simply omits the link.
 *
 * Pure and dependency-free so it can be unit-tested without a DOM.
 */

/** Encode a path/ref for a URL while keeping its `/` separators readable. */
function encodeSegments(value) {
  return String(value)
    .split('/')
    .map(encodeURIComponent)
    .join('/');
}

/** Per-provider blob path + line-anchor builders, keyed by hostname match. */
const PROVIDERS = [
  {
    match: (host) => host === 'github.com',
    blob: (slug, ref, path) => `/${slug}/blob/${ref}/${path}`,
    anchor: ({ start, end }) => (end && end !== start ? `#L${start}-L${end}` : `#L${start}`),
  },
  {
    // gitlab.com and self-managed GitLab instances ("gitlab.example.com").
    match: (host) => host === 'gitlab.com' || host.startsWith('gitlab.'),
    blob: (slug, ref, path) => `/${slug}/-/blob/${ref}/${path}`,
    anchor: ({ start, end }) => (end && end !== start ? `#L${start}-${end}` : `#L${start}`),
  },
  {
    match: (host) => host === 'bitbucket.org',
    blob: (slug, ref, path) => `/${slug}/src/${ref}/${path}`,
    anchor: ({ start, end }) =>
      end && end !== start ? `#lines-${start}:${end}` : `#lines-${start}`,
  },
];

/**
 * @param {?string} repoUrl  the clone URL (https), or null
 * @param {{ref?: string, path: string, lines?: {start:number, end:number}}} opts
 *   `ref` is a branch/tag name or a commit oid; `lines` is an optional selection.
 * @returns {?string}  a web URL for the file, or null when the host is unknown
 */
export function fileWebUrl(repoUrl, { ref, path, lines } = {}) {
  if (!repoUrl || !ref || !path) return null;
  let parsed;
  try {
    parsed = new URL(repoUrl);
  } catch {
    return null;
  }
  if (parsed.protocol !== 'http:' && parsed.protocol !== 'https:') return null;

  const provider = PROVIDERS.find((p) => p.match(parsed.hostname));
  if (!provider) return null;

  // owner/repo slug from the path, minus a trailing ".git".
  const segments = parsed.pathname.split('/').filter(Boolean);
  if (segments.length < 2) return null;
  segments[segments.length - 1] = segments[segments.length - 1].replace(/\.git$/i, '');
  const slug = segments.map(encodeURIComponent).join('/');

  let url =
    `${parsed.protocol}//${parsed.host}` +
    provider.blob(slug, encodeSegments(ref), encodeSegments(path));
  if (lines && lines.start) url += provider.anchor(lines);
  return url;
}
