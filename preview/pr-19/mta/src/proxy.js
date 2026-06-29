/**
 * Build the URL the browser actually fetches from a feed URL and a proxy
 * template. MTA feeds send no CORS headers, so live mode has to go through a
 * CORS proxy (or a self-hosted one); sample mode needs none of this.
 *
 * Template rules (first match wins):
 *   - empty / falsy           -> the feed URL unchanged (direct; only works with
 *                                a self-hosted proxy or a browser CORS shim)
 *   - contains "{url}"        -> replaced with the URL-encoded feed URL
 *   - contains "{rawurl}"     -> replaced with the raw feed URL
 *   - ends with "=" or "/"    -> feed URL appended (encoded after "=", raw after "/")
 *   - otherwise               -> encoded feed URL appended
 */

export const DIRECT = '';

/** A few well-known public CORS proxies, plus "direct". User-overridable. */
export const PROXY_PRESETS = [
  { id: 'corsproxy', label: 'corsproxy.io', template: 'https://corsproxy.io/?url={url}' },
  { id: 'allorigins', label: 'allorigins.win', template: 'https://api.allorigins.win/raw?url={url}' },
  { id: 'codetabs', label: 'codetabs.com', template: 'https://api.codetabs.com/v1/proxy/?quest={rawurl}' },
  { id: 'direct', label: 'Direct (needs your own proxy)', template: DIRECT },
];

/**
 * @param {string} template  a proxy template (see module docs) or '' for direct
 * @param {string} feedUrl   the upstream feed URL
 * @returns {string}
 */
export function buildFetchUrl(template, feedUrl) {
  const tpl = (template || '').trim();
  if (!tpl) return feedUrl;
  if (tpl.includes('{url}')) return tpl.replace('{url}', encodeURIComponent(feedUrl));
  if (tpl.includes('{rawurl}')) return tpl.replace('{rawurl}', feedUrl);
  if (tpl.endsWith('=')) return tpl + encodeURIComponent(feedUrl);
  if (tpl.endsWith('/')) return tpl + feedUrl;
  return tpl + encodeURIComponent(feedUrl);
}

/** True when no proxy is in play (requests go straight to the origin). */
export function isDirect(template) {
  return !((template || '').trim());
}
