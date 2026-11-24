// Build the repository endpoints and CORS-proxied URLs the transport fetches.

// Same public proxy the in-browser git client uses. It streams the
// upload-pack body. The playground worker stops at 25 MiB, and a depth-1
// fetch of playground main is just over that, so the worker returns HTTP 413.
export const DEFAULT_PROXY = "https://cors.isomorphic-git.org";

/**
 * Normalize a user-typed repository reference into a smart-HTTP base URL.
 *
 * Accepts `owner/repo`, `github.com/owner/repo`, a full `https://…` URL, with
 * or without a trailing `.git`. Returns a base ending in `.git`.
 */
export function normalizeRepoUrl(input) {
  let value = (input || "").trim();
  if (!value) throw new Error("enter a repository URL");
  value = value.replace(/\/+$/, "");

  if (/^[\w.-]+\/[\w.-]+$/.test(value)) {
    value = `https://github.com/${value}`;
  } else if (/^github\.com\//i.test(value)) {
    value = `https://${value}`;
  } else if (!/^https?:\/\//i.test(value)) {
    value = `https://${value}`;
  }

  const url = new URL(value);
  if (url.protocol !== "https:" && url.protocol !== "http:") {
    throw new Error(`unsupported scheme: ${url.protocol}`);
  }
  if (!url.pathname.endsWith(".git")) {
    url.pathname = `${url.pathname}.git`;
  }
  return url.toString();
}

/** The info/refs advertisement URL for a base repo URL. */
export function infoRefsUrl(base) {
  return `${base}/info/refs?service=git-upload-pack`;
}

/** The upload-pack POST URL for a base repo URL. */
export function uploadPackUrl(base) {
  return `${base}/git-upload-pack`;
}

/**
 * Wrap a target URL the way isomorphic-git's `corsProxify` does.
 *
 * A proxy that ends in `?` is a query-string proxy: the target is appended
 * as-is. Any other proxy is a path proxy. The scheme is stripped and the
 * remainder is appended, which is what `https://cors.isomorphic-git.org`
 * expects (`/github.com/owner/repo.git/...`).
 */
export function proxied(proxyBase, targetUrl) {
  const proxy = (proxyBase || "").trim().replace(/\/+$/, "");
  if (!proxy) return targetUrl;
  if (proxy.endsWith("?")) return `${proxy}${targetUrl}`;
  return `${proxy}/${targetUrl.replace(/^https?:\/\//, "")}`;
}
