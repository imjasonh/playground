// Build the repository endpoints and CORS-proxied URLs the transport fetches.

export const DEFAULT_PROXY = "https://cors-proxy-worker.imjasonh.workers.dev";

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

/** Wrap a target URL in a CORS-proxy request URL. */
export function proxied(proxyBase, targetUrl) {
  const trimmed = (proxyBase || "").trim().replace(/\/+$/, "");
  if (!trimmed) return targetUrl;
  return `${trimmed}/?url=${encodeURIComponent(targetUrl)}`;
}
