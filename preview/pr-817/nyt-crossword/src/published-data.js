// A PR preview is served under /preview/pr-<N>/<app>/. Scraped JSON is on
// gh-pages at /<app>/data/, not in the preview tree. Data requests from a
// preview should use that published path, which is the current gh-pages head.

const PREVIEW_MARKER = "/preview/pr-";

export function publishedDataUrl(pathname, relativePath) {
  if (typeof pathname !== "string" || typeof relativePath !== "string") return null;
  if (!relativePath.startsWith("data/")) return null;
  const markerAt = pathname.indexOf(PREVIEW_MARKER);
  if (markerAt === -1) return null;
  const afterPr = pathname.slice(markerAt + PREVIEW_MARKER.length);
  const prSlash = afterPr.indexOf("/");
  if (prSlash === -1) return null;
  const app = afterPr.slice(prSlash + 1).split("/").filter(Boolean)[0];
  if (!app) return null;
  const root = pathname.slice(0, markerAt).replace(/\/$/, "");
  return `${root}/${app}/${relativePath}`;
}
