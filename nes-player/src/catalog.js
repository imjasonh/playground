export const REPO = "imjasonh/playground";
export const BRANCH = "main";
export const ROM_DIR = "nescript/examples";

export function listingUrl() {
  return `https://api.github.com/repos/${REPO}/contents/${ROM_DIR}?ref=${BRANCH}`;
}

export function romUrl(name) {
  return `https://raw.githubusercontent.com/${REPO}/${BRANCH}/${ROM_DIR}/${encodeURIComponent(name)}.nes`;
}

export function sourceUrl(name) {
  return `https://github.com/${REPO}/blob/${BRANCH}/${ROM_DIR}/${encodeURIComponent(name)}.ne`;
}

/**
 * Turns a GitHub contents API listing into the ROMs it holds, sorted by name.
 * @param {unknown} entries
 * @returns {{name: string, size: number}[]}
 */
export function parseListing(entries) {
  if (!Array.isArray(entries)) {
    throw new Error("GitHub returned an unexpected listing");
  }
  return entries
    .filter(
      (e) =>
        e &&
        e.type === "file" &&
        typeof e.name === "string" &&
        /\.nes$/i.test(e.name),
    )
    .map((e) => ({
      name: e.name.replace(/\.nes$/i, ""),
      size: Number(e.size) || 0,
    }))
    .sort((a, b) => a.name.localeCompare(b.name));
}

/**
 * Filters ROM names by a search string. Underscores and spaces match each
 * other, so "dvd screen" finds dvd_screensaver.
 */
export function filterRoms(roms, query) {
  const q = query.trim().toLowerCase().replace(/[\s_-]+/g, " ");
  if (!q) return roms;
  return roms.filter((r) =>
    r.name.toLowerCase().replace(/[\s_-]+/g, " ").includes(q),
  );
}
