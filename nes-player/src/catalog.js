export const REPO = "imjasonh/playground";
export const BRANCH = "main";
export const ROM_DIR = "nescript/examples";

// The games the NEScript README shows, then SHA-256, then Coin Cavern.
// The other ROMs in nescript/examples are compiler smoke tests.
export const PLAYABLE = [
  { name: "platformer", title: "Platformer" },
  { name: "war", title: "War" },
  { name: "pong", title: "Pong" },
  { name: "subway", title: "Subway" },
  { name: "rampart", title: "Rampart" },
  { name: "dvd_screensaver", title: "DVD screensaver" },
  { name: "sha256", title: "SHA-256" },
  { name: "coin_cavern", title: "Coin Cavern" },
];

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
 * Turns a GitHub contents API listing into the playable games it holds,
 * in PLAYABLE order. A game that isn't on main yet is left out.
 * @param {unknown} entries
 * @returns {{name: string, title: string, size: number}[]}
 */
export function parseListing(entries) {
  if (!Array.isArray(entries)) {
    throw new Error("GitHub returned an unexpected listing");
  }
  const sizes = new Map();
  for (const entry of entries) {
    if (
      entry &&
      entry.type === "file" &&
      typeof entry.name === "string" &&
      /\.nes$/i.test(entry.name)
    ) {
      sizes.set(entry.name.replace(/\.nes$/i, ""), Number(entry.size) || 0);
    }
  }
  return selectPlayable([...sizes].map(([name, size]) => ({ name, size })));
}

/**
 * Keeps the playable games from a listing or from a previously cached one,
 * in PLAYABLE order, and fills in their titles.
 * @param {unknown} roms
 */
export function selectPlayable(roms) {
  if (!Array.isArray(roms)) return [];
  const sizes = new Map();
  for (const rom of roms) {
    if (rom && typeof rom.name === "string") sizes.set(rom.name, Number(rom.size) || 0);
  }
  return PLAYABLE.filter((game) => sizes.has(game.name)).map((game) => ({
    name: game.name,
    title: game.title,
    size: sizes.get(game.name),
  }));
}

/**
 * Filters games by a search string. Underscores and spaces match each
 * other, so "dvd screen" finds DVD screensaver.
 */
export function filterRoms(roms, query) {
  const q = query.trim().toLowerCase().replace(/[\s_-]+/g, " ");
  if (!q) return roms;
  return roms.filter((r) =>
    `${r.title} ${r.name}`.toLowerCase().replace(/[\s_-]+/g, " ").includes(q),
  );
}
