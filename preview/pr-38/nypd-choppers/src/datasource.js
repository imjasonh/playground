// Resolve where the app should fetch its scraped ADS-B data from.
//
// The hourly scraper only ever publishes to the production location on the
// gh-pages branch: `<site-root>/nypd-choppers/data/`. PR previews are served
// from `<site-root>/preview/pr-<n>/nypd-choppers/` and do NOT get their own copy
// of that data (it would bloat gh-pages and never be current). So when the app
// detects it is running inside a preview path, it strips the `/preview/pr-<n>/`
// segment and reads the same production data instead — a preview shows the
// latest real flights, not the bundled sample day.

/**
 * Absolute URL (no trailing slash) of the scraped-data directory to fetch from,
 * given the current page's origin and pathname.
 *
 * @param {string} origin e.g. "https://imjasonh.github.io"
 * @param {string} pathname e.g. "/playground/preview/pr-38/nypd-choppers/"
 * @returns {string} e.g. "https://imjasonh.github.io/playground/nypd-choppers/data"
 */
export function resolveDataBase(origin, pathname) {
  // Directory holding the app's index.html (drop any trailing filename).
  let dir = String(pathname == null ? "/" : pathname).replace(/[^/]*$/, "");
  if (!dir.startsWith("/")) dir = `/${dir}`;
  if (!dir.endsWith("/")) dir += "/";
  // Reuse production scraper output from a PR preview.
  dir = dir.replace(/\/preview\/pr-\d+\//, "/");
  return `${origin || ""}${dir}data`;
}
