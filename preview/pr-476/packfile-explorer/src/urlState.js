// Read and write shareable URL state: ?pack=<stored id>#<object oid>.
//
// The pack id is the IndexedDB key (usually the repo base URL, or file://… for
// local opens). Refreshing with the same URL reloads the pack from local storage.

const PACK_PARAM = "pack";

/** Parse the current location into pack id and optional object oid. */
export function readUrlState(locationLike = location) {
  const url = new URL(locationLike.href);
  const packId = url.searchParams.get(PACK_PARAM);
  const objectId = (url.hash || "").replace(/^#/, "").trim() || null;
  return {
    packId: packId && packId.length > 0 ? packId : null,
    objectId: objectId && /^[0-9a-f]{40}$/i.test(objectId) ? objectId : null,
  };
}

/**
 * Update the address bar to reflect the open pack and optional object selection.
 * Uses replaceState so clicking around does not spam browser history.
 */
export function writeUrlState({ packId, objectId }, locationLike = location, historyLike = history) {
  const url = new URL(locationLike.href);
  if (packId) url.searchParams.set(PACK_PARAM, packId);
  else url.searchParams.delete(PACK_PARAM);
  const hash = objectId ? `#${objectId}` : "";
  const next = `${url.pathname}${url.search}${hash}`;
  const current = `${locationLike.pathname}${locationLike.search}${locationLike.hash}`;
  if (current !== next) {
    historyLike.replaceState(null, "", next);
  }
}

/** Build a shareable URL for a pack and optional object oid. */
export function packShareUrl(packId, objectId = null, locationLike = location) {
  const url = new URL(locationLike.href);
  url.searchParams.set(PACK_PARAM, packId);
  url.hash = objectId || "";
  return url.toString();
}
