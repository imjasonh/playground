// Read, write, and navigate shareable URL state: ?pack=<stored id>#<object oid>.
//
// The pack id is the IndexedDB key (usually the repo base URL, or file://… for
// local opens). Refreshing with the same URL reloads the pack from local storage.
// Browser history entries carry a small state payload so Back/Forward moves
// cleanly between landing, pack overview, and objects (including unresolved
// thin-pack entries that have no oid).

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

/** Normalize a navigation target into { packId, view, objectId, objectIndex }. */
export function normalizeNavTarget(target = {}) {
  const packId = target.packId && String(target.packId).length > 0 ? String(target.packId) : null;
  if (!packId) {
    return { packId: null, view: "landing", objectId: null, objectIndex: null };
  }
  const objectId =
    target.objectId && /^[0-9a-f]{40}$/i.test(target.objectId) ? target.objectId : null;
  const objectIndex =
    !objectId && Number.isInteger(target.objectIndex) && target.objectIndex >= 0
      ? target.objectIndex
      : null;
  const view =
    objectId || objectIndex != null || target.view === "object" ? "object" : "overview";
  return { packId, view, objectId, objectIndex };
}

/** Derive a navigation target from a location (when history.state is absent). */
export function navTargetFromUrl(locationLike = location) {
  const { packId, objectId } = readUrlState(locationLike);
  return normalizeNavTarget({ packId, objectId });
}

/** True when two normalized navigation targets represent the same screen. */
export function sameNavTarget(a, b) {
  if (!a || !b) return false;
  return (
    (a.packId || null) === (b.packId || null) &&
    (a.view || "landing") === (b.view || "landing") &&
    (a.objectId || null) === (b.objectId || null) &&
    (a.objectIndex ?? null) === (b.objectIndex ?? null)
  );
}

/** Build the relative pathname + search + hash for a pack and optional object oid. */
export function formatUrlState({ packId, objectId }, locationLike = location) {
  const url = new URL(locationLike.href);
  if (packId) url.searchParams.set(PACK_PARAM, packId);
  else url.searchParams.delete(PACK_PARAM);
  const hash = packId && objectId ? `#${objectId}` : "";
  return `${url.pathname}${url.search}${hash}`;
}

/**
 * Update the address bar to reflect the open pack and optional object selection.
 * Uses pushState by default so browser Back/Forward stays inside the app; pass
 * `{ replace: true }` to update the current entry in place.
 */
export function writeUrlState(
  { packId, objectId },
  locationLike = location,
  historyLike = history,
  { replace = false, state = null, force = false } = {},
) {
  const next = formatUrlState({ packId, objectId }, locationLike);
  const current = `${locationLike.pathname}${locationLike.search}${locationLike.hash}`;
  if (replace) {
    if (current !== next || state !== null || force) {
      historyLike.replaceState(state, "", next);
      return true;
    }
    return false;
  }
  if (current !== next || force) {
    historyLike.pushState(state, "", next);
    return true;
  }
  return false;
}

/** Build a shareable URL for a pack and optional object oid. */
export function packShareUrl(packId, objectId = null, locationLike = location) {
  const url = new URL(locationLike.href);
  url.searchParams.set(PACK_PARAM, packId);
  url.hash = objectId || "";
  return url.toString();
}

/**
 * Coordinate browser History API entries with in-app Back/Forward controls.
 *
 * Each entry written by this controller carries a `{ __pfNav: true, session,
 * pos, packId, view, objectId, objectIndex }` state object so:
 * - browser Back/Forward and the toolbar Back/Forward buttons share one stack
 * - toolbar Back stays inside the app (pos > 0 within this session)
 * - switching to Overview, Landing, or unresolved objects (no oid) restores
 *   cleanly on popstate
 */
export function createNavHistory({
  locationLike = location,
  historyLike = history,
  sessionId = `${Date.now().toString(36)}-${Math.random().toString(36).slice(2, 8)}`,
} = {}) {
  let session = sessionId;
  let pos = 0;
  let max = 0;
  let current = navTargetFromUrl(locationLike);

  function makeState(target, index) {
    return {
      __pfNav: true,
      session,
      pos: index,
      packId: target.packId,
      view: target.view,
      objectId: target.objectId,
      objectIndex: target.objectIndex,
    };
  }

  function isOwnState(state) {
    return Boolean(state && state.__pfNav && typeof state.pos === "number" && state.session);
  }

  /** Stamp the initial history entry at boot without pushing a new entry. */
  function init(target = null) {
    const existing = historyLike.state;
    const fromUrl = navTargetFromUrl(locationLike);
    if (isOwnState(existing)) {
      session = existing.session;
      pos = existing.pos;
      max = Math.max(max, pos);
    } else {
      pos = 0;
      max = 0;
    }
    const chosen =
      target != null
        ? normalizeNavTarget(target)
        : isOwnState(existing) &&
            (existing.packId || null) === (fromUrl.packId || null) &&
            (existing.objectId || null) === (fromUrl.objectId || null)
          ? normalizeNavTarget(existing)
          : fromUrl;
    current = chosen;
    writeUrlState(chosen, locationLike, historyLike, {
      replace: true,
      state: makeState(chosen, pos),
      force: true,
    });
    return chosen;
  }

  /** Push a new history entry unless the target matches the current screen. */
  function push(target) {
    const normalized = normalizeNavTarget(target);
    if (sameNavTarget(current, normalized)) return false;
    pos += 1;
    max = pos;
    current = normalized;
    writeUrlState(normalized, locationLike, historyLike, {
      replace: false,
      state: makeState(normalized, pos),
      force: true,
    });
    return true;
  }

  /** Replace the current history entry in place without changing stack depth. */
  function replace(target) {
    const normalized = normalizeNavTarget(target);
    current = normalized;
    writeUrlState(normalized, locationLike, historyLike, {
      replace: true,
      state: makeState(normalized, pos),
      force: true,
    });
    return normalized;
  }

  /** Handle a browser popstate event and return the target to render. */
  function onPopState(eventState) {
    if (isOwnState(eventState)) {
      if (eventState.session === session) {
        pos = eventState.pos;
        if (pos > max) max = pos;
      } else {
        session = eventState.session;
        pos = eventState.pos;
        max = Math.max(pos, 0);
      }
      current = normalizeNavTarget(eventState);
      return current;
    }
    const normalized = navTargetFromUrl(locationLike);
    current = normalized;
    return normalized;
  }

  function canBack() {
    return pos > 0;
  }

  function canForward() {
    return pos < max;
  }

  function back() {
    if (!canBack()) return false;
    historyLike.back();
    return true;
  }

  function forward() {
    if (!canForward()) return false;
    historyLike.forward();
    return true;
  }

  return {
    init,
    push,
    replace,
    onPopState,
    canBack,
    canForward,
    back,
    forward,
    get current() {
      return current;
    },
    get pos() {
      return pos;
    },
    get max() {
      return max;
    },
  };
}
