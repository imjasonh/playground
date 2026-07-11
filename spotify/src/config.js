/** Storage keys and OAuth scopes for the Spotify Web Playback app. */

export const STORAGE_KEYS = {
  clientId: "spotify.clientId",
  verifier: "spotify.codeVerifier",
  tokens: "spotify.tokens",
};

/**
 * Scopes required for search + Web Playback SDK streaming.
 * @see https://developer.spotify.com/documentation/web-playback-sdk
 */
export const SCOPES = [
  "streaming",
  "user-read-email",
  "user-read-private",
  "user-read-playback-state",
  "user-modify-playback-state",
].join(" ");

export const AUTH_URL = "https://accounts.spotify.com/authorize";
export const TOKEN_URL = "https://accounts.spotify.com/api/token";
export const API_BASE = "https://api.spotify.com/v1";

/** Redirect URI must match a URI registered in the Spotify Developer Dashboard. */
export function redirectUri(location = globalThis.location) {
  const path = location.pathname.endsWith("/")
    ? location.pathname
    : `${location.pathname}/`;
  return `${location.origin}${path}`;
}

export function loadClientId(storage = globalThis.localStorage) {
  if (!storage) return "";
  return storage.getItem(STORAGE_KEYS.clientId)?.trim() || "";
}

export function saveClientId(clientId, storage = globalThis.localStorage) {
  if (!storage) return String(clientId || "").trim();
  const value = String(clientId || "").trim();
  if (value) storage.setItem(STORAGE_KEYS.clientId, value);
  else storage.removeItem(STORAGE_KEYS.clientId);
  return value;
}
