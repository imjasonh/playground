/** Thin Spotify Web API client for search and playback control. */

import { API_BASE } from "./config.js";

/**
 * @param {string} accessToken
 * @param {string} path
 * @param {RequestInit & { fetchImpl?: typeof fetch }} [options]
 */
export async function spotifyFetch(accessToken, path, options = {}) {
  const { fetchImpl = globalThis.fetch, headers, ...rest } = options;
  const response = await fetchImpl(`${API_BASE}${path}`, {
    ...rest,
    headers: {
      Authorization: `Bearer ${accessToken}`,
      ...(rest.body ? { "Content-Type": "application/json" } : {}),
      ...headers,
    },
  });

  if (response.status === 204) return null;

  const text = await response.text();
  const data = text ? JSON.parse(text) : null;

  if (!response.ok) {
    const detail =
      data?.error?.message || data?.error_description || response.statusText;
    const err = new Error(detail || `Spotify API ${response.status}`);
    err.status = response.status;
    err.body = data;
    throw err;
  }

  return data;
}

/**
 * Normalize a search API track into a UI-friendly record.
 * @param {object} track
 */
export function mapTrack(track) {
  if (!track) return null;
  const images = track.album?.images || [];
  const image =
    images.find((img) => img.width >= 64 && img.width <= 300) ||
    images[images.length - 1] ||
    null;
  return {
    id: track.id,
    uri: track.uri,
    name: track.name,
    artists: (track.artists || []).map((a) => a.name).filter(Boolean),
    album: track.album?.name || "",
    imageUrl: image?.url || "",
    durationMs: track.duration_ms || 0,
    explicit: Boolean(track.explicit),
  };
}

/**
 * @param {string} accessToken
 * @param {string} query
 * @param {{ limit?: number, fetchImpl?: typeof fetch }} [options]
 */
export async function searchTracks(accessToken, query, options = {}) {
  const { limit = 20, fetchImpl = globalThis.fetch } = options;
  const q = String(query || "").trim();
  if (!q) return [];

  const params = new URLSearchParams({
    q,
    type: "track",
    limit: String(limit),
  });
  const data = await spotifyFetch(accessToken, `/search?${params}`, {
    fetchImpl,
  });
  return (data?.tracks?.items || []).map(mapTrack).filter(Boolean);
}

/**
 * Start or resume playback of one or more URIs on a specific device.
 * @param {string} accessToken
 * @param {string} deviceId
 * @param {string[]} uris
 * @param {{ fetchImpl?: typeof fetch }} [options]
 */
export async function playUris(accessToken, deviceId, uris, options = {}) {
  const { fetchImpl = globalThis.fetch } = options;
  if (!deviceId) throw new Error("Player device is not ready yet.");
  if (!uris?.length) throw new Error("No tracks to play.");

  return spotifyFetch(
    accessToken,
    `/me/player/play?device_id=${encodeURIComponent(deviceId)}`,
    {
      method: "PUT",
      body: JSON.stringify({ uris }),
      fetchImpl,
    },
  );
}

/**
 * Transfer playback to the Web Playback SDK device and optionally start playing.
 */
export async function transferPlayback(
  accessToken,
  deviceId,
  { play = true, fetchImpl = globalThis.fetch } = {},
) {
  return spotifyFetch(accessToken, "/me/player", {
    method: "PUT",
    body: JSON.stringify({ device_ids: [deviceId], play }),
    fetchImpl,
  });
}

export async function fetchCurrentUser(accessToken, options = {}) {
  const { fetchImpl = globalThis.fetch } = options;
  return spotifyFetch(accessToken, "/me", { fetchImpl });
}

/** Format milliseconds as m:ss. */
export function formatDuration(ms) {
  const total = Math.max(0, Math.floor(Number(ms) / 1000) || 0);
  const minutes = Math.floor(total / 60);
  const seconds = total % 60;
  return `${minutes}:${String(seconds).padStart(2, "0")}`;
}

export function artistLine(artists) {
  if (!artists?.length) return "Unknown artist";
  return artists.join(", ");
}
