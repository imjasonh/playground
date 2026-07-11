/**
 * Spotify Play — browser UI wiring for login, search, and Web Playback SDK.
 */

import { artistLine, formatDuration, playUris, searchTracks } from "./api.js";
import {
  beginLogin,
  clearTokens,
  getValidAccessToken,
  handleAuthCallback,
  loadTokens,
} from "./auth.js";
import { loadClientId, saveClientId } from "./config.js";
import { createPlayer } from "./player.js";

const state = {
  accessToken: null,
  deviceId: null,
  player: null,
  results: [],
  query: "",
  status: "idle",
  error: "",
  track: null,
  paused: true,
  position: 0,
  duration: 0,
};

const els = {};

function $(id) {
  return document.getElementById(id);
}

function setError(message) {
  state.error = message || "";
  if (els.error) {
    els.error.textContent = state.error;
    els.error.hidden = !state.error;
  }
}

function setStatus(message) {
  state.status = message || "";
  if (els.status) els.status.textContent = state.status;
}

function showLoggedOut() {
  els.gate.hidden = false;
  els.app.hidden = true;
  els.nowPlaying.hidden = true;
  els.logout.hidden = true;
}

function showLoggedIn() {
  els.gate.hidden = true;
  els.app.hidden = false;
  els.logout.hidden = false;
}

function renderResults() {
  if (!els.results) return;
  els.results.replaceChildren();

  if (!state.results.length) {
    const empty = document.createElement("p");
    empty.className = "empty";
    empty.textContent = state.query
      ? "No tracks matched that search."
      : "Search for a song, artist, or album.";
    els.results.appendChild(empty);
    return;
  }

  const list = document.createElement("ul");
  list.className = "track-list";
  list.setAttribute("role", "list");

  for (const track of state.results) {
    const item = document.createElement("li");
    item.className = "track";

    const art = document.createElement("img");
    art.className = "track__art";
    art.alt = "";
    art.width = 56;
    art.height = 56;
    art.loading = "lazy";
    if (track.imageUrl) art.src = track.imageUrl;
    else art.classList.add("track__art--empty");

    const meta = document.createElement("div");
    meta.className = "track__meta";

    const title = document.createElement("p");
    title.className = "track__title";
    title.textContent = track.name;

    const subtitle = document.createElement("p");
    subtitle.className = "track__subtitle";
    subtitle.textContent = `${artistLine(track.artists)} · ${track.album}`;

    meta.append(title, subtitle);

    const duration = document.createElement("span");
    duration.className = "track__duration";
    duration.textContent = formatDuration(track.durationMs);

    const play = document.createElement("button");
    play.type = "button";
    play.className = "track__play";
    play.textContent = "Play";
    play.setAttribute("aria-label", `Play ${track.name}`);
    play.addEventListener("click", () => void playTrack(track));

    item.append(art, meta, duration, play);
    list.appendChild(item);
  }

  els.results.appendChild(list);
}

function renderNowPlaying() {
  const track = state.track;
  if (!track) {
    els.nowPlaying.hidden = true;
    return;
  }

  els.nowPlaying.hidden = false;
  els.npTitle.textContent = track.name;
  els.npArtist.textContent = artistLine(
    track.artists?.map((a) => a.name || a) || [],
  );
  if (track.album?.images?.[0]?.url) {
    els.npArt.src = track.album.images[0].url;
    els.npArt.hidden = false;
  } else if (typeof track.imageUrl === "string" && track.imageUrl) {
    els.npArt.src = track.imageUrl;
    els.npArt.hidden = false;
  } else {
    els.npArt.removeAttribute("src");
    els.npArt.hidden = true;
  }

  els.togglePlay.textContent = state.paused ? "Play" : "Pause";
  els.togglePlay.setAttribute(
    "aria-label",
    state.paused ? "Play" : "Pause",
  );

  const duration = state.duration || track.duration_ms || track.durationMs || 0;
  const position = Math.min(state.position || 0, duration || 0);
  els.npTime.textContent = `${formatDuration(position)} / ${formatDuration(duration)}`;
  if (duration > 0) {
    els.npProgress.value = String(Math.round((position / duration) * 1000));
  } else {
    els.npProgress.value = "0";
  }
}

async function ensureToken() {
  const token = await getValidAccessToken();
  state.accessToken = token;
  return token;
}

async function playTrack(track) {
  setError("");
  try {
    const token = await ensureToken();
    if (!token) {
      showLoggedOut();
      throw new Error("Session expired — log in again.");
    }
    if (!state.deviceId) {
      throw new Error(
        "Player is still connecting. Wait a moment, then try again.",
      );
    }
    setStatus(`Playing ${track.name}…`);
    await playUris(token, state.deviceId, [track.uri]);
    state.track = {
      name: track.name,
      artists: track.artists.map((name) => ({ name })),
      album: { images: track.imageUrl ? [{ url: track.imageUrl }] : [] },
      duration_ms: track.durationMs,
      imageUrl: track.imageUrl,
    };
    state.paused = false;
    state.duration = track.durationMs;
    state.position = 0;
    renderNowPlaying();
    setStatus("Ready");
  } catch (err) {
    setError(err.message || String(err));
    setStatus("Ready");
  }
}

async function onSearch(event) {
  event.preventDefault();
  const query = els.searchInput.value.trim();
  state.query = query;
  setError("");

  if (!query) {
    state.results = [];
    renderResults();
    return;
  }

  setStatus("Searching…");
  els.searchBtn.disabled = true;
  try {
    const token = await ensureToken();
    if (!token) {
      showLoggedOut();
      throw new Error("Session expired — log in again.");
    }
    state.results = await searchTracks(token, query);
    renderResults();
    setStatus(
      state.results.length
        ? `${state.results.length} track${state.results.length === 1 ? "" : "s"}`
        : "No results",
    );
  } catch (err) {
    setError(err.message || String(err));
    setStatus("Ready");
  } finally {
    els.searchBtn.disabled = false;
  }
}

async function onLogin(event) {
  event.preventDefault();
  setError("");
  const clientId = saveClientId(els.clientId.value);
  els.clientId.value = clientId;
  try {
    await beginLogin({ clientId });
  } catch (err) {
    setError(err.message || String(err));
  }
}

function onLogout() {
  if (state.player) {
    try {
      state.player.disconnect();
    } catch {
      /* ignore */
    }
  }
  clearTokens();
  state.accessToken = null;
  state.deviceId = null;
  state.player = null;
  state.results = [];
  state.track = null;
  showLoggedOut();
  setStatus("");
  setError("");
}

function onPlayerEvent(event, payload) {
  if (event === "ready") {
    state.deviceId = payload.device_id;
    setStatus("Player ready — search and play");
    return;
  }
  if (event === "not_ready") {
    state.deviceId = null;
    setStatus("Player offline");
    return;
  }
  if (
    event === "initialization_error" ||
    event === "authentication_error" ||
    event === "account_error" ||
    event === "playback_error"
  ) {
    const message = payload?.message || event;
    if (event === "account_error") {
      setError(
        `${message} Web Playback requires a Spotify Premium account.`,
      );
    } else {
      setError(message);
    }
    return;
  }
  if (event === "player_state_changed") {
    if (!payload) return;
    state.paused = Boolean(payload.paused);
    state.position = payload.position || 0;
    state.duration = payload.duration || 0;
    state.track = payload.track_window?.current_track || state.track;
    renderNowPlaying();
  }
}

async function connectPlayer() {
  setStatus("Connecting player…");
  state.player = await createPlayer({
    getOAuthToken: (cb) => {
      void getValidAccessToken()
        .then((token) => {
          if (!token) throw new Error("Not authenticated");
          cb(token);
        })
        .catch((err) => {
          setError(err.message || String(err));
        });
    },
    onEvent: onPlayerEvent,
  });
}

async function bootstrapSession() {
  try {
    await handleAuthCallback();
  } catch (err) {
    setError(err.message || String(err));
  }

  const token = await ensureToken();
  if (!token) {
    showLoggedOut();
    return;
  }

  showLoggedIn();
  renderResults();
  try {
    await connectPlayer();
  } catch (err) {
    setError(err.message || String(err));
    setStatus("Ready");
  }
}

function bind() {
  els.gate = $("gate");
  els.app = $("app");
  els.clientId = $("client-id");
  els.loginForm = $("login-form");
  els.searchForm = $("search-form");
  els.searchInput = $("search-input");
  els.searchBtn = $("search-btn");
  els.results = $("results");
  els.error = $("error");
  els.status = $("status");
  els.logout = $("logout");
  els.nowPlaying = $("now-playing");
  els.npArt = $("np-art");
  els.npTitle = $("np-title");
  els.npArtist = $("np-artist");
  els.npTime = $("np-time");
  els.npProgress = $("np-progress");
  els.togglePlay = $("toggle-play");
  els.prev = $("prev");
  els.next = $("next");
  els.redirectHint = $("redirect-hint");

  els.clientId.value = loadClientId();
  const redirect = `${location.origin}${location.pathname.endsWith("/") ? location.pathname : `${location.pathname}/`}`;
  els.redirectHint.textContent = redirect;

  els.loginForm.addEventListener("submit", onLogin);
  els.searchForm.addEventListener("submit", onSearch);
  els.logout.addEventListener("click", onLogout);

  els.togglePlay.addEventListener("click", () => {
    state.player?.togglePlay();
  });
  els.prev.addEventListener("click", () => {
    state.player?.previousTrack();
  });
  els.next.addEventListener("click", () => {
    state.player?.nextTrack();
  });
}

export async function init() {
  bind();
  // Tokens may already exist from a previous visit.
  if (loadTokens()) {
    // keep gate hidden until bootstrap finishes to avoid flash
  }
  await bootstrapSession();
}

if (typeof document !== "undefined") {
  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", () => void init());
  } else {
    void init();
  }
}
