/**
 * Spotify Web Playback SDK wrapper.
 * Loads https://sdk.scdn.co/spotify-player.js and exposes connect/control helpers.
 */

const SDK_SRC = "https://sdk.scdn.co/spotify-player.js";

/**
 * Ensure the Web Playback SDK script is loaded, then wait for readiness.
 * @param {{ document?: Document, window?: Window }} [env]
 * @returns {Promise<typeof window.Spotify>}
 */
export function loadSdk(env = {}) {
  const doc = env.document || globalThis.document;
  const win = env.window || globalThis;

  if (win.Spotify?.Player) {
    return Promise.resolve(win.Spotify);
  }

  return new Promise((resolve, reject) => {
    const previous = win.onSpotifyWebPlaybackSDKReady;
    const timeout = setTimeout(() => {
      reject(new Error("Timed out loading the Spotify Web Playback SDK."));
    }, 20_000);

    win.onSpotifyWebPlaybackSDKReady = () => {
      clearTimeout(timeout);
      if (typeof previous === "function") previous();
      resolve(win.Spotify);
    };

    const existing = doc.querySelector(`script[src="${SDK_SRC}"]`);
    if (existing) return;

    const script = doc.createElement("script");
    script.src = SDK_SRC;
    script.async = true;
    script.onerror = () => {
      clearTimeout(timeout);
      reject(new Error("Failed to load the Spotify Web Playback SDK script."));
    };
    doc.body.appendChild(script);
  });
}

/**
 * Create and connect a Spotify.Player.
 * @param {object} options
 * @param {(cb: (token: string) => void) => void} options.getOAuthToken
 * @param {(event: string, payload: unknown) => void} [options.onEvent]
 * @param {string} [options.name]
 * @param {number} [options.volume]
 * @param {{ document?: Document, window?: Window }} [options.env]
 */
export async function createPlayer({
  getOAuthToken,
  onEvent,
  name = "Playground Spotify",
  volume = 0.7,
  env = {},
} = {}) {
  const Spotify = await loadSdk(env);
  const player = new Spotify.Player({
    name,
    getOAuthToken,
    volume,
  });

  const emit = (event) => (payload) => {
    if (typeof onEvent === "function") onEvent(event, payload);
  };

  for (const event of [
    "ready",
    "not_ready",
    "player_state_changed",
    "initialization_error",
    "authentication_error",
    "account_error",
    "playback_error",
  ]) {
    player.addListener(event, emit(event));
  }

  const connected = await player.connect();
  if (!connected) {
    throw new Error("Spotify player failed to connect.");
  }

  return player;
}
