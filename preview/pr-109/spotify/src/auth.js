/**
 * Authorization Code + PKCE helpers for Spotify SPA auth.
 * @see https://developer.spotify.com/documentation/web-api/tutorials/code-pkce-flow
 */

import {
  AUTH_URL,
  SCOPES,
  STORAGE_KEYS,
  TOKEN_URL,
  loadClientId,
  redirectUri,
} from "./config.js";

const encoder = new TextEncoder();

/** Cryptographically random code verifier (43–128 chars). */
export function generateCodeVerifier(length = 64) {
  const charset =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-._~";
  const bytes = new Uint8Array(length);
  crypto.getRandomValues(bytes);
  return Array.from(bytes, (b) => charset[b % charset.length]).join("");
}

export async function sha256Base64Url(plain) {
  const digest = await crypto.subtle.digest("SHA-256", encoder.encode(plain));
  return base64UrlEncode(new Uint8Array(digest));
}

export function base64UrlEncode(bytes) {
  let binary = "";
  for (const byte of bytes) binary += String.fromCharCode(byte);
  return btoa(binary).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
}

export async function generateCodeChallenge(verifier) {
  return sha256Base64Url(verifier);
}

/**
 * @param {object} tokens
 * @param {string} tokens.access_token
 * @param {string} [tokens.refresh_token]
 * @param {number|string} [tokens.expires_in] seconds until expiry
 * @param {number} [tokens.expires_at] absolute ms timestamp
 */
export function normalizeTokens(tokens, now = Date.now()) {
  if (!tokens?.access_token) {
    throw new Error("Token response missing access_token");
  }
  const expiresIn = Number(tokens.expires_in) || 3600;
  const expiresAt =
    typeof tokens.expires_at === "number"
      ? tokens.expires_at
      : now + expiresIn * 1000;
  return {
    access_token: tokens.access_token,
    refresh_token: tokens.refresh_token || null,
    expires_at: expiresAt,
    token_type: tokens.token_type || "Bearer",
  };
}

export function isTokenExpired(tokens, now = Date.now(), skewMs = 60_000) {
  if (!tokens?.access_token || !tokens.expires_at) return true;
  return now >= tokens.expires_at - skewMs;
}

export function loadTokens(storage = globalThis.localStorage) {
  if (!storage) return null;
  const raw = storage.getItem(STORAGE_KEYS.tokens);
  if (!raw) return null;
  try {
    return normalizeTokens(JSON.parse(raw));
  } catch {
    storage.removeItem(STORAGE_KEYS.tokens);
    return null;
  }
}

export function saveTokens(tokens, storage = globalThis.localStorage) {
  const normalized = normalizeTokens(tokens);
  if (storage) storage.setItem(STORAGE_KEYS.tokens, JSON.stringify(normalized));
  return normalized;
}

export function clearTokens(storage = globalThis.localStorage) {
  if (!storage) return;
  storage.removeItem(STORAGE_KEYS.tokens);
  storage.removeItem(STORAGE_KEYS.verifier);
  storage.removeItem(`${STORAGE_KEYS.verifier}.state`);
}

export function buildAuthorizeUrl({
  clientId,
  verifier,
  challenge,
  state,
  redirect,
}) {
  const params = new URLSearchParams({
    client_id: clientId,
    response_type: "code",
    redirect_uri: redirect,
    scope: SCOPES,
    code_challenge_method: "S256",
    code_challenge: challenge,
    state,
  });
  return `${AUTH_URL}?${params}`;
}

/**
 * Start the Spotify login redirect. Persists the PKCE verifier for the callback.
 */
export async function beginLogin({
  clientId = loadClientId(),
  storage = globalThis.localStorage,
  location = globalThis.location,
  assign = (url) => {
    location.assign(url);
  },
} = {}) {
  const id = String(clientId || "").trim();
  if (!id) throw new Error("Enter your Spotify Client ID before logging in.");

  const verifier = generateCodeVerifier();
  const challenge = await generateCodeChallenge(verifier);
  const state = generateCodeVerifier(32);
  storage.setItem(STORAGE_KEYS.verifier, verifier);
  storage.setItem(`${STORAGE_KEYS.verifier}.state`, state);

  const url = buildAuthorizeUrl({
    clientId: id,
    verifier,
    challenge,
    state,
    redirect: redirectUri(location),
  });
  assign(url);
  return url;
}

export async function exchangeCodeForTokens({
  code,
  clientId = loadClientId(),
  storage = globalThis.localStorage,
  location = globalThis.location,
  fetchImpl = globalThis.fetch,
} = {}) {
  const verifier = storage.getItem(STORAGE_KEYS.verifier);
  if (!verifier) {
    throw new Error("Missing PKCE verifier — start login again.");
  }
  if (!clientId) {
    throw new Error("Missing Spotify Client ID.");
  }

  const body = new URLSearchParams({
    client_id: clientId,
    grant_type: "authorization_code",
    code,
    redirect_uri: redirectUri(location),
    code_verifier: verifier,
  });

  const response = await fetchImpl(TOKEN_URL, {
    method: "POST",
    headers: { "Content-Type": "application/x-www-form-urlencoded" },
    body,
  });

  const data = await response.json().catch(() => ({}));
  if (!response.ok) {
    const detail = data.error_description || data.error || response.statusText;
    throw new Error(`Token exchange failed: ${detail}`);
  }

  storage.removeItem(STORAGE_KEYS.verifier);
  storage.removeItem(`${STORAGE_KEYS.verifier}.state`);
  return saveTokens(data, storage);
}

export async function refreshAccessToken({
  refreshToken,
  clientId = loadClientId(),
  storage = globalThis.localStorage,
  fetchImpl = globalThis.fetch,
} = {}) {
  if (!refreshToken) throw new Error("No refresh token available.");
  if (!clientId) throw new Error("Missing Spotify Client ID.");

  const body = new URLSearchParams({
    client_id: clientId,
    grant_type: "refresh_token",
    refresh_token: refreshToken,
  });

  const response = await fetchImpl(TOKEN_URL, {
    method: "POST",
    headers: { "Content-Type": "application/x-www-form-urlencoded" },
    body,
  });

  const data = await response.json().catch(() => ({}));
  if (!response.ok) {
    const detail = data.error_description || data.error || response.statusText;
    throw new Error(`Token refresh failed: ${detail}`);
  }

  // Spotify may omit refresh_token on refresh; keep the previous one.
  if (!data.refresh_token) data.refresh_token = refreshToken;
  return saveTokens(data, storage);
}

/**
 * Return a valid access token, refreshing when needed.
 */
export async function getValidAccessToken({
  storage = globalThis.localStorage,
  fetchImpl = globalThis.fetch,
  now = Date.now(),
} = {}) {
  let tokens = loadTokens(storage);
  if (!tokens) return null;

  if (!isTokenExpired(tokens, now)) {
    return tokens.access_token;
  }

  if (!tokens.refresh_token) {
    clearTokens(storage);
    return null;
  }

  tokens = await refreshAccessToken({
    refreshToken: tokens.refresh_token,
    clientId: loadClientId(storage),
    storage,
    fetchImpl,
  });
  return tokens.access_token;
}

/**
 * Handle `?code=` / `?error=` after Spotify redirects back.
 * Clears the query string from the address bar when done.
 * @returns {Promise<'ok'|'error'|'none'>}
 */
export async function handleAuthCallback({
  storage = globalThis.localStorage,
  location = globalThis.location,
  history = globalThis.history,
  fetchImpl = globalThis.fetch,
} = {}) {
  const params = new URLSearchParams(location.search);
  const error = params.get("error");
  const code = params.get("code");
  const state = params.get("state");

  if (!error && !code) return "none";

  const cleanUrl = `${location.pathname}${location.hash || ""}`;
  history.replaceState({}, "", cleanUrl);

  if (error) {
    throw new Error(`Spotify authorization denied: ${error}`);
  }

  const expected = storage.getItem(`${STORAGE_KEYS.verifier}.state`);
  if (expected && state && expected !== state) {
    throw new Error("OAuth state mismatch — try logging in again.");
  }

  await exchangeCodeForTokens({
    code,
    clientId: loadClientId(storage),
    storage,
    location,
    fetchImpl,
  });
  return "ok";
}
