import test from "node:test";
import assert from "node:assert/strict";
import { webcrypto } from "node:crypto";

import {
  AUTH_URL,
  SCOPES,
  STORAGE_KEYS,
  loadClientId,
  redirectUri,
  saveClientId,
} from "../src/config.js";
import {
  base64UrlEncode,
  buildAuthorizeUrl,
  clearTokens,
  exchangeCodeForTokens,
  generateCodeChallenge,
  generateCodeVerifier,
  getValidAccessToken,
  handleAuthCallback,
  isTokenExpired,
  loadTokens,
  normalizeTokens,
  refreshAccessToken,
  saveTokens,
  sha256Base64Url,
} from "../src/auth.js";

if (!globalThis.crypto) {
  globalThis.crypto = webcrypto;
}

function memoryStorage(seed = {}) {
  const map = new Map(Object.entries(seed));
  return {
    getItem: (key) => (map.has(key) ? map.get(key) : null),
    setItem: (key, value) => {
      map.set(key, String(value));
    },
    removeItem: (key) => {
      map.delete(key);
    },
  };
}

test("redirectUri keeps a trailing slash for directory-style Pages URLs", () => {
  assert.equal(
    redirectUri({ origin: "https://example.com", pathname: "/playground/spotify" }),
    "https://example.com/playground/spotify/",
  );
  assert.equal(
    redirectUri({ origin: "http://localhost:3000", pathname: "/" }),
    "http://localhost:3000/",
  );
});

test("client id persists trimmed values and clears blanks", () => {
  const storage = memoryStorage();
  assert.equal(saveClientId("  abc123  ", storage), "abc123");
  assert.equal(loadClientId(storage), "abc123");
  assert.equal(saveClientId("   ", storage), "");
  assert.equal(loadClientId(storage), "");
});

test("code verifier is URL-safe and long enough for PKCE", () => {
  const verifier = generateCodeVerifier(64);
  assert.equal(verifier.length, 64);
  assert.match(verifier, /^[A-Za-z0-9\-._~]+$/);
});

test("sha256 base64url challenge matches a known vector", async () => {
  // RFC 7636 appendix B
  const verifier = "dBjftJeZ4CVP-mB92K27uhbUJU1p1r_wW1gFWFOEjXk";
  const challenge = await generateCodeChallenge(verifier);
  assert.equal(challenge, "E9Melhoa2OwvFrEMTJguCHaoeK1t8URWbuGJSstw-cM");
  assert.equal(await sha256Base64Url(verifier), challenge);
});

test("base64UrlEncode strips padding and uses URL alphabet", () => {
  assert.equal(base64UrlEncode(new Uint8Array([0xff, 0xef])), "_-8");
});

test("normalizeTokens computes expires_at from expires_in", () => {
  const tokens = normalizeTokens(
    { access_token: "a", refresh_token: "r", expires_in: 3600 },
    1_000_000,
  );
  assert.equal(tokens.expires_at, 1_000_000 + 3_600_000);
  // 60s skew: still valid well before expiry
  assert.equal(isTokenExpired(tokens, 1_000_000), false);
  assert.equal(isTokenExpired(tokens, 1_000_000 + 3_540_000), true);
});

test("buildAuthorizeUrl includes PKCE params and streaming scopes", () => {
  const url = new URL(
    buildAuthorizeUrl({
      clientId: "cid",
      verifier: "v",
      challenge: "ch",
      state: "st",
      redirect: "http://localhost:3000/",
    }),
  );
  assert.equal(url.origin + url.pathname, AUTH_URL);
  assert.equal(url.searchParams.get("client_id"), "cid");
  assert.equal(url.searchParams.get("response_type"), "code");
  assert.equal(url.searchParams.get("code_challenge_method"), "S256");
  assert.equal(url.searchParams.get("code_challenge"), "ch");
  assert.equal(url.searchParams.get("state"), "st");
  assert.equal(url.searchParams.get("redirect_uri"), "http://localhost:3000/");
  assert.equal(url.searchParams.get("scope"), SCOPES);
  assert.match(SCOPES, /streaming/);
});

test("save/load/clear tokens round-trip through storage", () => {
  const storage = memoryStorage();
  saveTokens(
    { access_token: "tok", refresh_token: "ref", expires_in: 120 },
    storage,
  );
  const loaded = loadTokens(storage);
  assert.equal(loaded.access_token, "tok");
  assert.equal(loaded.refresh_token, "ref");
  clearTokens(storage);
  assert.equal(loadTokens(storage), null);
  assert.equal(storage.getItem(STORAGE_KEYS.tokens), null);
});

test("exchangeCodeForTokens posts PKCE body and stores the result", async () => {
  const storage = memoryStorage({
    [STORAGE_KEYS.verifier]: "verifier-value",
    [STORAGE_KEYS.clientId]: "cid",
  });
  const calls = [];
  const fetchImpl = async (url, init) => {
    calls.push({ url, init });
    return {
      ok: true,
      json: async () => ({
        access_token: "access",
        refresh_token: "refresh",
        expires_in: 3600,
        token_type: "Bearer",
      }),
    };
  };

  const tokens = await exchangeCodeForTokens({
    code: "auth-code",
    clientId: "cid",
    storage,
    location: { origin: "http://localhost:3000", pathname: "/" },
    fetchImpl,
  });

  assert.equal(tokens.access_token, "access");
  assert.equal(storage.getItem(STORAGE_KEYS.verifier), null);
  assert.equal(calls.length, 1);
  assert.equal(calls[0].url, "https://accounts.spotify.com/api/token");
  const body = String(calls[0].init.body);
  assert.match(body, /grant_type=authorization_code/);
  assert.match(body, /code=auth-code/);
  assert.match(body, /code_verifier=verifier-value/);
  assert.match(body, /client_id=cid/);
});

test("refreshAccessToken keeps previous refresh token when omitted", async () => {
  const storage = memoryStorage({ [STORAGE_KEYS.clientId]: "cid" });
  const fetchImpl = async () => ({
    ok: true,
    json: async () => ({
      access_token: "new-access",
      expires_in: 3600,
    }),
  });

  const tokens = await refreshAccessToken({
    refreshToken: "old-refresh",
    clientId: "cid",
    storage,
    fetchImpl,
  });

  assert.equal(tokens.access_token, "new-access");
  assert.equal(tokens.refresh_token, "old-refresh");
});

test("getValidAccessToken refreshes when expired", async () => {
  const storage = memoryStorage({
    [STORAGE_KEYS.clientId]: "cid",
    [STORAGE_KEYS.tokens]: JSON.stringify({
      access_token: "old",
      refresh_token: "ref",
      expires_at: 1,
    }),
  });
  let refreshed = false;
  const fetchImpl = async () => {
    refreshed = true;
    return {
      ok: true,
      json: async () => ({
        access_token: "fresh",
        refresh_token: "ref",
        expires_in: 3600,
      }),
    };
  };

  const token = await getValidAccessToken({
    storage,
    fetchImpl,
    now: 10_000,
  });
  assert.equal(token, "fresh");
  assert.equal(refreshed, true);
});

test("handleAuthCallback exchanges code and cleans the URL", async () => {
  const storage = memoryStorage({
    [STORAGE_KEYS.clientId]: "cid",
    [STORAGE_KEYS.verifier]: "verifier",
    [`${STORAGE_KEYS.verifier}.state`]: "expected",
  });
  const historyCalls = [];
  const result = await handleAuthCallback({
    storage,
    location: {
      search: "?code=abc&state=expected",
      pathname: "/spotify/",
      hash: "",
      origin: "http://localhost:3000",
    },
    history: {
      replaceState: (_s, _t, url) => historyCalls.push(url),
    },
    fetchImpl: async () => ({
      ok: true,
      json: async () => ({
        access_token: "access",
        refresh_token: "refresh",
        expires_in: 3600,
      }),
    }),
  });

  assert.equal(result, "ok");
  assert.deepEqual(historyCalls, ["/spotify/"]);
  assert.equal(loadTokens(storage).access_token, "access");
});
