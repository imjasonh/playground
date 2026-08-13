// Password hashing: PBKDF2-SHA256 (Web Crypto). Stored as
//   pbkdf2$<iterations>$<saltHex>$<hashHex>
//
// Sessions: signed cookie containing "<expiresUnix>.<hmacHex>" — no DB row,
// rotates with SESSION_SECRET. The cookie is the auth itself; if you need
// revocation, change SESSION_SECRET.

// Workers runtime caps PBKDF2 at 100k iterations.
const PBKDF2_ITER = 100_000;
const PBKDF2_HASH = "SHA-256";
const PBKDF2_KEYLEN_BITS = 256;
const SESSION_TTL_SECONDS = 60 * 60 * 24 * 30; // 30 days
const CHALLENGE_TTL_SECONDS = 5 * 60; // 5 minutes
export const SESSION_COOKIE = "y_session";
export const CHALLENGE_COOKIE = "y_challenge";

const enc = new TextEncoder();

function toHex(bytes: ArrayBuffer | Uint8Array): string {
  const u8 = bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes);
  return [...u8].map((b) => b.toString(16).padStart(2, "0")).join("");
}

function fromHex(hex: string): Uint8Array {
  const out = new Uint8Array(hex.length / 2);
  for (let i = 0; i < out.length; i++) {
    out[i] = parseInt(hex.slice(i * 2, i * 2 + 2), 16);
  }
  return out;
}

async function pbkdf2(
  password: string,
  salt: Uint8Array,
  iterations: number,
): Promise<Uint8Array> {
  const keyMaterial = await crypto.subtle.importKey(
    "raw",
    enc.encode(password),
    "PBKDF2",
    false,
    ["deriveBits"],
  );
  const bits = await crypto.subtle.deriveBits(
    {
      name: "PBKDF2",
      salt: salt as BufferSource,
      iterations,
      hash: PBKDF2_HASH,
    },
    keyMaterial,
    PBKDF2_KEYLEN_BITS,
  );
  return new Uint8Array(bits);
}

export async function hashPassword(password: string): Promise<string> {
  const salt = new Uint8Array(16);
  crypto.getRandomValues(salt);
  const hash = await pbkdf2(password, salt, PBKDF2_ITER);
  return `pbkdf2$${PBKDF2_ITER}$${toHex(salt)}$${toHex(hash)}`;
}

export async function verifyPassword(
  password: string,
  stored: string,
): Promise<boolean> {
  const parts = stored.split("$");
  if (parts.length !== 4 || parts[0] !== "pbkdf2") return false;
  const iter = parseInt(parts[1], 10);
  const salt = fromHex(parts[2]);
  const expected = fromHex(parts[3]);
  const got = await pbkdf2(password, salt, iter);
  return constantTimeEqual(got, expected);
}

function constantTimeEqual(a: Uint8Array, b: Uint8Array): boolean {
  if (a.length !== b.length) return false;
  let diff = 0;
  for (let i = 0; i < a.length; i++) diff |= a[i] ^ b[i];
  return diff === 0;
}

async function hmacKey(secret: string): Promise<CryptoKey> {
  return crypto.subtle.importKey(
    "raw",
    enc.encode(secret),
    { name: "HMAC", hash: "SHA-256" },
    false,
    ["sign", "verify"],
  );
}

async function hmacHex(secret: string, message: string): Promise<string> {
  const key = await hmacKey(secret);
  const sig = await crypto.subtle.sign("HMAC", key, enc.encode(message));
  return toHex(sig);
}

export async function makeSessionCookie(
  secret: string,
  nowSeconds: number,
): Promise<string> {
  const expires = nowSeconds + SESSION_TTL_SECONDS;
  const payload = String(expires);
  const sig = await hmacHex(secret, payload);
  return `${payload}.${sig}`;
}

export async function verifySessionCookie(
  secret: string,
  raw: string | undefined,
  nowSeconds: number,
): Promise<boolean> {
  if (!raw) return false;
  const dot = raw.indexOf(".");
  if (dot < 0) return false;
  const payload = raw.slice(0, dot);
  const sig = raw.slice(dot + 1);
  const expected = await hmacHex(secret, payload);
  if (!constantTimeEqual(fromHex(sig), fromHex(expected))) return false;
  const expires = parseInt(payload, 10);
  if (!Number.isFinite(expires)) return false;
  return nowSeconds < expires;
}

// Short-lived signed cookie carrying a WebAuthn challenge across the
// options/verify roundtrip. Format: `<expires>.<challenge>.<hmac>`.
export const CHALLENGE_TTL = CHALLENGE_TTL_SECONDS;

export async function makeChallengeCookie(
  secret: string,
  challenge: string,
  nowSeconds: number,
): Promise<string> {
  const expires = nowSeconds + CHALLENGE_TTL_SECONDS;
  const payload = `${expires}.${challenge}`;
  const sig = await hmacHex(secret, payload);
  return `${payload}.${sig}`;
}

export async function verifyChallengeCookie(
  secret: string,
  raw: string | undefined,
  nowSeconds: number,
): Promise<string | null> {
  if (!raw) return null;
  const lastDot = raw.lastIndexOf(".");
  if (lastDot < 0) return null;
  const payload = raw.slice(0, lastDot);
  const sig = raw.slice(lastDot + 1);
  const expected = await hmacHex(secret, payload);
  if (!constantTimeEqual(fromHex(sig), fromHex(expected))) return null;
  const firstDot = payload.indexOf(".");
  if (firstDot < 0) return null;
  const expires = parseInt(payload.slice(0, firstDot), 10);
  if (!Number.isFinite(expires) || nowSeconds >= expires) return null;
  return payload.slice(firstDot + 1);
}
