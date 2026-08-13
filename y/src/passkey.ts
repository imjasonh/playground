// Passkey (WebAuthn) glue around @simplewebauthn/server.
//
// Single-user model: there is exactly one virtual user; credentials are not
// scoped per-user. RP ID and origin are derived from SITE_URL.

import {
  generateAuthenticationOptions,
  generateRegistrationOptions,
  verifyAuthenticationResponse,
  verifyRegistrationResponse,
} from "@simplewebauthn/server";
import type {
  AuthenticationResponseJSON,
  PublicKeyCredentialCreationOptionsJSON,
  PublicKeyCredentialRequestOptionsJSON,
  RegistrationResponseJSON,
  WebAuthnCredential,
} from "@simplewebauthn/types";

export const RP_NAME_DEFAULT = "y";
// Single virtual user; the user handle is opaque to WebAuthn but must be
// consistent across registrations to let the authenticator dedupe.
const USER_HANDLE = "y-admin";
const USER_NAME = "admin";

export interface StoredCredential {
  id: number;
  credential_id: string; // base64url
  public_key: Uint8Array;
  counter: number;
  transports: string | null; // comma-separated
  label: string;
  created_at: number;
}

export interface RpContext {
  rpID: string;
  origin: string;
  rpName: string;
}

export function rpFromEnv(env: Env): RpContext {
  const u = new URL(env.SITE_URL);
  return {
    rpID: u.hostname,
    origin: `${u.protocol}//${u.host}`,
    rpName: env.SITE_TITLE || RP_NAME_DEFAULT,
  };
}

// ---- DB helpers ----

export async function listCredentials(
  db: D1Database,
): Promise<StoredCredential[]> {
  const { results } = await db
    .prepare(
      "SELECT id, credential_id, public_key, counter, transports, label, created_at FROM credentials ORDER BY created_at",
    )
    .all<StoredCredential>();
  // D1 returns BLOB columns as ArrayBuffer; normalize to Uint8Array.
  return results.map((r) => ({
    ...r,
    public_key:
      r.public_key instanceof Uint8Array
        ? r.public_key
        : new Uint8Array(r.public_key as unknown as ArrayBuffer),
  }));
}

export async function findCredentialByCredentialId(
  db: D1Database,
  credentialId: string,
): Promise<StoredCredential | null> {
  const row = await db
    .prepare(
      "SELECT id, credential_id, public_key, counter, transports, label, created_at FROM credentials WHERE credential_id = ?1",
    )
    .bind(credentialId)
    .first<StoredCredential>();
  if (!row) return null;
  return {
    ...row,
    public_key:
      row.public_key instanceof Uint8Array
        ? row.public_key
        : new Uint8Array(row.public_key as unknown as ArrayBuffer),
  };
}

export async function countCredentials(db: D1Database): Promise<number> {
  const row = await db
    .prepare("SELECT COUNT(*) AS n FROM credentials")
    .first<{ n: number }>();
  return row?.n ?? 0;
}

export async function insertCredential(
  db: D1Database,
  cred: {
    credentialId: string;
    publicKey: Uint8Array;
    counter: number;
    transports: string[] | undefined;
    label: string;
  },
  createdAt: number,
): Promise<void> {
  await db
    .prepare(
      `INSERT INTO credentials (credential_id, public_key, counter, transports, label, created_at)
       VALUES (?1, ?2, ?3, ?4, ?5, ?6)`,
    )
    .bind(
      cred.credentialId,
      cred.publicKey,
      cred.counter,
      cred.transports?.join(",") ?? null,
      cred.label,
      createdAt,
    )
    .run();
}

export async function updateCredentialCounter(
  db: D1Database,
  credentialId: string,
  counter: number,
): Promise<void> {
  await db
    .prepare("UPDATE credentials SET counter = ?1 WHERE credential_id = ?2")
    .bind(counter, credentialId)
    .run();
}

export async function deleteCredential(
  db: D1Database,
  id: number,
): Promise<void> {
  await db.prepare("DELETE FROM credentials WHERE id = ?1").bind(id).run();
}

// ---- WebAuthn flows ----

export async function buildRegistrationOptions(
  env: Env,
): Promise<PublicKeyCredentialCreationOptionsJSON> {
  const { rpID, rpName } = rpFromEnv(env);
  const existing = await listCredentials(env.DB);
  return generateRegistrationOptions({
    rpName,
    rpID,
    userID: new TextEncoder().encode(USER_HANDLE),
    userName: USER_NAME,
    attestationType: "none",
    excludeCredentials: existing.map((c) => ({
      id: c.credential_id,
      transports: parseTransports(c.transports),
    })),
    authenticatorSelection: {
      residentKey: "preferred",
      userVerification: "preferred",
    },
  });
}

export async function verifyRegistration(
  env: Env,
  expectedChallenge: string,
  response: RegistrationResponseJSON,
  label: string,
): Promise<{ ok: true } | { ok: false; reason: string }> {
  const { rpID, origin } = rpFromEnv(env);
  let result;
  try {
    result = await verifyRegistrationResponse({
      response,
      expectedChallenge,
      expectedOrigin: origin,
      expectedRPID: rpID,
    });
  } catch (err) {
    return { ok: false, reason: err instanceof Error ? err.message : "verification failed" };
  }
  if (!result.verified || !result.registrationInfo) {
    return { ok: false, reason: "not verified" };
  }
  const info = result.registrationInfo;
  const cred: WebAuthnCredential = info.credential;
  await insertCredential(
    env.DB,
    {
      credentialId: cred.id,
      publicKey: cred.publicKey,
      counter: cred.counter,
      transports: response.response.transports,
      label: label || "passkey",
    },
    Math.floor(Date.now() / 1000),
  );
  return { ok: true };
}

export async function buildAuthenticationOptions(
  env: Env,
): Promise<PublicKeyCredentialRequestOptionsJSON> {
  const { rpID } = rpFromEnv(env);
  const creds = await listCredentials(env.DB);
  return generateAuthenticationOptions({
    rpID,
    userVerification: "preferred",
    allowCredentials: creds.map((c) => ({
      id: c.credential_id,
      transports: parseTransports(c.transports),
    })),
  });
}

export async function verifyAuthentication(
  env: Env,
  expectedChallenge: string,
  response: AuthenticationResponseJSON,
): Promise<{ ok: true } | { ok: false; reason: string }> {
  const { rpID, origin } = rpFromEnv(env);
  const stored = await findCredentialByCredentialId(env.DB, response.id);
  if (!stored) return { ok: false, reason: "unknown credential" };

  const credential: WebAuthnCredential = {
    id: stored.credential_id,
    publicKey: stored.public_key,
    counter: stored.counter,
    transports: parseTransports(stored.transports),
  };

  let result;
  try {
    result = await verifyAuthenticationResponse({
      response,
      expectedChallenge,
      expectedOrigin: origin,
      expectedRPID: rpID,
      credential,
    });
  } catch (err) {
    return { ok: false, reason: err instanceof Error ? err.message : "verification failed" };
  }
  if (!result.verified) return { ok: false, reason: "not verified" };

  await updateCredentialCounter(
    env.DB,
    response.id,
    result.authenticationInfo.newCounter,
  );
  return { ok: true };
}

function parseTransports(s: string | null): WebAuthnCredential["transports"] {
  if (!s) return undefined;
  return s.split(",").filter(Boolean) as WebAuthnCredential["transports"];
}
