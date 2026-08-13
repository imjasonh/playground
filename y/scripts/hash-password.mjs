#!/usr/bin/env node
// Reads a password from stdin (or argv[2]) and prints a hash matching
// src/auth.ts's verifyPassword format. Run: `node scripts/hash-password.mjs`.

import { webcrypto, randomBytes } from "node:crypto";
import { stdin } from "node:process";

const ITER = 100_000;
const enc = new TextEncoder();

const toHex = (b) =>
  [...new Uint8Array(b)].map((x) => x.toString(16).padStart(2, "0")).join("");

async function pbkdf2(password, salt, iter) {
  const km = await webcrypto.subtle.importKey(
    "raw",
    enc.encode(password),
    "PBKDF2",
    false,
    ["deriveBits"],
  );
  return webcrypto.subtle.deriveBits(
    { name: "PBKDF2", salt, iterations: iter, hash: "SHA-256" },
    km,
    256,
  );
}

async function readStdin() {
  let data = "";
  for await (const chunk of stdin) data += chunk;
  return data.trim();
}

const password = process.argv[2] ?? (await readStdin());
if (!password) {
  console.error("usage: hash-password.mjs <password>   (or pipe via stdin)");
  process.exit(2);
}

const salt = randomBytes(16);
const hash = await pbkdf2(password, salt, ITER);
console.log(`pbkdf2$${ITER}$${toHex(salt)}$${toHex(hash)}`);
