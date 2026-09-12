// Parse resolved git object bytes (commit, tree, tag) into structured data.

import { bytesToHex, decodeUtf8 } from "./hex.js";

/** Parse a commit object body. */
export function parseCommit(data) {
  const text = decodeUtf8(data);
  const split = text.indexOf("\n\n");
  const headerText = split === -1 ? text : text.slice(0, split);
  const message = split === -1 ? "" : text.slice(split + 2);

  const commit = { tree: null, parents: [], author: null, committer: null, message, headers: [] };
  for (const line of headerText.split("\n")) {
    const sp = line.indexOf(" ");
    if (sp === -1) continue;
    const key = line.slice(0, sp);
    const value = line.slice(sp + 1);
    commit.headers.push({ key, value });
    if (key === "tree") commit.tree = value;
    else if (key === "parent") commit.parents.push(value);
    else if (key === "author") commit.author = parseIdentity(value);
    else if (key === "committer") commit.committer = parseIdentity(value);
  }
  return commit;
}

/** Parse a `name <email> timestamp tz` identity line. */
export function parseIdentity(value) {
  const match = value.match(/^(.*?) <([^>]*)> (\d+) ([+-]\d{4})$/);
  if (!match) return { raw: value };
  const [, name, email, ts, tz] = match;
  return {
    raw: value,
    name,
    email,
    timestamp: Number(ts),
    tz,
    date: new Date(Number(ts) * 1000),
  };
}

const MODE_TYPE = {
  "40000": "tree",
  "040000": "tree",
  "160000": "commit",
  "120000": "blob",
};

/** Map a tree entry mode string to the referenced object type. */
export function treeEntryType(mode) {
  if (MODE_TYPE[mode]) return MODE_TYPE[mode];
  if (mode.startsWith("100")) return "blob";
  return "blob";
}

/** Parse a tree object body into `{ mode, name, oid, type }` entries. */
export function parseTree(data) {
  const entries = [];
  let at = 0;
  while (at < data.length) {
    let sp = at;
    while (sp < data.length && data[sp] !== 0x20) sp += 1;
    const mode = decodeUtf8(data.subarray(at, sp));
    let nul = sp + 1;
    while (nul < data.length && data[nul] !== 0x00) nul += 1;
    const name = decodeUtf8(data.subarray(sp + 1, nul));
    const oid = bytesToHex(data.subarray(nul + 1, nul + 21));
    at = nul + 21;
    entries.push({ mode, name, oid, type: treeEntryType(mode) });
  }
  return entries;
}

/** Parse a tag object body. */
export function parseTag(data) {
  const text = decodeUtf8(data);
  const split = text.indexOf("\n\n");
  const headerText = split === -1 ? text : text.slice(0, split);
  const message = split === -1 ? "" : text.slice(split + 2);
  const tag = { object: null, type: null, tag: null, tagger: null, message };
  for (const line of headerText.split("\n")) {
    const sp = line.indexOf(" ");
    if (sp === -1) continue;
    const key = line.slice(0, sp);
    const value = line.slice(sp + 1);
    if (key === "object") tag.object = value;
    else if (key === "type") tag.type = value;
    else if (key === "tag") tag.tag = value;
    else if (key === "tagger") tag.tagger = parseIdentity(value);
  }
  return tag;
}

/** Heuristic: does a blob look like binary (has NUL in the first 8000 bytes)? */
export function looksBinary(data) {
  const limit = Math.min(data.length, 8000);
  for (let i = 0; i < limit; i += 1) {
    if (data[i] === 0) return true;
  }
  return false;
}
