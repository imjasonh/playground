// Fetch a repository's refs and packfile over smart-HTTP through the CORS proxy.
//
// This is the only module that touches the network. Everything it returns is
// plain bytes/structures that the pure parser modules consume.

import { buildFetchRequest, parseInfoRefs, splitUploadPackResult } from "./protocol.js";
import { demuxSideband } from "./pktline.js";
import { infoRefsUrl, proxied, uploadPackUrl } from "./proxy.js";

/** Fetch and parse the info/refs advertisement. */
export async function fetchRefs(proxyBase, base) {
  const url = proxied(proxyBase, infoRefsUrl(base));
  const res = await fetch(url, {
    headers: { Accept: "application/x-git-upload-pack-advertisement" },
  });
  if (!res.ok) {
    throw new Error(`info/refs failed: HTTP ${res.status}`);
  }
  const bytes = new Uint8Array(await res.arrayBuffer());
  const parsed = parseInfoRefs(bytes);
  if (parsed.refs.length === 0) {
    throw new Error("no refs advertised (is this a git repository?)");
  }
  return parsed;
}

/**
 * Fetch a packfile for the given wants. `deepen` requests a shallow clone.
 * Returns `{ pack, progress, control }`.
 */
export async function fetchPack(proxyBase, base, { wants, deepen = 1 }) {
  const body = buildFetchRequest({ wants, deepen });
  const url = proxied(proxyBase, uploadPackUrl(base));
  const res = await fetch(url, {
    method: "POST",
    headers: {
      "Content-Type": "application/x-git-upload-pack-request",
      Accept: "application/x-git-upload-pack-result",
    },
    body,
  });
  if (!res.ok) {
    throw new Error(`upload-pack failed: HTTP ${res.status}`);
  }
  const bytes = new Uint8Array(await res.arrayBuffer());
  const { control, sidebandLines } = splitUploadPackResult(bytes);
  const { pack, progress, error } = demuxSideband(sidebandLines);
  if (error) throw new Error(`server error: ${error.trim()}`);
  if (pack.length === 0) {
    throw new Error("no pack data returned");
  }
  return { pack, progress, control };
}
