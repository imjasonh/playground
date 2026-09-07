// Fetch a repository's refs and packfile over smart-HTTP through the CORS proxy.
//
// This is the only module that touches the network. Everything it returns is
// plain bytes/structures that the pure parser modules consume.

import { buildFetchRequest, parseInfoRefs, splitUploadPackResult } from "./protocol.js";
import { createUploadPackReader, demuxSideband } from "./pktline.js";
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
 *
 * When the response body streams, side-band progress is reported live through
 * `onProgress(text)`; otherwise the whole body is demuxed at once. `wants` must
 * be a non-empty list of oids. Returns `{ pack, progress, control }`.
 */
export async function fetchPack(proxyBase, base, { wants, deepen = 1, onProgress = null }) {
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

  let result;
  if (res.body && typeof res.body.getReader === "function") {
    const reader = createUploadPackReader({ onProgress });
    const streamReader = res.body.getReader();
    for (;;) {
      const { value, done } = await streamReader.read();
      if (done) break;
      if (value && value.length) reader.push(value instanceof Uint8Array ? value : new Uint8Array(value));
    }
    result = reader.finish();
  } else {
    const bytes = new Uint8Array(await res.arrayBuffer());
    const { sidebandLines } = splitUploadPackResult(bytes);
    const { pack, progress, error } = demuxSideband(sidebandLines);
    result = { pack, progress, error, control: [] };
  }

  if (result.error) throw new Error(`server error: ${result.error.trim()}`);
  if (result.pack.length === 0) {
    throw new Error("no pack data returned");
  }
  return { pack: result.pack, progress: result.progress, control: result.control };
}
