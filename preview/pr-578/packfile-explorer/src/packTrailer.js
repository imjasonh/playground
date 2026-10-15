// Read and verify the packfile trailer.
//
// A pack ends with a 20-byte SHA-1 over every preceding byte. Recomputing it
// tells you the download wasn't truncated or corrupted, and it's the same
// checksum git prints as the pack name (`pack-<sha1>.pack`).

/**
 * Verify a pack's trailing SHA-1 against its contents.
 *
 * `parsed` is the `parsePack` result (for `trailerOffset`, `trailer`, `count`,
 * `version`). `sha1Hex(bytes)` returns the lowercase hex digest (async). Returns
 * `{ version, count, storedTrailer, computedTrailer, valid, bodyBytes }`.
 */
export async function verifyPackTrailer(packBytes, parsed, sha1Hex) {
  const body = packBytes.subarray(0, parsed.trailerOffset);
  const computed = await sha1Hex(body);
  return {
    version: parsed.version,
    count: parsed.count,
    storedTrailer: parsed.trailer,
    computedTrailer: computed,
    valid: computed === parsed.trailer,
    bodyBytes: parsed.trailerOffset,
  };
}
