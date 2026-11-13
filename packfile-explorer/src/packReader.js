// Readers that hand the streaming parser bytes without holding the whole pack.
//
// A 50 GiB packfile can't be one ArrayBuffer (browsers cap a single buffer
// around 2 GiB and RAM caps it sooner), so the streaming index reads ranges on
// demand. A reader exposes its total `size` and an async `read(offset, length)`
// that returns a `Uint8Array` of the bytes actually available (possibly short
// at end of input). `bytesReader` wraps an in-memory buffer (tests, small
// packs); `blobReader` wraps a `File`/`Blob` and slices it so the browser
// keeps only the current window resident.

/** A reader over an in-memory `Uint8Array`. */
export function bytesReader(bytes) {
  return {
    size: bytes.length,
    async read(offset, length) {
      const start = Math.max(0, Math.min(offset, bytes.length));
      const end = Math.max(start, Math.min(offset + length, bytes.length));
      return bytes.subarray(start, end);
    },
  };
}

/** A reader over a `Blob`/`File`, reading each window with `slice`. */
export function blobReader(blob) {
  return {
    size: blob.size,
    async read(offset, length) {
      const start = Math.max(0, Math.min(offset, blob.size));
      const end = Math.max(start, Math.min(offset + length, blob.size));
      if (end <= start) return new Uint8Array(0);
      return new Uint8Array(await blob.slice(start, end).arrayBuffer());
    },
  };
}
