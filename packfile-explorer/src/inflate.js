// A zlib inflater that reports how many compressed bytes it consumed.
//
// Pack parsing needs the consumed byte count to find the next entry, but the
// entries don't record their compressed length. pako's streaming `Inflate`
// exposes `strm.total_in`, but its high-level `push` auto-resets on any bytes
// that follow a complete zlib member (its concatenated-stream handling), which
// corrupts `total_in` for the packed bytes that trail each object.
//
// That reset is gated on `wrap > 0`, so raw inflate (negative windowBits) skips
// it. Git objects use a plain 2-byte zlib header and a 4-byte adler32 trailer
// with no preset dictionary, so we strip the header, raw-inflate the deflate
// blocks (which stop cleanly at the final block regardless of trailing bytes),
// and add the 2 header + 4 trailer bytes back to get the member length.

const ZLIB_HEADER = 2;
const ADLER32 = 4;

/**
 * Build an `inflate(bytes, offset)` function from the pako module.
 *
 * Returns `{ data: Uint8Array, consumed: number }`, where `consumed` is the
 * length of the whole zlib member starting at `offset`.
 */
export function makePakoInflate(pako) {
  return (bytes, offset) => {
    const cmf = bytes[offset];
    const flg = bytes[offset + 1];
    if ((cmf & 0x0f) !== 0x08) {
      throw new Error(`not a zlib stream at offset ${offset}: cmf=0x${cmf.toString(16)}`);
    }
    if (flg & 0x20) {
      throw new Error(`unexpected preset dictionary in zlib stream at offset ${offset}`);
    }

    const inflator = new pako.Inflate({ windowBits: -15 });
    inflator.push(bytes.subarray(offset + ZLIB_HEADER));
    if (inflator.err) {
      throw new Error(`inflate failed at offset ${offset}: ${inflator.msg || inflator.err}`);
    }
    if (!inflator.ended) {
      throw new Error(`inflate did not reach stream end at offset ${offset}`);
    }
    const data = inflator.result || new Uint8Array(0);
    const consumed = ZLIB_HEADER + inflator.strm.total_in + ADLER32;
    return { data, consumed };
  };
}

/**
 * Build a streaming `inflate(reader, offset)` for packs too large to hold whole.
 *
 * It reads the zlib member starting at `offset` from `reader` in `chunkSize`
 * windows and raw-inflates them, so memory is one window plus the inflated
 * result. Returns `{ data, consumed }` with the same `consumed` (whole zlib
 * member length) as `makePakoInflate`. `reader` is a `packReader` (`size` plus
 * async `read(offset, length)`).
 */
export function makePakoStreamInflate(pako, { chunkSize = 1 << 20 } = {}) {
  return async (reader, offset) => {
    const head = await reader.read(offset, Math.min(chunkSize, reader.size - offset));
    if (head.length < 2) {
      throw new Error(`truncated zlib stream at offset ${offset}`);
    }
    const cmf = head[0];
    const flg = head[1];
    if ((cmf & 0x0f) !== 0x08) {
      throw new Error(`not a zlib stream at offset ${offset}: cmf=0x${cmf.toString(16)}`);
    }
    if (flg & 0x20) {
      throw new Error(`unexpected preset dictionary in zlib stream at offset ${offset}`);
    }

    const inflator = new pako.Inflate({ windowBits: -15 });
    inflator.push(head.subarray(ZLIB_HEADER));
    let pos = offset + head.length;
    while (!inflator.ended && !inflator.err && pos < reader.size) {
      const chunk = await reader.read(pos, Math.min(chunkSize, reader.size - pos));
      if (chunk.length === 0) break;
      inflator.push(chunk);
      pos += chunk.length;
    }
    if (inflator.err) {
      throw new Error(`inflate failed at offset ${offset}: ${inflator.msg || inflator.err}`);
    }
    if (!inflator.ended) {
      throw new Error(`inflate did not reach stream end at offset ${offset}`);
    }
    const data = inflator.result || new Uint8Array(0);
    const consumed = ZLIB_HEADER + inflator.strm.total_in + ADLER32;
    return { data, consumed };
  };
}
