// Git delta encoding: apply and describe.
//
// A delta object starts with two size varints (base size, result size) then a
// stream of copy and insert instructions. See
// https://git-scm.com/docs/pack-format#_deltified_representation.

/** Read a delta-size varint (7 bits per byte, little-endian). */
function readDeltaSize(bytes, start) {
  let size = 0;
  let shift = 0;
  let at = start;
  for (;;) {
    const byte = bytes[at];
    at += 1;
    size |= (byte & 0x7f) << shift;
    shift += 7;
    if ((byte & 0x80) === 0) break;
  }
  return { size: size >>> 0, at };
}

/**
 * Decode a delta into a base size, result size, and instruction list. Each
 * instruction is `{ type: "copy", offset, size }` or
 * `{ type: "insert", data: Uint8Array }`. Useful for both applying and
 * visualizing how a deltified object reuses its base.
 */
export function parseDelta(delta) {
  let { size: baseSize, at } = readDeltaSize(delta, 0);
  const resultRead = readDeltaSize(delta, at);
  const resultSize = resultRead.size;
  at = resultRead.at;

  const ops = [];
  while (at < delta.length) {
    const opcode = delta[at];
    at += 1;
    if (opcode & 0x80) {
      // Copy from base: variable offset/size fields selected by the low bits.
      let offset = 0;
      let size = 0;
      if (opcode & 0x01) offset |= delta[at++];
      if (opcode & 0x02) offset |= delta[at++] << 8;
      if (opcode & 0x04) offset |= delta[at++] << 16;
      if (opcode & 0x08) offset |= delta[at++] << 24;
      if (opcode & 0x10) size |= delta[at++];
      if (opcode & 0x20) size |= delta[at++] << 8;
      if (opcode & 0x40) size |= delta[at++] << 16;
      if (size === 0) size = 0x10000;
      ops.push({ type: "copy", offset: offset >>> 0, size });
    } else if (opcode !== 0) {
      // Insert the next `opcode` literal bytes.
      const data = delta.subarray(at, at + opcode);
      at += opcode;
      ops.push({ type: "insert", data });
    } else {
      throw new Error("invalid delta opcode 0x00");
    }
  }
  return { baseSize, resultSize, ops };
}

/** Apply a delta against its base object, returning the reconstructed bytes. */
export function applyDelta(base, delta) {
  const { baseSize, resultSize, ops } = parseDelta(delta);
  if (base.length !== baseSize) {
    throw new Error(`delta base size mismatch: expected ${baseSize}, got ${base.length}`);
  }
  const out = new Uint8Array(resultSize);
  let at = 0;
  for (const op of ops) {
    if (op.type === "copy") {
      out.set(base.subarray(op.offset, op.offset + op.size), at);
      at += op.size;
    } else {
      out.set(op.data, at);
      at += op.data.length;
    }
  }
  if (at !== resultSize) {
    throw new Error(`delta result size mismatch: wrote ${at}, expected ${resultSize}`);
  }
  return out;
}
