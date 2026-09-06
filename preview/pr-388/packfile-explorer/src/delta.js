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
 * Decode a delta into a base size, result size, instruction list, and byte
 * regions for hex visualization. Each instruction is
 * `{ type: "copy", offset, size, copyIndex, span }` or
 * `{ type: "insert", data, span }`. Regions mark header varints, opcodes,
 * offset/size fields, and literal insert bytes in the delta stream.
 */
export function parseDelta(delta) {
  let { size: baseSize, at } = readDeltaSize(delta, 0);
  const baseSizeStart = 0;
  const baseSizeEnd = at;
  const resultRead = readDeltaSize(delta, at);
  const resultSize = resultRead.size;
  const resultSizeStart = at;
  at = resultRead.at;
  const resultSizeEnd = at;

  const regions = [
    {
      start: baseSizeStart,
      end: baseSizeEnd,
      role: "header",
      field: "baseSize",
      value: baseSize,
      label: `base size ${baseSize}`,
    },
    {
      start: resultSizeStart,
      end: resultSizeEnd,
      role: "header",
      field: "resultSize",
      value: resultSize,
      label: `result size ${resultSize}`,
    },
  ];

  const ops = [];
  let copyIndex = 0;
  while (at < delta.length) {
    const opcodeAt = at;
    const opcode = delta[at];
    at += 1;
    if (opcode & 0x80) {
      // Copy from base: variable offset/size fields selected by the low bits.
      let offset = 0;
      let size = 0;
      const offsetStart = at;
      if (opcode & 0x01) offset |= delta[at++];
      if (opcode & 0x02) offset |= delta[at++] << 8;
      if (opcode & 0x04) offset |= delta[at++] << 16;
      if (opcode & 0x08) offset |= delta[at++] << 24;
      const offsetEnd = at;
      const sizeStart = at;
      if (opcode & 0x10) size |= delta[at++];
      if (opcode & 0x20) size |= delta[at++] << 8;
      if (opcode & 0x40) size |= delta[at++] << 16;
      const sizeEnd = at;
      if (size === 0) size = 0x10000;
      offset = offset >>> 0;

      regions.push({
        start: opcodeAt,
        end: opcodeAt + 1,
        role: "opcode",
        op: "copy",
        copyIndex,
        opcode,
        label: `copy opcode 0x${opcode.toString(16)}`,
      });
      if (offsetEnd > offsetStart) {
        regions.push({
          start: offsetStart,
          end: offsetEnd,
          role: "copy-offset",
          copyIndex,
          offset,
          label: `base offset ${offset}`,
        });
      }
      if (sizeEnd > sizeStart) {
        regions.push({
          start: sizeStart,
          end: sizeEnd,
          role: "copy-size",
          copyIndex,
          size,
          label: `copy size ${size}`,
        });
      } else {
        regions.push({
          start: opcodeAt,
          end: opcodeAt + 1,
          role: "copy-size",
          copyIndex,
          size,
          label: `copy size ${size} (implicit)`,
        });
      }

      ops.push({
        type: "copy",
        offset,
        size,
        copyIndex,
        span: { start: opcodeAt, end: at },
      });
      copyIndex += 1;
    } else if (opcode !== 0) {
      // Insert the next `opcode` literal bytes.
      const dataStart = at;
      const data = delta.subarray(at, at + opcode);
      at += opcode;
      regions.push({
        start: opcodeAt,
        end: opcodeAt + 1,
        role: "opcode",
        op: "insert",
        label: `insert opcode (${opcode} B)`,
      });
      regions.push({
        start: dataStart,
        end: at,
        role: "insert-data",
        label: `literal insert (${opcode} B)`,
      });
      ops.push({ type: "insert", data, span: { start: opcodeAt, end: at } });
    } else {
      throw new Error("invalid delta opcode 0x00");
    }
  }
  return { baseSize, resultSize, ops, regions };
}

/**
 * Map a resolved object's bytes back to copy/insert segments for coloring.
 * Copy segments reference the delta base oid and offset in that base object.
 */
export function buildResolvedSegments(deltaParsed, baseOid) {
  const segments = [];
  let outAt = 0;
  for (const op of deltaParsed.ops) {
    if (op.type === "copy") {
      segments.push({
        start: outAt,
        end: outAt + op.size,
        kind: "copy",
        copyIndex: op.copyIndex,
        baseOffset: op.offset,
        baseOid,
        size: op.size,
      });
      outAt += op.size;
    } else {
      segments.push({
        start: outAt,
        end: outAt + op.data.length,
        kind: "insert",
        size: op.data.length,
      });
      outAt += op.data.length;
    }
  }
  return segments;
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
