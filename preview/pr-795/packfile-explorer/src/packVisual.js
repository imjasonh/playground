// Annotate raw packfile bytes for a single object entry (header, base pointer,
// zlib member). Used by the hex editor in the detail pane.

import { bytesToHex } from "./hex.js";
import { OBJ_OFS_DELTA, OBJ_REF_DELTA } from "./pack.js";

function readEntryHeader(bytes, start) {
  let at = start;
  let byte = bytes[at++];
  const type = (byte >> 4) & 0x07;
  let size = byte & 0x0f;
  let shift = 4;
  while (byte & 0x80) {
    byte = bytes[at++];
    size += (byte & 0x7f) * 2 ** shift;
    shift += 7;
  }
  return { type, size, at };
}

function readOffsetVarint(bytes, start) {
  let at = start;
  let byte = bytes[at++];
  let value = byte & 0x7f;
  while (byte & 0x80) {
    byte = bytes[at++];
    value = ((value + 1) * 128) + (byte & 0x7f);
  }
  return { value, at };
}

/**
 * Return byte regions covering one pack entry: object header, base oid or ofs
 * varint, and the zlib-compressed payload. `sliceBytes` holds the entry's own
 * bytes, starting at `entry.offset`, and the returned regions are
 * slice-relative (0-based) so they color the hex view directly.
 */
export function annotatePackEntrySlice(sliceBytes, entry) {
  const regions = [];
  let at = 0;
  const header = readEntryHeader(sliceBytes, at);
  at = header.at;
  regions.push({
    start: 0,
    end: at,
    role: "pack-header",
    label: `object header · ${entry.typeName} · inflated ${header.size} B`,
  });

  if (entry.type === OBJ_REF_DELTA) {
    const oidStart = at;
    at += 20;
    const baseOid = bytesToHex(sliceBytes.subarray(oidStart, at));
    regions.push({
      start: oidStart,
      end: at,
      role: "base-oid",
      baseOid,
      label: `base oid ${baseOid}`,
    });
  } else if (entry.type === OBJ_OFS_DELTA) {
    const ofsStart = at;
    const ofs = readOffsetVarint(sliceBytes, at);
    at = ofs.at;
    regions.push({
      start: ofsStart,
      end: at,
      role: "base-offset",
      baseOffset: entry.baseOffset,
      distance: ofs.value,
      label: `ofs-delta −${ofs.value} → pack@${entry.baseOffset}`,
    });
  }

  const zlibStart = entry.dataOffset - entry.offset;
  const zlibEnd = zlibStart + entry.compressedSize;
  regions.push({
    start: zlibStart,
    end: zlibEnd,
    role: "zlib",
    label: `zlib ${zlibEnd - zlibStart} B compressed`,
  });

  return { regions, bytes: sliceBytes.subarray(0, entry.packedSize) };
}
