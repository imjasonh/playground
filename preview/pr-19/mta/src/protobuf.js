/**
 * A minimal Protocol Buffers reader/writer — just enough of the wire format to
 * decode (and, for sample data + tests, encode) GTFS-realtime feeds.
 *
 * GTFS-realtime is plain proto2 with no exotic features, so we only implement
 * the four wire types that actually appear: varint (0), 64-bit (1),
 * length-delimited (2), and 32-bit (5). There is deliberately no schema/codegen
 * here — `gtfsRealtime.js` walks fields by number — which keeps the app free of
 * a heavyweight protobuf dependency and makes every layer unit-testable.
 *
 * Varints are read/written as JS numbers, which are exact for integers up to
 * 2**53. Feed timestamps are POSIX seconds (~1.7e9), comfortably inside that
 * range, so we never need BigInt here.
 */

export const WIRE = {
  VARINT: 0,
  FIXED64: 1,
  LEN: 2,
  FIXED32: 5,
};

const textEncoder = new TextEncoder();
const textDecoder = new TextDecoder('utf-8');

/** Streaming reader over a byte buffer. */
export class Reader {
  /** @param {Uint8Array} bytes */
  constructor(bytes) {
    this.buf = bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes);
    this.pos = 0;
    this.len = this.buf.length;
    this.view = new DataView(this.buf.buffer, this.buf.byteOffset, this.buf.byteLength);
  }

  eof() {
    return this.pos >= this.len;
  }

  /** Read a base-128 varint as an unsigned JS number (exact to 2**53). */
  readVarint() {
    let result = 0;
    let factor = 1;
    let byte;
    do {
      if (this.pos >= this.len) throw new RangeError('varint truncated');
      byte = this.buf[this.pos++];
      result += (byte & 0x7f) * factor;
      factor *= 128;
    } while (byte & 0x80);
    return result;
  }

  /** Read a field tag, returning its field number and wire type. */
  readTag() {
    const tag = this.readVarint();
    return { field: Math.floor(tag / 8), wireType: tag & 0x7 };
  }

  /** Read a length-delimited chunk as a subarray (no copy). */
  readBytes() {
    const length = this.readVarint();
    const start = this.pos;
    const end = start + length;
    if (end > this.len) throw new RangeError('length-delimited field truncated');
    this.pos = end;
    return this.buf.subarray(start, end);
  }

  /** Read a length-delimited chunk decoded as a UTF-8 string. */
  readString() {
    return textDecoder.decode(this.readBytes());
  }

  /** Read a length-delimited chunk wrapped in a fresh sub-reader. */
  readMessage() {
    return new Reader(this.readBytes());
  }

  readFixed32() {
    const value = this.view.getUint32(this.pos, true);
    this.pos += 4;
    return value;
  }

  readFloat() {
    const value = this.view.getFloat32(this.pos, true);
    this.pos += 4;
    return value;
  }

  readDouble() {
    const value = this.view.getFloat64(this.pos, true);
    this.pos += 8;
    return value;
  }

  /** Advance past a field whose value we don't care about. */
  skip(wireType) {
    switch (wireType) {
      case WIRE.VARINT:
        this.readVarint();
        break;
      case WIRE.FIXED64:
        this.pos += 8;
        break;
      case WIRE.LEN:
        this.pos += this.readVarint();
        break;
      case WIRE.FIXED32:
        this.pos += 4;
        break;
      default:
        throw new RangeError(`unsupported wire type ${wireType}`);
    }
    if (this.pos > this.len) throw new RangeError('skipped past end of buffer');
  }
}

/**
 * Walk every field in `bytes`, invoking `visit(field, reader, wireType)`. The
 * callback must consume exactly one value from `reader` (e.g. `readVarint`,
 * `readString`, `readMessage`); if it consumes nothing, the field is skipped.
 *
 * @param {Uint8Array|Reader} bytes
 * @param {(field: number, reader: Reader, wireType: number) => void} visit
 */
export function eachField(bytes, visit) {
  const reader = bytes instanceof Reader ? bytes : new Reader(bytes);
  while (!reader.eof()) {
    const { field, wireType } = reader.readTag();
    const before = reader.pos;
    visit(field, reader, wireType);
    if (reader.pos === before) reader.skip(wireType);
  }
}

/** Accumulating writer; call {@link Writer#finish} for the encoded bytes. */
export class Writer {
  constructor() {
    /** @type {number[]} */
    this.bytes = [];
  }

  writeVarint(value) {
    let v = Math.floor(value);
    if (v < 0) throw new RangeError('writeVarint expects a non-negative integer');
    while (v > 0x7f) {
      this.bytes.push((v & 0x7f) | 0x80);
      v = Math.floor(v / 128);
    }
    this.bytes.push(v & 0x7f);
    return this;
  }

  tag(field, wireType) {
    return this.writeVarint(field * 8 + wireType);
  }

  varint(field, value) {
    if (value === undefined || value === null) return this;
    return this.tag(field, WIRE.VARINT).writeVarint(value);
  }

  string(field, value) {
    if (value === undefined || value === null) return this;
    return this.bytesField(field, textEncoder.encode(String(value)));
  }

  bytesField(field, data) {
    if (data === undefined || data === null) return this;
    const arr = data instanceof Uint8Array ? data : Uint8Array.from(data);
    this.tag(field, WIRE.LEN).writeVarint(arr.length);
    for (let i = 0; i < arr.length; i += 1) this.bytes.push(arr[i]);
    return this;
  }

  /** Write a sub-message field from either a Writer or raw bytes. */
  message(field, sub) {
    if (sub === undefined || sub === null) return this;
    const data = sub instanceof Writer ? sub.finish() : sub;
    return this.bytesField(field, data);
  }

  float(field, value) {
    if (value === undefined || value === null) return this;
    const buf = new Uint8Array(4);
    new DataView(buf.buffer).setFloat32(0, value, true);
    this.tag(field, WIRE.FIXED32);
    for (let i = 0; i < 4; i += 1) this.bytes.push(buf[i]);
    return this;
  }

  finish() {
    return Uint8Array.from(this.bytes);
  }
}
