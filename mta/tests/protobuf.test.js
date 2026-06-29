import { Reader, Writer, eachField, WIRE } from '../src/protobuf.js';

describe('protobuf reader/writer', () => {
  test('varint round-trips across sizes (incl. > 32 bits)', () => {
    const values = [0, 1, 127, 128, 255, 300, 16384, 1700000000, 2 ** 40, 2 ** 46];
    for (const value of values) {
      const bytes = new Writer().writeVarint(value).finish();
      expect(new Reader(bytes).readVarint()).toBe(value);
    }
  });

  test('writeVarint rejects negatives', () => {
    expect(() => new Writer().writeVarint(-1)).toThrow();
  });

  test('string field encodes tag + UTF-8 and reads back', () => {
    const text = 'Times Sq – 42 St ☺';
    const reader = new Reader(new Writer().string(1, text).finish());
    const { field, wireType } = reader.readTag();
    expect(field).toBe(1);
    expect(wireType).toBe(WIRE.LEN);
    expect(reader.readString()).toBe(text);
  });

  test('float field round-trips (approximately)', () => {
    const reader = new Reader(new Writer().float(2, 40.7128).finish());
    const { field, wireType } = reader.readTag();
    expect(field).toBe(2);
    expect(wireType).toBe(WIRE.FIXED32);
    expect(reader.readFloat()).toBeCloseTo(40.7128, 3);
  });

  test('nested messages decode via eachField', () => {
    const sub = new Writer().varint(1, 5).string(2, 'hi');
    const bytes = new Writer().message(3, sub).finish();

    let inner = null;
    eachField(bytes, (field, reader) => {
      if (field !== 3) return;
      inner = {};
      eachField(reader.readMessage(), (f, r) => {
        if (f === 1) inner.a = r.readVarint();
        else if (f === 2) inner.b = r.readString();
      });
    });
    expect(inner).toEqual({ a: 5, b: 'hi' });
  });

  test('eachField skips fields the visitor ignores (all wire types)', () => {
    const bytes = new Writer().varint(1, 9).string(2, 'x').float(3, 1.5).finish();
    const seen = [];
    eachField(bytes, (field, reader) => {
      if (field === 2) seen.push(reader.readString());
    });
    expect(seen).toEqual(['x']);
  });

  test('reading past the end of a truncated length field throws', () => {
    const bytes = Uint8Array.from([0x0a, 0xff, 0xff, 0xff, 0x0f]); // field1 LEN, huge length
    expect(() => eachField(bytes, (field, reader) => {
      if (field === 1) reader.readMessage();
    })).toThrow(RangeError);
  });
});
