import test from "node:test";
import assert from "node:assert/strict";

import { describeHeader, readHeader } from "../src/rom.js";
import { makeRom } from "./rom-fixture.js";

test("readHeader reads mapper, sizes, and mirroring", () => {
  const rom = makeRom({ prgBanks: 2, chrBanks: 1, mapper: 4, vertical: true });
  const h = readHeader(rom);
  assert.deepEqual(h, {
    mapper: 4,
    prgKiB: 32,
    chrKiB: 8,
    mirroring: "vertical",
    battery: false,
  });
  assert.equal(describeHeader(h), "Mapper 4, 32 KiB PRG, 8 KiB CHR");
});

test("readHeader combines the mapper nibbles from flags 6 and 7", () => {
  assert.equal(readHeader(makeRom({ mapper: 66 })).mapper, 66);
});

test("readHeader ignores flags 7 when an old dumper left junk in the header", () => {
  const rom = makeRom({ mapper: 1 });
  rom[7] = 0x44;
  rom.set([0x44, 0x69, 0x73, 0x6b], 12);
  assert.equal(readHeader(rom).mapper, 1);
});

test("describeHeader names CHR RAM when there is no CHR ROM", () => {
  const h = readHeader(makeRom({ chrBanks: 0 }));
  assert.equal(describeHeader(h), "Mapper 0, 16 KiB PRG, CHR RAM");
});

test("readHeader rejects files that aren't iNES ROMs", () => {
  assert.throws(() => readHeader(new TextEncoder().encode("GIF89a........")), /Not an iNES ROM/);
  assert.throws(() => readHeader(makeRom().slice(0, 1000)), /truncated/);
  const empty = makeRom();
  empty[4] = 0;
  assert.throws(() => readHeader(empty), /no PRG banks/);
});
