import test from "node:test";
import assert from "node:assert/strict";

import {
  compileSongFrames,
  parseNsfHeader,
  songToNsf,
  NSF_LOAD_ADDRESS,
  NSF_NTSC_PLAY_US,
} from "../src/export/nsf.js";
import { nsfToInesRom, songToNesRom } from "../src/export/nesRom.js";
import { createDemoSong, createSong } from "../src/song.js";
import { overdubNote } from "../src/sequencer/pattern.js";

test("songToNsf writes a valid NSF header", () => {
  const nsf = songToNsf(createDemoSong(), { loops: 1 });
  const header = parseNsfHeader(nsf);
  assert.equal(header.version, 1);
  assert.equal(header.songs, 1);
  assert.equal(header.loadAddress, NSF_LOAD_ADDRESS);
  assert.equal(header.initAddress, NSF_LOAD_ADDRESS);
  assert.ok(header.playAddress > header.initAddress);
  assert.equal(header.ntscPlayUs, NSF_NTSC_PLAY_US);
  assert.deepEqual(header.bankswitch, [0, 0, 0, 0, 0, 0, 0, 0]);
  assert.equal(header.expansion, 0);
  assert.equal(header.title, "Boot Loop");
  assert.ok(header.data.length > 32);
});

test("compileSongFrames emits register activity for demo", () => {
  const { frames, durationSec } = compileSongFrames(createDemoSong(), {
    loops: 1,
  });
  assert.ok(frames.length > 30, `frames ${frames.length}`);
  assert.ok(durationSec > 0.5);
  const writes = frames.reduce((n, f) => n + f.length, 0);
  assert.ok(writes > 10, `writes ${writes}`);
  for (const frame of frames) {
    for (const w of frame) {
      assert.ok(w.addr >= 0x4000 && w.addr <= 0x4017);
      assert.ok(w.value >= 0 && w.value <= 255);
    }
  }
});

test("empty song still produces a playable NSF", () => {
  const nsf = songToNsf(createSong({ title: "Silence" }), { loops: 1 });
  const header = parseNsfHeader(nsf);
  assert.equal(header.title, "Silence");
  assert.ok(nsf.length > 128);
});

test("nsfToInesRom produces an iNES image", () => {
  const nsf = songToNsf(createDemoSong(), { loops: 1 });
  const rom = nsfToInesRom(nsf);
  assert.equal(String.fromCharCode(rom[0], rom[1], rom[2]), "NES");
  assert.equal(rom[3], 0x1a);
  assert.equal(rom[4], 2); // 32KB PRG
  assert.equal(rom[5], 1); // 8KB CHR
  assert.equal(rom.length, 16 + 32 * 1024 + 8 * 1024);
});

test("songToNesRom matches NSF-wrapped ROM program payload size class", () => {
  let song = createSong({ title: "Beep", bpm: 120, length: 8 });
  song.patterns[0] = overdubNote(song.patterns[0], "pulse1", 0, 60, {
    length: 2,
  });
  const rom = songToNesRom(song, { loops: 1 });
  assert.equal(rom[0], 0x4e);
  assert.ok(rom.length > 16);
});
