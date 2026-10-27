// Plays Rampart matches in jsnes, a human (scripted, random) against
// the CPU, and reports what an accurate emulator or real NES would
// draw differently from jsnes:
//
//   - PPU register writes ($2005-$2007, $2003/$2004, $4014) while the
//     PPU is rendering, which corrupt the scroll and VRAM on hardware.
//   - $2001 writes in the middle of the visible frame, which start or
//     stop rendering partway down the screen.
//   - NMI handlers that run past vblank, and frame handlers that are
//     still running when the next NMI arrives (dropped frames).
//   - Battle frames where every sprite vanishes for a frame.
//   - More than 8 sprites on one scanline, which hardware drops.
//   - Board cells or attributes that change during a match.
//
// Usage: node rampart_probe.mjs [games] [outdir]

import { execFileSync } from "node:child_process";
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";

const require = createRequire(import.meta.url);
const loaded = require("jsnes");
const jsnes = loaded.NES ? loaded : globalThis.jsnes;
const { PNG } = require("pngjs");

const GAMES = Number(process.argv[2] || 20);
const OUT = process.argv[3] || "/tmp/rampart-probe";
mkdirSync(OUT, { recursive: true });

// Builds the ROM with a symbol file so the RAM addresses below track
// the source. Set NESCRIPT to use a compiler other than the release
// build.
const ROOT = fileURLToPath(new URL("../..", import.meta.url));
const NESCRIPT = process.env.NESCRIPT || `${ROOT}/target/release/nescript`;
const SYMS = `${OUT}/rampart.mlb`;
execFileSync(NESCRIPT, [
  "build",
  `${ROOT}/examples/rampart.ne`,
  "-o",
  `${OUT}/rampart.nes`,
  "--symbols",
  SYMS,
]);
const ROM = readFileSync(`${OUT}/rampart.nes`);
const sym = {};
for (const line of readFileSync(SYMS, "utf8").split("\n")) {
  const [kind, addr, name] = line.split(":");
  if (name) sym[`${kind}:${name}`] = parseInt(addr, 16);
}
function ram(name) {
  const a = sym[`R:${name}`];
  if (a === undefined) throw new Error(`no RAM symbol ${name} in ${SYMS}`);
  return a;
}
const A = {
  state: 0x03,
  mode: ram("mode"),
  cpuLevel: ram("cpu_level"),
  custWho: ram("cust_who"),
  custCursor: ram("cust_cursor"),
  turn: ram("turn"),
  unblank: ram("unblank"),
  phase: ram("phase"),
  onCard: ram("on_card"),
  actor: ram("actor"),
  crits: ram("crits"),
  lkReady: ram("lk_ready"),
};
// The fixed bank is the last 16 KB of PRG, mapped at $C000 under
// UxROM. The wait loop sits within a few bytes of main_loop.
const prgSize = ROM[4] * 0x4000;
const mainLoop = sym["P:main_loop"] - (prgSize - 0x4000) + 0xc000;
const WAIT_LOOP = [mainLoop, mainLoop + 16];
const ST_TITLE = 0;
const ST_BATTLE = 1;
const ST_CUSTOM = 2;
const P_WAIT = 0;
const P_LOCK = 2;
const P_MOVE = 7;
const P_AIM = 9;
const P_OVER = 11;

const B = {
  A: 0,
  B: 1,
  START: 3,
  UP: 4,
  DOWN: 5,
  LEFT: 6,
  RIGHT: 7,
};
const DIRS = [B.UP, B.DOWN, B.LEFT, B.RIGHT];
const LOCK_KEYS = [B.UP, B.DOWN, B.LEFT, B.RIGHT, B.A, B.B];

let seed = 12345;
function rnd(n) {
  seed = (Math.imul(seed, 1103515245) + 12345) >>> 0;
  return (seed >>> 8) % n;
}

const pixels = new Uint32Array(256 * 240);
const nes = new jsnes.NES({
  onFrame(fb) {
    for (let i = 0; i < fb.length; i++) pixels[i] = 0xff000000 | fb[i];
  },
  onAudioSample() {},
  sampleRate: 44100,
});
nes.loadROM(ROM);
const ppu = nes.ppu;
const cpu = nes.cpu;
const peek = (a) => cpu.mem[a & 0x7ff];
const vram = (a) => ppu.vramMem[ppu.vramMirrorTable[a & 0x3fff]];

// ── PPU write log ──────────────────────────────────────────
let frameNo = 0;
let frameWrites = [];
// The VRAM ring's head and tail at the end of each recent frame.
const RING_HEAD = 0x7e5;
const RING_TAIL = 0x7ec;
const ringLog = [];
const origWrite = nes.mmap.write.bind(nes.mmap);
nes.mmap.write = (addr, val) => {
  let reg = -1;
  if (addr >= 0x2000 && addr < 0x4000) reg = 0x2000 + (addr & 7);
  else if (addr === 0x4014) reg = 0x4014;
  if (reg >= 0) {
    frameWrites.push({
      reg,
      val,
      sl: ppu.scanline,
      x: ppu.curX,
      on: ppu.f_bgVisibility === 1 || ppu.f_spVisibility === 1,
    });
  }
  origWrite(addr, val);
};

// ── Findings ───────────────────────────────────────────────
const findings = new Map();
function note(kind, detail, shot) {
  let f = findings.get(kind);
  if (!f) {
    f = { kind, count: 0, examples: [], shots: 0, by: {} };
    findings.set(kind, f);
  }
  f.count++;
  const key = `state${detail.state} phase${detail.phase}${detail.onCard ? " card" : ""}`;
  f.by[key] = (f.by[key] || 0) + 1;
  if (f.examples.length < 8) f.examples.push(detail);
  if (shot && f.shots < 4) {
    f.shots++;
    save(`${kind}-${f.shots}`);
  }
}

function save(name) {
  const png = new PNG({ width: 256, height: 240 });
  const buf = Buffer.from(pixels.buffer.slice(0));
  png.data = buf;
  writeFileSync(`${OUT}/${name}.png`, PNG.sync.write(png));
}

function ctx() {
  return {
    game: gameNo,
    frame: frameNo,
    state: peek(A.state),
    phase: peek(A.phase),
    turn: peek(A.turn),
    onCard: peek(A.onCard),
  };
}

// Visible scanlines are 21..260 in jsnes numbering; 20 is pre-render.
const nmiTiming = [];
function checkWrites() {
  let lastVblankSl = -1;
  // Cycles from the start of vblank: the DMA write marks the end of
  // the audio tick, and the drain's last $2005 write marks its end.
  const cyc = (w) => Math.round((w.sl * 341 + w.x) / 3);
  const dma = frameWrites.find((w) => w.reg === 0x4014 && (w.sl <= 25));
  let end = null;
  let drained = 0;
  for (const w of frameWrites) {
    if (w.sl > 40) break;
    if (w.reg === 0x2005) end = w;
    if (w.reg === 0x2007) drained++;
  }
  if (dma && end && frameNo > 10) {
    nmiTiming.push({ dma: cyc(dma), end: cyc(end), bytes: drained, on: end.on });
  }
  for (const w of frameWrites) {
    const rendering = w.on && w.sl >= 20 && w.sl <= 260;
    if (
      rendering &&
      (w.reg === 0x2005 ||
        w.reg === 0x2006 ||
        w.reg === 0x2007 ||
        w.reg === 0x2003 ||
        w.reg === 0x2004 ||
        w.reg === 0x4014)
    ) {
      note(
        `write-during-render-${w.reg.toString(16)}`,
        { ...ctx(), line: w.sl - 21, dot: w.x, val: w.val },
        true,
      );
    }
    if (w.reg === 0x2001 && w.sl >= 21 && w.sl <= 260) {
      note(
        `2001-mid-frame-${w.val ? "on" : "off"}`,
        { ...ctx(), line: w.sl - 21, val: w.val.toString(16) },
        true,
      );
    }
    if (w.reg === 0x2000 && w.on && w.sl >= 20 && w.sl <= 260) {
      note("2000-during-render", { ...ctx(), line: w.sl - 21, val: w.val }, true);
    }
    if (w.sl <= 19 && (w.reg === 0x2007 || w.reg === 0x2005 || w.reg === 0x2006)) {
      lastVblankSl = Math.max(lastVblankSl, w.sl);
    }
  }
  if (lastVblankSl >= 0) {
    nmiLines.push(lastVblankSl);
  }
}

// Sprites per scanline from the OAM the PPU just rendered, and frames
// where every sprite vanished from a battle board that had them.
let lastVisible = 0;
function checkSprites() {
  if (frameNo < 10) return;
  const counts = new Uint8Array(240);
  let visible = 0;
  for (let i = 0; i < 64; i++) {
    if (ppu.spriteMem[i * 4] < 0xef) visible++;
  }
  const board =
    peek(A.state) === ST_BATTLE &&
    !peek(A.onCard) &&
    peek(A.unblank) === 0 &&
    ppu.f_spVisibility === 1;
  if (board && visible === 0 && lastVisible > 0) {
    note("sprites-vanished", ctx(), true);
  }
  lastVisible = board ? visible : 0;
  for (let i = 0; i < 64; i++) {
    const y = ppu.spriteMem[i * 4];
    if (y >= 0xef) continue;
    for (let r = 1; r <= 8; r++) {
      const line = y + r;
      if (line < 240) counts[line]++;
    }
  }
  let worst = 0;
  let at = -1;
  for (let l = 0; l < 240; l++) {
    if (counts[l] > worst) {
      worst = counts[l];
      at = l;
    }
  }
  if (worst > 8) {
    note("sprites-over-8-per-line", { ...ctx(), line: at, count: worst }, true);
  }
}

// True when the CPU sits in a wait_frame poll (`LDA $00` / `BEQ -4`).
// jsnes keeps REG_PC one byte behind the next instruction.
function inFramePoll() {
  const next = cpu.REG_PC + 1;
  const poll = (a) =>
    nes.mmap.load(a) === 0xa5 &&
    nes.mmap.load(a + 1) === 0x00 &&
    nes.mmap.load(a + 2) === 0xf0 &&
    nes.mmap.load(a + 3) === 0xfc;
  return poll(next) || poll(next - 2);
}

// The frame handler should be back in the wait loop when NMI fires.
// A handler that never gets back there for HANG_FRAMES is a hang. A
// wait_frame inside a handler, as set_mask does, is not an overrun.
const HANG_FRAMES = 300;
let overrunRun = 0;
let midHandlerWait = false;
const overrunPcs = {};
function checkOverrun() {
  midHandlerWait = false;
  if (frameNo < 10) return false;
  const pc = cpu.REG_PC;
  if (pc >= WAIT_LOOP[0] && pc <= WAIT_LOOP[1]) {
    overrunRun = 0;
    return false;
  }
  if (inFramePoll()) {
    midHandlerWait = true;
    overrunRun = 0;
    return false;
  }
  const shown = ppu.f_bgVisibility === 1 || ppu.f_spVisibility === 1;
  if (shown) overrunPcs[pc.toString(16)] = (overrunPcs[pc.toString(16)] || 0) + 1;
  note(`frame-overrun-${shown ? "shown" : "blanked"}`, { ...ctx(), pc: pc.toString(16) }, false);
  overrunRun++;
  return overrunRun >= HANG_FRAMES;
}

// With PROBE_TRACE set, keep the last few thousand PCs so a hang
// report shows how the program got where it is.
const TRACE = process.env.PROBE_TRACE ? new Uint16Array(4096) : null;
let traceAt = 0;
if (TRACE) {
  const emulate = cpu.emulate.bind(cpu);
  cpu.emulate = () => {
    TRACE[traceAt++ & 4095] = cpu.REG_PC + 1;
    return emulate();
  };
}

function reportHang() {
  const dir = `${OUT}/hang-game${String(gameNo).padStart(2, "0")}`;
  mkdirSync(dir, { recursive: true });
  save(`hang-game${String(gameNo).padStart(2, "0")}/screen`);
  writeFileSync(`${dir}/ram.bin`, Buffer.from(cpu.mem.slice(0, 0x800)));
  writeFileSync(`${dir}/ring.json`, JSON.stringify(ringLog, null, 1));
  if (TRACE) {
    const pcs = [];
    for (let i = 0; i < 4096; i++) pcs.push(TRACE[(traceAt + i) & 4095].toString(16));
    writeFileSync(`${dir}/trace.txt`, pcs.join("\n"));
  }
  note("hang", { ...ctx(), sp: cpu.REG_SP.toString(16), pc: cpu.REG_PC.toString(16) }, false);
}

// Board cells never change during a match. Card attributes never
// change while one Lock screen is up, but a CPU opponent lets the
// card repaint its gray-out pattern each time a new Lock screen
// opens, since plan legality tracks each mech's current damage.
let boardRef = null;
let cardRef = null;
let wasOnCard = false;
function snapshot(rows, cols) {
  const out = [];
  for (const r of rows) for (const c of cols) out.push(vram(0x2000 + r * 32 + c));
  for (let i = 0; i < 64; i++) out.push(vram(0x23c0 + i));
  return out;
}
const BOARD_ROWS = Array.from({ length: 24 }, (_, i) => 2 + i);
const BOARD_COLS = Array.from({ length: 24 }, (_, i) => 1 + i);
// Skips frames that end inside a swap's wait, while the old screen is
// still showing, and frames with rendering off.
function checkBoard() {
  if (peek(A.state) !== ST_BATTLE || peek(A.unblank) !== 0) return;
  if (midHandlerWait || ppu.f_bgVisibility !== 1) return;
  if (peek(A.onCard)) {
    const snap = snapshot([], []);
    if (!cardRef || !wasOnCard) cardRef = snap;
    else if (snap.some((v, i) => v !== cardRef[i])) {
      note("card-attr-changed", ctx(), true);
      cardRef = snap;
    }
    wasOnCard = true;
    return;
  }
  wasOnCard = false;
  const snap = snapshot(BOARD_ROWS, BOARD_COLS);
  if (!boardRef) {
    boardRef = snap;
    return;
  }
  const diffs = [];
  for (let i = 0; i < snap.length; i++) {
    if (snap[i] !== boardRef[i]) {
      if (i < 24 * 24) {
        diffs.push(`r${BOARD_ROWS[Math.floor(i / 24)]}c${BOARD_COLS[i % 24]}=${snap[i]}`);
      } else {
        diffs.push(`attr${i - 576}=${snap[i]}`);
      }
    }
  }
  if (diffs.length) {
    note("board-changed", { ...ctx(), diffs: diffs.slice(0, 6) }, true);
  }
}

// ── Input script ───────────────────────────────────────────
const queue = [];
function press(button, hold = 2, gap = 3) {
  queue.push({ button, hold, gap });
}
let cur = null;
function pumpInput() {
  if (!cur && queue.length) {
    cur = { ...queue.shift(), t: 0 };
    nes.buttonDown(1, cur.button);
  }
  if (!cur) return;
  cur.t++;
  if (cur.t === cur.hold) nes.buttonUp(1, cur.button);
  if (cur.t >= cur.hold + cur.gap) cur = null;
}

let gameNo = 0;
let lastState = -1;
let lastPhase = -1;
let phaseFrames = 0;
let gameFrames = 0;
const nmiLines = [];
const games = [];

function planTitle() {
  // sel starts on START (row 4). Up three times reaches CPU level.
  press(B.UP);
  press(B.UP);
  press(B.UP);
  for (let i = rnd(3); i > 0; i--) press(B.RIGHT);
  press(B.DOWN);
  if (rnd(2)) press(B.RIGHT);
  press(B.DOWN);
  if (rnd(2)) press(B.RIGHT);
  press(B.START);
}

function planCustom() {
  for (let i = rnd(4); i > 0; i--) press(B.B);
  for (let i = rnd(4); i > 0; i--) press(DIRS[rnd(4)]);
  // Down from the name row walks to the gun, arm, and START rows.
  for (let i = 0; i < 6; i++) press(B.DOWN);
  press(B.UP);
  press(B.UP);
  for (let i = rnd(5); i > 0; i--) press(B.RIGHT);
  press(B.DOWN);
  for (let i = rnd(5); i > 0; i--) press(B.RIGHT);
  press(B.START);
}

function drive() {
  const st = peek(A.state);
  const ph = peek(A.phase);
  if (st !== lastState || ph !== lastPhase) {
    phaseFrames = 0;
  } else {
    phaseFrames++;
  }
  const entered = st !== lastState || ph !== lastPhase;
  lastState = st;
  lastPhase = ph;
  if (queue.length || cur) return;

  if (st === ST_TITLE) {
    if (phaseFrames === 30) planTitle();
    return;
  }
  if (st === ST_CUSTOM) {
    if (phaseFrames === 60) planCustom();
    if (phaseFrames > 600 && phaseFrames % 120 === 0) press(B.START);
    return;
  }
  if (ph === P_LOCK && peek(A.lkReady) === 0) {
    if (phaseFrames % 20 === 10) {
      press(LOCK_KEYS[rnd(6)]);
      press(LOCK_KEYS[rnd(6)]);
      press(B.START);
    }
    return;
  }
  if (ph === P_MOVE && peek(A.actor) === 0) {
    if (phaseFrames % 40 === 20) {
      for (let i = rnd(4); i > 0; i--) press(DIRS[rnd(4)]);
      if (phaseFrames > 200) press(B.B);
      press(B.A);
    }
    return;
  }
  if (ph === P_AIM && peek(A.actor) === 0) {
    if (phaseFrames % 40 === 20) {
      for (let i = rnd(5); i > 0; i--) press(DIRS[rnd(4)]);
      press(B.A);
    }
    return;
  }
  if (ph === P_WAIT && entered && rnd(3) === 0) {
    press(B.A, 2, 2);
    return;
  }
  if (ph === P_OVER && phaseFrames === 90) {
    press(B.START);
  }
}

// ── Run ────────────────────────────────────────────────────
const SAMPLE_EVERY = 97;
let inBattle = false;
const MAX_FRAMES = 60 * 60 * 60 * 3;
while (gameNo < GAMES && frameNo < MAX_FRAMES) {
  pumpInput();
  frameWrites = [];
  nes.frame();
  frameNo++;
  ringLog.push({
    ...ctx(),
    head: peek(RING_HEAD),
    tail: peek(RING_TAIL),
    pending: (peek(RING_HEAD) - peek(RING_TAIL)) & 0xff,
    drained: frameWrites.filter((w) => w.reg === 0x2007 && w.sl <= 40).length,
    ring: Buffer.from(cpu.mem.slice(0x400, 0x500)).toString("hex"),
    q: [peek(0x20), peek(0x21), Buffer.from(cpu.mem.slice(0x532, 0x632)).toString("hex")],
    regs: frameWrites
      .filter((w) => w.reg !== 0x2007)
      .map((w) => `${w.reg.toString(16)}=${w.val.toString(16)}@${w.sl}`)
      .join(" "),
  });
  if (ringLog.length > HANG_FRAMES + 40) ringLog.shift();
  checkWrites();
  checkSprites();
  if (checkOverrun()) {
    reportHang();
    games.push({ game: gameNo, frames: gameFrames, turn: peek(A.turn), hung: true });
    nes.loadROM(ROM);
    queue.length = 0;
    cur = null;
    overrunRun = 0;
    inBattle = false;
    gameNo++;
    continue;
  }
  checkBoard();
  drive();

  const st = peek(A.state);
  if (st === ST_BATTLE && !inBattle) {
    inBattle = true;
    gameFrames = 0;
    boardRef = null;
    cardRef = null;
    wasOnCard = false;
  }
  if (inBattle) {
    gameFrames++;
    if (gameFrames % SAMPLE_EVERY === 0) {
      const dir = `${OUT}/game${String(gameNo).padStart(2, "0")}`;
      mkdirSync(dir, { recursive: true });
      const png = new PNG({ width: 256, height: 240 });
      png.data = Buffer.from(pixels.buffer.slice(0));
      writeFileSync(`${dir}/f${String(gameFrames).padStart(6, "0")}.png`, PNG.sync.write(png));
    }
  }
  if (inBattle && st === ST_BATTLE && peek(A.phase) === P_OVER && phaseFrames === 60) {
    save(`end-game${String(gameNo).padStart(2, "0")}`);
  }
  if (inBattle && st === ST_TITLE) {
    games.push({
      game: gameNo,
      frames: gameFrames,
      turn: peek(A.turn),
      crits: [peek(A.crits), peek(A.crits + 1)],
      level: peek(A.cpuLevel),
    });
    inBattle = false;
    gameNo++;
  }
}

const hist = {};
for (const l of nmiLines) hist[l] = (hist[l] || 0) + 1;
function pct(arr, p) {
  const s = [...arr].sort((a, b) => a - b);
  return s[Math.min(s.length - 1, Math.floor((s.length * p) / 100))];
}
const nmi = {
  samples: nmiTiming.length,
  dmaAt: { p50: pct(nmiTiming.map((t) => t.dma), 50), max: pct(nmiTiming.map((t) => t.dma), 100) },
  drainEnd: {
    p50: pct(nmiTiming.map((t) => t.end), 50),
    p99: pct(nmiTiming.map((t) => t.end), 99),
    max: pct(nmiTiming.map((t) => t.end), 100),
  },
  maxBytes: pct(nmiTiming.map((t) => t.bytes), 100),
  overVblank: nmiTiming.filter((t) => t.end > 2273).length,
  overVblankShown: nmiTiming.filter((t) => t.end > 2273 && t.on).length,
};
const report = {
  frames: frameNo,
  games,
  nmi,
  nmiLastVblankWriteLine: hist,
  overrunPcs,
  findings: [...findings.values()].map(({ kind, count, by, examples }) => ({ kind, count, by, examples })),
};
writeFileSync(`${OUT}/report.json`, JSON.stringify(report, null, 2));
console.log(JSON.stringify(report, null, 2));
