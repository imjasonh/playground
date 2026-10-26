-- Mesen2 .dbg validation probe.
--
-- Invocation (see `.github/workflows/ci.yml` for the full recipe):
--   DOTNET_SYSTEM_GLOBALIZATION_INVARIANT=1 xvfb-run -a \
--     ./Mesen --testRunner <rom.nes> probe.lua --timeout=15
--
-- Mesen auto-loads <rom>.dbg from the same directory as <rom.nes>
-- and runs this script inside its scripting engine. We exercise a
-- handful of .dbg features in order of increasing depth:
--
--   1. Each `sym` record resolves via `emu.getLabelAddress`.
--   2. Addresses land in sensible ranges that match the compiler's
--      linker output (Mesen applies `val - seg.start + ooffs - 16`
--      to produce PRG-relative byte offsets, so our `seg` record's
--      `ooffs` must include the iNES header or every address shifts
--      by 16 bytes — which was a real bug caught by this test).
--   3. The emulator actually runs: after three `startFrame` events
--      the CPU's PC must be inside the fixed bank's CPU window.
--   4. `emu.read()` returns the iNES header's magic bytes from
--      `nesPrgRom`, confirming the PRG region is mapped where our
--      linker said.
--
-- Mesen's `emu.log` writes to an internal buffer the testRunner
-- doesn't expose to stdout, so the only reliable signal back to CI
-- is the process exit code via `emu.stop(code)`. Each failure path
-- has a unique small-integer code so the CI log pinpoints which
-- assertion broke without needing extra output.
--
-- Exit codes:
--    0 = all checks passed
--   1-8 = individual `sym` record resolution failed (see `labels`)
--  10-13 = label address out of expected range
--  20-21 = label ordering wrong (linker emitted them in the wrong
--          order, which would break source-level stepping)
--     30 = `startFrame` callback never fired (emulator didn't run)
--     31 = CPU PC landed outside the fixed bank after 3 frames
--     40 = byte at `main_loop`'s PRG offset is not the expected
--          LDA-zp opcode that the NEScript runtime always emits
--          as the first instruction of the main loop. Fires if
--          Mesen's PRG mapping drifted (e.g., `seg.ooffs` wrong)
--          or the runtime's main-loop prologue changed (rebless
--          MAIN_LOOP_OPCODE below with the new first byte).

local function fail(code)
  emu.stop(code)
end

-- --- 1. Every user-facing label our render_dbg emits must resolve ---
--
-- We pair each label with the unique exit code that identifies it.
-- The addresses Mesen returns are PRG-relative byte offsets (see
-- file-level comment above).
--
-- `reset` is deliberately omitted from this list: Mesen2 reserves
-- the name for its own built-in labels and `getLabelAddress("reset")`
-- returns nil even when our .dbg defines it.
local labels = {
  { name = "nmi",        missing = 2 },
  { name = "irq",        missing = 3 },
  { name = "Main_frame", missing = 4 },
  { name = "main_loop",  missing = 5 },
}

local resolved = {}
for _, entry in ipairs(labels) do
  local info = emu.getLabelAddress(entry.name)
  if info == nil then fail(entry.missing) end
  resolved[entry.name] = info
end

-- --- 2. Addresses must fit in the fixed bank's PRG window ---
--
-- Fixed bank is 16 KB, always placed post-header, so PRG-relative
-- offsets fall in [0, 0x4000). Zero is suspicious (would mean the
-- label landed at the very first byte of the fixed bank, which
-- would only happen if it aliased `__reset` — we already skipped
-- that case above).
local function in_fixed_bank(info, code)
  if info.address < 0 or info.address >= 0x4000 then fail(code) end
  if info.address == 0 then fail(code) end
end

in_fixed_bank(resolved["nmi"],        10)
in_fixed_bank(resolved["irq"],        11)
in_fixed_bank(resolved["Main_frame"], 12)
in_fixed_bank(resolved["main_loop"],  13)

-- --- Relative layout: codegen emits main_loop before the user's
-- state handlers, and NMI/IRQ vectors sit past the user code near
-- the end of the fixed bank. Regressions in the linker's placement
-- algorithm would re-order these and break source-line mapping.
if resolved["main_loop"].address >= resolved["Main_frame"].address then fail(20) end
if resolved["Main_frame"].address >= resolved["nmi"].address then fail(21) end

-- --- 3. Emulation actually runs: PC should be inside the fixed
-- bank after the third `startFrame` event. Before the third frame
-- Mesen's rendering subsystem is still warming up (master-clock
-- alignment) and PC can briefly land in the reset vector's setup
-- sequence, which the compiler sometimes places at addresses
-- outside the user-visible labels. Three frames is enough to reach
-- the main loop's body on every example we've tried.
local frames_seen = 0
emu.addEventCallback(function()
  frames_seen = frames_seen + 1
  if frames_seen < 3 then return end

  local state = emu.getState()
  local pc = state["cpu.pc"]
  if pc == nil or pc < 0xC000 or pc >= 0x10000 then fail(31) end

  -- --- 4. Mesen's PRG mapping matches our label addresses ---
  -- NEScript's runtime always emits `LDA ZP_FRAME_FLAG` as the
  -- first instruction of the main loop — opcode 0xA5 in 6502.
  -- Read what Mesen thinks is the byte at `main_loop.address` in
  -- `nesPrgRom` and check against that constant. This catches
  -- any drift between the linker's label addresses and Mesen's
  -- view of the PRG memory map, including the `seg.ooffs` bug
  -- this probe was written to pin down: if `ooffs` is wrong by
  -- N bytes, every label shifts by N bytes and reads the wrong
  -- opcode. Checking both existence *and* exact value lets a
  -- non-$FF coincidence slip through the net.
  local MAIN_LOOP_OPCODE = 0xA5
  local byte = emu.read(resolved["main_loop"].address, emu.memType.nesPrgRom)
  if byte ~= MAIN_LOOP_OPCODE then fail(40) end

  emu.stop(0) -- all checks passed
end, emu.eventType.startFrame)

-- If `startFrame` never fires within the --timeout window, Mesen's
-- wait loop returns whatever `result` was last set to (initially
-- -1, which 8-bit-truncates to 255). Catch that specifically: our
-- script's path through the callback is the only one that ever
-- calls `emu.stop`, so reaching this point just yields to the
-- frame loop — any non-zero non-fail exit means the callback
-- mechanism itself is broken.
