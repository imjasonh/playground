import { OTA_0_OFFSET, OTA_1_OFFSET } from "../src/constants.js";
import { flashFirmware, toBinaryString } from "../src/flash.js";
import test from "node:test";
import assert from "node:assert/strict";

function fakeEspTool({ chip = "ESP32-D0WDQ6 (revision v1.0)" } = {}) {
  const calls = [];
  class Transport {
    constructor(port, tracing) {
      this.port = port;
      calls.push(["Transport", tracing]);
    }
    async setDTR(state) {
      calls.push(["DTR", state]);
    }
    async setRTS(state) {
      calls.push(["RTS", state]);
    }
    async disconnect() {
      calls.push("disconnect");
    }
  }
  class ESPLoader {
    constructor(opts) {
      this.opts = opts;
    }
    async main() {
      calls.push("main");
      return chip;
    }
    async writeFlash(flashOpts) {
      calls.push(["writeFlash", flashOpts]);
    }
  }
  return { Transport, ESPLoader, calls };
}

test("flashFirmware writes both slots, pulses EN into the app, and disconnects", async () => {
  const { Transport, ESPLoader, calls } = fakeEspTool();
  const firmware = new Uint8Array([0xe9, 0, 1]);
  const result = await flashFirmware({
    port: { id: "cu.usbserial" },
    firmware,
    ESPLoader,
    Transport,
  });
  assert.equal(result.chip.startsWith("ESP32"), true);
  assert.deepEqual(
    result.parts.map((p) => p.address),
    [OTA_0_OFFSET, OTA_1_OFFSET],
  );
  assert.equal(calls[0][0], "Transport");
  assert.equal(calls[0][1], undefined);
  assert.equal(calls[1], "main");
  assert.equal(calls[2][0], "writeFlash");
  assert.equal(calls[2][1].eraseAll, false);
  assert.equal(calls[2][1].flashSize, "4MB");
  assert.equal(typeof calls[2][1].fileArray[0].data, "string");
  assert.equal(calls[2][1].fileArray[0].data.charCodeAt(0), 0xe9);
  assert.deepEqual(calls.slice(3, 7), [
    ["DTR", false],
    ["RTS", true],
    ["RTS", false],
    ["DTR", false],
  ]);
  assert.equal(calls[7], "disconnect");
});

test("flashFirmware warns when the chip is not classic ESP32", async () => {
  const { Transport, ESPLoader } = fakeEspTool({ chip: "ESP32-S3" });
  const lines = [];
  await flashFirmware({
    port: {},
    firmware: new Uint8Array([0xe9]),
    ESPLoader,
    Transport,
    terminal: {
      clean() {},
      writeLine(line) {
        lines.push(line);
      },
      write() {},
    },
  });
  assert.match(lines.join("\n"), /classic ESP32/);
});

test("toBinaryString round-trips bytes including a chunk boundary", () => {
  const bytes = new Uint8Array(8200);
  bytes[0] = 0xe9;
  bytes[8199] = 0x7f;
  const s = toBinaryString(bytes);
  assert.equal(s.length, 8200);
  assert.equal(s.charCodeAt(0), 0xe9);
  assert.equal(s.charCodeAt(8199), 0x7f);
});
