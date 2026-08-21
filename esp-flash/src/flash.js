import {
  FLASH_FREQ,
  FLASH_MODE,
  FLASH_SIZE,
  ROM_BAUD,
} from "./constants.js";
import { flashParts, inspectImage, isClassicEsp32 } from "./image.js";

/**
 * Convert firmware bytes to the binary string esptool-js 0.5.x still flashes.
 *
 * Its TypeScript types say `Uint8Array`, but `writeFlash` runs the blob
 * through `bstrToUi8`, which calls `charCodeAt`.
 *
 * @param {Uint8Array} bytes
 */
export function toBinaryString(bytes) {
  const chunk = 8192;
  let out = "";
  for (let i = 0; i < bytes.length; i += chunk) {
    out += String.fromCharCode.apply(null, bytes.subarray(i, i + chunk));
  }
  return out;
}

/**
 * Flash `firmware` onto a SerialPort using esptool-js.
 *
 * `ESPLoader` and `Transport` are injected so unit tests do not load the
 * vendored bundle.
 *
 * @param {{
 *   port: SerialPort,
 *   firmware: Uint8Array,
 *   bothSlots?: boolean,
 *   baudrate?: number,
 *   terminal?: { clean: Function, writeLine: Function, write: Function },
 *   ESPLoader: new (opts: object) => {
 *     main: () => Promise<string>,
 *     writeFlash: (opts: object) => Promise<void>,
 *     after: (mode: string) => Promise<void>,
 *   },
 *   Transport: new (port: SerialPort, tracing?: boolean) => {
 *     disconnect: () => Promise<void>,
 *   },
 *   onProgress?: (fileIndex: number, written: number, total: number) => void,
 * }} opts
 */
export async function flashFirmware(opts) {
  const firmware = opts.firmware;
  inspectImage(firmware);
  const parts = flashParts(firmware, { bothSlots: opts.bothSlots }).map((part) => ({
    address: part.address,
    data: toBinaryString(part.data),
  }));
  const Transport = opts.Transport;
  const ESPLoader = opts.ESPLoader;
  if (typeof Transport !== "function" || typeof ESPLoader !== "function") {
    throw new Error("esptool-js Transport/ESPLoader are not loaded");
  }

  const transport = new Transport(opts.port, true);
  const loader = new ESPLoader({
    transport,
    baudrate: opts.baudrate || ROM_BAUD,
    terminal: opts.terminal,
  });

  try {
    const chip = await loader.main();
    if (!isClassicEsp32(chip)) {
      opts.terminal?.writeLine?.(
        `Warning: detected ${chip || "unknown chip"}; inkbot images are classic ESP32.`,
      );
    }
    await loader.writeFlash({
      fileArray: parts,
      flashMode: FLASH_MODE,
      flashFreq: FLASH_FREQ,
      flashSize: FLASH_SIZE,
      eraseAll: false,
      compress: true,
      reportProgress: opts.onProgress,
    });
    await loader.after("hard_reset");
    return { chip, parts };
  } finally {
    try {
      await transport.disconnect();
    } catch {
      // Port may already be gone after reset.
    }
  }
}
