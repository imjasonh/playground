function sleep(ms) {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

/**
 * Pulse EN with IO0 held high so the chip leaves the ROM bootloader and
 * runs the app.
 *
 * esptool-js `HardReset` only deasserts RTS. After `ClassicReset` used to
 * enter download mode, RTS is already false, so that call is a no-op and
 * the stub keeps running. Sequence matches Python esptool `hard_reset` on
 * CH340 / CH9102 adapters: DTR false (IO0 high), RTS true (EN low), wait,
 * RTS false (EN high).
 *
 * @param {{
 *   setDTR: (state: boolean) => Promise<void>,
 *   setRTS: (state: boolean) => Promise<void>,
 * }} transport
 */
export async function resetIntoApp(transport) {
  if (
    !transport ||
    typeof transport.setDTR !== "function" ||
    typeof transport.setRTS !== "function"
  ) {
    throw new Error("serial transport cannot toggle DTR/RTS");
  }
  await transport.setDTR(false);
  await transport.setRTS(true);
  await sleep(100);
  await transport.setRTS(false);
  await sleep(50);
  await transport.setDTR(false);
}
