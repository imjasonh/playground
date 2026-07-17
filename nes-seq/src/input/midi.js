/**
 * Web MIDI input wrapper. Gracefully no-ops when the API is unavailable
 * (Safari) or the user denies permission.
 */

/**
 * @typedef {object} MidiHandlers
 * @property {(midi: number, velocity: number) => void} onNoteOn
 * @property {(midi: number) => void} onNoteOff
 * @property {(info: { supported: boolean, connected: boolean, name: string|null, error?: string }) => void} [onStatus]
 */

/**
 * @param {MidiHandlers} handlers
 * @returns {{ start: () => Promise<void>, stop: () => void }}
 */
export function createMidiInput(handlers) {
  /** @type {MIDIAccess|null} */
  let access = null;
  /** @type {Map<number, number>} note → count (for overlapping devices) */
  const active = new Map();

  function emitStatus(partial) {
    handlers.onStatus?.({
      supported: Boolean(navigator.requestMIDIAccess),
      connected: false,
      name: null,
      ...partial,
    });
  }

  /**
   * @param {MIDIMessageEvent} event
   */
  function onMessage(event) {
    const data = event.data;
    if (!data || data.length < 1) return;
    const status = data[0] & 0xf0;
    const note = data[1] & 0x7f;
    const velocity = data.length > 2 ? data[2] & 0x7f : 0;

    if (status === 0x90 && velocity > 0) {
      active.set(note, (active.get(note) || 0) + 1);
      // Map MIDI 0–127 velocity → NES 1–15
      const nesVel = Math.max(1, Math.min(15, Math.round((velocity / 127) * 15)));
      handlers.onNoteOn(note, nesVel);
      return;
    }
    if (status === 0x80 || (status === 0x90 && velocity === 0)) {
      const count = (active.get(note) || 1) - 1;
      if (count <= 0) active.delete(note);
      else active.set(note, count);
      if (count <= 0) handlers.onNoteOff(note);
    }
  }

  function bindInputs() {
    if (!access) return;
    let firstName = null;
    let count = 0;
    for (const input of access.inputs.values()) {
      input.onmidimessage = onMessage;
      if (!firstName) firstName = input.name || "MIDI device";
      count += 1;
    }
    emitStatus({
      supported: true,
      connected: count > 0,
      name: firstName,
    });
  }

  return {
    async start() {
      if (!navigator.requestMIDIAccess) {
        emitStatus({
          supported: false,
          connected: false,
          name: null,
          error: "Web MIDI is not supported in this browser (try Chrome or Firefox).",
        });
        return;
      }
      try {
        access = await navigator.requestMIDIAccess({ sysex: false });
        access.onstatechange = () => bindInputs();
        bindInputs();
      } catch (err) {
        emitStatus({
          supported: true,
          connected: false,
          name: null,
          error: err instanceof Error ? err.message : "MIDI permission denied",
        });
      }
    },
    stop() {
      if (!access) return;
      for (const input of access.inputs.values()) {
        input.onmidimessage = null;
      }
      access.onstatechange = null;
      access = null;
      active.clear();
    },
  };
}

/**
 * Detect support without requesting permission.
 * @returns {boolean}
 */
export function isMidiSupported() {
  return typeof navigator !== "undefined" && Boolean(navigator.requestMIDIAccess);
}
