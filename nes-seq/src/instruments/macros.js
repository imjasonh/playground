/**
 * FamiTracker-style instrument macros for NES channels.
 *
 * Each macro is a sequence of values replayed while a note is held.
 * Empty sequences mean "use the instrument's static default".
 */

/**
 * @typedef {"pulse1"|"pulse2"|"triangle"|"noise"} ChannelId
 *
 * @typedef {object} Instrument
 * @property {string} id
 * @property {string} name
 * @property {ChannelId} channel
 * @property {number} duty          pulse duty 0–3 (ignored for others)
 * @property {number} volume        0–15 default volume
 * @property {number[]} volumeMacro
 * @property {number[]} dutyMacro
 * @property {number[]} arpMacro    semitone offsets relative to note
 * @property {number} macroSpeed    engine ticks per macro step (≥1)
 * @property {boolean} shortNoise   noise LFSR mode
 */

/**
 * @returns {Instrument[]}
 */
export function createDefaultInstruments() {
  return [
    {
      id: "pulse-lead",
      name: "Pulse Lead",
      channel: "pulse1",
      duty: 2,
      volume: 12,
      volumeMacro: [12, 12, 11, 10, 9, 8, 8, 7],
      dutyMacro: [],
      arpMacro: [],
      macroSpeed: 2,
      shortNoise: false,
    },
    {
      id: "pulse-square",
      name: "Pulse Square",
      channel: "pulse2",
      duty: 2,
      volume: 10,
      volumeMacro: [],
      dutyMacro: [2, 2, 1, 1],
      arpMacro: [],
      macroSpeed: 3,
      shortNoise: false,
    },
    {
      id: "pulse-arp",
      name: "Major Arp",
      channel: "pulse1",
      duty: 1,
      volume: 11,
      volumeMacro: [11, 10, 9, 9],
      dutyMacro: [],
      arpMacro: [0, 4, 7],
      macroSpeed: 2,
      shortNoise: false,
    },
    {
      id: "tri-bass",
      name: "Tri Bass",
      channel: "triangle",
      duty: 0,
      volume: 15,
      volumeMacro: [],
      dutyMacro: [],
      arpMacro: [],
      macroSpeed: 1,
      shortNoise: false,
    },
    {
      id: "noise-hat",
      name: "Noise Hat",
      channel: "noise",
      duty: 0,
      volume: 10,
      volumeMacro: [10, 8, 6, 4, 2, 0],
      dutyMacro: [],
      arpMacro: [],
      macroSpeed: 1,
      shortNoise: true,
    },
    {
      id: "noise-snare",
      name: "Noise Snare",
      channel: "noise",
      duty: 0,
      volume: 12,
      volumeMacro: [12, 11, 9, 6, 3, 0],
      dutyMacro: [],
      arpMacro: [],
      macroSpeed: 1,
      shortNoise: false,
    },
  ];
}

/**
 * Runtime voice state for macro expansion.
 * @typedef {object} VoiceState
 * @property {Instrument} instrument
 * @property {number} noteMidi
 * @property {number} tick
 * @property {boolean} active
 * @property {number} releaseTicks  0 = sustaining; >0 counting down after note-off
 */

/**
 * @param {Instrument} instrument
 * @param {number} noteMidi
 * @returns {VoiceState}
 */
export function startVoice(instrument, noteMidi) {
  return {
    instrument: cloneInstrument(instrument),
    noteMidi,
    tick: 0,
    active: true,
    releaseTicks: 0,
  };
}

/**
 * @param {VoiceState} voice
 * @param {number} [releaseLength=6]
 */
export function releaseVoice(voice, releaseLength = 6) {
  if (!voice.active) return;
  voice.releaseTicks = Math.max(1, releaseLength);
}

/**
 * Advance macros by one engine tick and return the current sounding params.
 *
 * @param {VoiceState} voice
 * @returns {{ midi: number, volume: number, duty: number, shortNoise: boolean, active: boolean }}
 */
export function tickVoice(voice) {
  if (!voice.active) {
    return {
      midi: voice.noteMidi,
      volume: 0,
      duty: voice.instrument.duty,
      shortNoise: voice.instrument.shortNoise,
      active: false,
    };
  }

  const inst = voice.instrument;
  const speed = Math.max(1, inst.macroSpeed | 0);
  const step = Math.floor(voice.tick / speed);

  let volume = macroValue(inst.volumeMacro, step, inst.volume);
  const duty = macroValue(inst.dutyMacro, step, inst.duty) & 3;
  const arp = macroValue(inst.arpMacro, step, 0);
  const midi = clampInt(voice.noteMidi + arp, 0, 127);

  if (voice.releaseTicks > 0) {
    voice.releaseTicks -= 1;
    volume = Math.max(0, Math.floor(volume * (voice.releaseTicks / 6)));
    if (voice.releaseTicks <= 0 || volume <= 0) {
      voice.active = false;
      volume = 0;
    }
  } else if (
    inst.volumeMacro.length > 0 &&
    step >= inst.volumeMacro.length - 1 &&
    volume <= 0
  ) {
    // One-shot volume macros (drums) end the voice.
    voice.active = false;
  }

  voice.tick += 1;

  return {
    midi,
    volume: clampInt(volume, 0, 15),
    duty,
    shortNoise: inst.shortNoise,
    active: voice.active,
  };
}

/**
 * Hold the last macro value when past the end (FamiTracker-style).
 * @param {number[]} sequence
 * @param {number} step
 * @param {number} fallback
 */
export function macroValue(sequence, step, fallback) {
  if (!sequence || sequence.length === 0) return fallback;
  if (step < 0) return sequence[0];
  if (step >= sequence.length) return sequence[sequence.length - 1];
  return sequence[step];
}

/**
 * @param {Instrument} instrument
 * @returns {Instrument}
 */
export function cloneInstrument(instrument) {
  return {
    id: instrument.id,
    name: instrument.name,
    channel: instrument.channel,
    duty: instrument.duty,
    volume: instrument.volume,
    volumeMacro: [...instrument.volumeMacro],
    dutyMacro: [...instrument.dutyMacro],
    arpMacro: [...instrument.arpMacro],
    macroSpeed: instrument.macroSpeed,
    shortNoise: instrument.shortNoise,
  };
}

/**
 * Serialize-friendly plain object.
 * @param {Instrument} instrument
 */
export function instrumentToJSON(instrument) {
  return cloneInstrument(instrument);
}

/**
 * @param {unknown} raw
 * @returns {Instrument}
 */
export function instrumentFromJSON(raw) {
  const o = raw && typeof raw === "object" ? raw : {};
  const channel = ["pulse1", "pulse2", "triangle", "noise"].includes(o.channel)
    ? o.channel
    : "pulse1";
  return {
    id: String(o.id || "custom"),
    name: String(o.name || "Custom"),
    channel,
    duty: clampInt(o.duty ?? 2, 0, 3),
    volume: clampInt(o.volume ?? 10, 0, 15),
    volumeMacro: asIntArray(o.volumeMacro),
    dutyMacro: asIntArray(o.dutyMacro),
    arpMacro: asIntArray(o.arpMacro, true),
    macroSpeed: Math.max(1, clampInt(o.macroSpeed ?? 1, 1, 16)),
    shortNoise: Boolean(o.shortNoise),
  };
}

function asIntArray(value, signed = false) {
  if (!Array.isArray(value)) return [];
  return value.map((n) => {
    const v = Number(n) | 0;
    return signed ? clampInt(v, -24, 24) : clampInt(v, 0, 15);
  });
}

function clampInt(value, min, max) {
  return Math.min(max, Math.max(min, Number(value) | 0));
}
