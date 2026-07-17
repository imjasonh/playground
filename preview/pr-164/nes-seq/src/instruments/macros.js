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
 * @property {number} duty
 * @property {number} volume
 * @property {number[]} volumeMacro
 * @property {number[]} dutyMacro
 * @property {number[]} arpMacro          semitone offsets
 * @property {number[]} pitchMacro        cumulative period units per macro step
 * @property {number} vibratoSpeed        ticks per vibrato phase step (0 = off)
 * @property {number} vibratoDepth        period units peak deviation
 * @property {number} delay               ticks before the note becomes audible
 * @property {number} macroSpeed
 * @property {boolean} shortNoise
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
      pitchMacro: [],
      vibratoSpeed: 0,
      vibratoDepth: 0,
      delay: 0,
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
      pitchMacro: [],
      vibratoSpeed: 3,
      vibratoDepth: 2,
      delay: 0,
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
      pitchMacro: [],
      vibratoSpeed: 0,
      vibratoDepth: 0,
      delay: 0,
      macroSpeed: 2,
      shortNoise: false,
    },
    {
      id: "pulse-vib",
      name: "Vibrato Lead",
      channel: "pulse1",
      duty: 2,
      volume: 11,
      volumeMacro: [11, 11, 10, 10],
      dutyMacro: [],
      arpMacro: [],
      pitchMacro: [],
      vibratoSpeed: 2,
      vibratoDepth: 3,
      delay: 0,
      macroSpeed: 1,
      shortNoise: false,
    },
    {
      id: "pulse-bend",
      name: "Pitch Drop",
      channel: "pulse2",
      duty: 1,
      volume: 12,
      volumeMacro: [12, 11, 10, 8, 6, 4],
      dutyMacro: [],
      arpMacro: [],
      pitchMacro: [0, 2, 4, 8, 12, 18, 24],
      vibratoSpeed: 0,
      vibratoDepth: 0,
      delay: 0,
      macroSpeed: 1,
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
      pitchMacro: [],
      vibratoSpeed: 0,
      vibratoDepth: 0,
      delay: 0,
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
      pitchMacro: [],
      vibratoSpeed: 0,
      vibratoDepth: 0,
      delay: 0,
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
      pitchMacro: [],
      vibratoSpeed: 0,
      vibratoDepth: 0,
      delay: 0,
      macroSpeed: 1,
      shortNoise: false,
    },
  ];
}

/**
 * Instruments available for a channel (preset library).
 * @param {ChannelId} channel
 */
export function presetsForChannel(channel) {
  return createDefaultInstruments().filter((i) => i.channel === channel);
}

/**
 * @typedef {object} VoiceState
 * @property {Instrument} instrument
 * @property {number} noteMidi
 * @property {number} tick
 * @property {boolean} active
 * @property {number} releaseTicks
 * @property {number} delayLeft
 * @property {number} pitchAccum
 * @property {number} [slideFromMidi]
 * @property {number} [slideToMidi]
 * @property {number} [slideTotalTicks]
 * @property {number} [slideTick]
 */

/**
 * @param {Instrument} instrument
 * @param {number} noteMidi
 * @param {{ slideTo?: number, slideTicks?: number }} [opts]
 * @returns {VoiceState}
 */
export function startVoice(instrument, noteMidi, opts = {}) {
  /** @type {VoiceState} */
  const voice = {
    instrument: cloneInstrument(instrument),
    noteMidi,
    tick: 0,
    active: true,
    releaseTicks: 0,
    delayLeft: Math.max(0, instrument.delay | 0),
    pitchAccum: 0,
  };
  if (opts.slideTo != null && opts.slideTicks != null && opts.slideTicks > 0) {
    voice.slideFromMidi = noteMidi;
    voice.slideToMidi = opts.slideTo;
    voice.slideTotalTicks = opts.slideTicks;
    voice.slideTick = 0;
  }
  return voice;
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
 * @typedef {object} VoiceParams
 * @property {number} midi
 * @property {number} volume
 * @property {number} duty
 * @property {boolean} shortNoise
 * @property {boolean} active
 * @property {number} periodOffset   signed timer-period adjustment
 */

/**
 * @param {VoiceState} voice
 * @returns {VoiceParams}
 */
export function tickVoice(voice) {
  const inst = voice.instrument;
  if (!voice.active) {
    return {
      midi: voice.noteMidi,
      volume: 0,
      duty: inst.duty,
      shortNoise: inst.shortNoise,
      active: false,
      periodOffset: 0,
    };
  }

  if (voice.delayLeft > 0) {
    voice.delayLeft -= 1;
    voice.tick += 1;
    return {
      midi: voice.noteMidi,
      volume: 0,
      duty: inst.duty,
      shortNoise: inst.shortNoise,
      active: true,
      periodOffset: 0,
    };
  }

  const speed = Math.max(1, inst.macroSpeed | 0);
  const step = Math.floor(voice.tick / speed);

  let volume = macroValue(inst.volumeMacro, step, inst.volume);
  const duty = macroValue(inst.dutyMacro, step, inst.duty) & 3;
  const arp = macroValue(inst.arpMacro, step, 0);

  // Pitch macro: accumulate period units each macro step (once per speed boundary).
  if (
    inst.pitchMacro.length > 0 &&
    voice.tick % speed === 0 &&
    step < inst.pitchMacro.length
  ) {
    voice.pitchAccum += inst.pitchMacro[step] | 0;
  }

  let midi = voice.noteMidi + arp;
  if (
    voice.slideToMidi != null &&
    voice.slideFromMidi != null &&
    voice.slideTotalTicks
  ) {
    const t = Math.min(voice.slideTick ?? 0, voice.slideTotalTicks);
    const alpha = t / voice.slideTotalTicks;
    midi =
      voice.slideFromMidi +
      (voice.slideToMidi - voice.slideFromMidi) * alpha;
    voice.slideTick = (voice.slideTick ?? 0) + 1;
  }
  midi = clampInt(Math.round(midi), 0, 127);

  let periodOffset = voice.pitchAccum;
  if (inst.vibratoDepth > 0 && inst.vibratoSpeed > 0) {
    const phase = Math.floor(voice.tick / Math.max(1, inst.vibratoSpeed));
    // 4-step triangle: 0, +d, 0, -d — cheap and NES-flavored.
    const tri = [0, 1, 0, -1][phase & 3];
    periodOffset += tri * (inst.vibratoDepth | 0);
  }

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
    voice.active = false;
  }

  voice.tick += 1;

  return {
    midi,
    volume: clampInt(volume, 0, 15),
    duty,
    shortNoise: inst.shortNoise,
    active: voice.active,
    periodOffset,
  };
}

/**
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
    volumeMacro: [...(instrument.volumeMacro || [])],
    dutyMacro: [...(instrument.dutyMacro || [])],
    arpMacro: [...(instrument.arpMacro || [])],
    pitchMacro: [...(instrument.pitchMacro || [])],
    vibratoSpeed: instrument.vibratoSpeed | 0,
    vibratoDepth: instrument.vibratoDepth | 0,
    delay: instrument.delay | 0,
    macroSpeed: instrument.macroSpeed,
    shortNoise: Boolean(instrument.shortNoise),
  };
}

/**
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
    pitchMacro: asIntArray(o.pitchMacro, true, -64, 64),
    vibratoSpeed: clampInt(o.vibratoSpeed ?? 0, 0, 16),
    vibratoDepth: clampInt(o.vibratoDepth ?? 0, 0, 16),
    delay: clampInt(o.delay ?? 0, 0, 48),
    macroSpeed: Math.max(1, clampInt(o.macroSpeed ?? 1, 1, 16)),
    shortNoise: Boolean(o.shortNoise),
  };
}

function asIntArray(value, signed = false, min = 0, max = 15) {
  if (!Array.isArray(value)) return [];
  const lo = signed ? (arguments.length > 2 ? min : -24) : min;
  const hi = signed ? (arguments.length > 2 ? max : 24) : max;
  return value.map((n) => clampInt(n, lo, hi));
}

function clampInt(value, min, max) {
  return Math.min(max, Math.max(min, Number(value) | 0));
}
