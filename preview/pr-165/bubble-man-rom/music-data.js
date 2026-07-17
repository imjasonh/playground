export const TICKS_PER_BEAT = 4;
export const BPM = 180;

const note = (start, duration, pitch, byte, address, label = "") => ({
  start,
  duration,
  pitch,
  byte,
  address,
  label,
});

const rest = (start, duration, byte, address) =>
  note(start, duration, null, byte, address, "rest");

export const sections = [
  {
    id: "intro",
    eyebrow: "Measures 1–4 · Opening phrase",
    title: "A quiet opening, assembled one byte at a time",
    summary:
      "Long low notes leave room for a fast broken-chord texture. The foreground sounds spacious even though the accompaniment is already moving every eighth note.",
    insight:
      "The first pulse changes from a thin 12.5% duty cycle to a bright 75% duty cycle midway through the excerpt. One oscillator convincingly becomes a second instrument.",
    durationTicks: 64,
    channels: [
      {
        id: "pulse1",
        name: "Pulse 1",
        color: "#ffcf70",
        wave: "pulse",
        duty: 0.125,
        gain: 0.17,
        events: [
          note(0, 8, "G2", "$CC", "$A1A7"),
          note(8, 4, "Ab2", "$AD", "$A1A8"),
          note(12, 2, "Bb2", "$8F", "$A1A9"),
          note(14, 16, "G2", "$EC", "$A1AA"),
          rest(30, 2, "$80", "$A1AB"),
          note(32, 8, "F2", "$CA", "$A1AC"),
          note(40, 4, "F2", "$AA", "$A1AD"),
          note(44, 2, "G2", "$8C", "$A1AE"),
          note(46, 2, "A1", "$82", "$A1AF"),
          note(48, 2, "G4", "$98", "$A1B4"),
          note(50, 2, "G4", "$98", "$A1B5"),
          note(52, 2, "F4", "$96", "$A1B8"),
          rest(54, 2, "$80", "$A1B9"),
          note(56, 2, "G4", "$98", "$A1BB"),
          note(58, 2, "G4", "$98", "$A1BC"),
          note(60, 2, "F4", "$96", "$A1BF"),
          rest(62, 2, "$80", "$A1C0"),
        ],
      },
      {
        id: "triangle",
        name: "Triangle",
        color: "#68d7d3",
        wave: "triangle",
        gain: 0.12,
        events: [
          "Eb3", "G3", "Eb4", "Eb3", "G3", "C4", "Eb4", "Ab3",
          "G3", "Eb4", "Eb3", "Eb4", "G3", "Eb3", "Eb4", "G3",
          "D3", "F3", "D4", "D3", "F3", "Bb3", "D4", "G3",
          "F3", "D4", "D3", "D4", "F3", "D3", "D4", "F3",
        ].map((pitch, index) =>
          note(index * 2, 2, pitch, index === 0 ? "$88" : "…", `$A${(0x3aa + index).toString(16).toUpperCase()}`),
        ),
      },
      {
        id: "noise",
        name: "Noise",
        color: "#a6a8c9",
        wave: "noise",
        gain: 0.055,
        events: Array.from({ length: 8 }, (_, index) =>
          note(index * 8, 1.2, "noise", "$83", "$A45D"),
        ),
      },
    ],
    code: [
      { address: "$A19C", bytes: "00 05", asm: "SET_SPEED $05", comment: "180 BPM on NTSC" },
      { address: "$A19E", bytes: "02 00", asm: "SET_DUTY $00", comment: "thin 12.5% pulse" },
      { address: "$A1A0", bytes: "05 13", asm: "SET_NOTE_BASE $13", comment: "select pitch table window" },
      { address: "$A1A2", bytes: "03 3D", asm: "SET_VOLUME_ENV $3D", comment: "pulse envelope" },
      { address: "$A1A4", bytes: "07 92 10", asm: "SET_VOLUME_CURVE $92,$10", comment: "decaying attack" },
      { address: "$A1A7", bytes: "CC AD 8F EC 80", asm: "G2  Ab2  Bb2  G2  REST", comment: "½, ¼, ⅛, whole, ⅛" },
      { address: "$A1AC", bytes: "CA AA 8C 82", asm: "F2  F2  G2  A1", comment: "½, ¼, ⅛, ⅛" },
      { address: "$A1B0", bytes: "02 C0", asm: "SET_DUTY $C0", comment: "bright 75% pulse" },
      { address: "$A1B2", bytes: "05 1F", asm: "SET_NOTE_BASE $1F", comment: "jump up two octaves" },
      { address: "$A1B4", bytes: "98 98 01 25 96 80", asm: "G4 G4 · F4 REST", comment: "short high response" },
    ],
  },
  {
    id: "ostinato",
    eyebrow: "Measures 9–10 · Loop entry",
    title: "The introduction disappears, but the machinery continues",
    summary:
      "The infinite loop begins here. Pulse 1 alternates registers so rapidly that the ear separates a low pedal from a high answering voice.",
    insight:
      "Nothing in the ROM says “two voices.” Alternating C3 and C4 on one monophonic channel creates that illusion perceptually.",
    durationTicks: 32,
    channels: [
      {
        id: "pulse1",
        name: "Pulse 1",
        color: "#ffcf70",
        wave: "pulse",
        duty: 0.5,
        gain: 0.15,
        events: [
          note(0, 4, "C3", "$B1", "$A1CC"),
          note(4, 2, "C4", "$9D", "$A1CF"),
          note(6, 2, "C3", "$91", "$A1D2"),
          rest(8, 2, "$80", "$A1D3"),
          note(10, 2, "Bb2", "$8F", "$A1D4"),
          note(12, 2, "C4", "$9D", "$A1D7"),
          note(14, 2, "C3", "$91", "$A1DA"),
          note(16, 4, "C3", "$B1", "$A1CC"),
          note(20, 2, "C4", "$9D", "$A1CF"),
          note(22, 2, "C3", "$91", "$A1D2"),
          rest(24, 2, "$80", "$A1D3"),
          note(26, 2, "Bb2", "$8F", "$A1D4"),
          note(28, 2, "C4", "$9D", "$A1D7"),
          note(30, 2, "C3", "$91", "$A1DA"),
        ],
      },
      {
        id: "pulse2",
        name: "Pulse 2",
        color: "#ff7f88",
        wave: "pulse",
        duty: 0.5,
        gain: 0.09,
        events: [
          "Eb2", "G3", "Eb3", "Eb2", "G3", "C3", "Eb3", "Ab2",
          "G3", "Eb3", "Eb2", "Eb3", "G3", "Eb2", "Eb3", "G3",
        ].map((pitch, index) => note(index * 2, 2, pitch, "·", "$A2F4")),
      },
      {
        id: "triangle",
        name: "Triangle",
        color: "#68d7d3",
        wave: "triangle",
        gain: 0.11,
        events: [
          "Eb3", "G3", "Eb4", "Eb3", "G3", "C4", "Eb4", "Ab3",
          "G3", "Eb4", "Eb3", "Eb4", "G3", "Eb3", "Eb4", "G3",
        ].map((pitch, index) => note(index * 2, 2, pitch, "·", "$A3F5")),
      },
      {
        id: "noise",
        name: "Noise",
        color: "#a6a8c9",
        wave: "noise",
        gain: 0.05,
        events: Array.from({ length: 8 }, (_, index) =>
          note(index * 4, index % 2 ? 0.8 : 1.4, "noise", "$83", "$A48E"),
        ),
      },
    ],
    code: [
      { address: "$A1C8", bytes: "02 80", asm: "SET_DUTY $80", comment: "fuller 50% pulse" },
      { address: "$A1CA", bytes: "05 13", asm: "SET_NOTE_BASE $13", comment: "return to low register" },
      { address: "$A1CC", bytes: "B1 01 10 9D 01 00 91", asm: "C3 · C4 · C3", comment: "quarter + two eighths" },
      { address: "$A1D3", bytes: "80 8F 01 10 9D 01 00 91", asm: "REST Bb2 · C4 · C3", comment: "answering half-bar" },
      { address: "$A1DB", bytes: "04 01 C8 A1", asm: "LOOP 1, $A1C8", comment: "play the cell twice" },
      { address: "$A3F5", bytes: "88 98 94 88 98 91 94 8D", asm: "Eb G Eb Eb G C Eb Ab", comment: "triangle broken harmony" },
    ],
  },
  {
    id: "lead",
    eyebrow: "Measures 17–18 · Lead entrance",
    title: "Three lines cooperate to imply an ensemble",
    summary:
      "Pulse 1 becomes the soloist. Pulse 2 shadows its contour while triangle preserves the harmonic current below it.",
    insight:
      "Sustained notes switch to vibrato definition 1. The modulation is data-driven: the same pulse oscillator now reads as an expressive lead.",
    durationTicks: 32,
    channels: [
      {
        id: "pulse1",
        name: "Pulse 1 lead",
        color: "#ffcf70",
        wave: "pulse",
        duty: 0.75,
        gain: 0.17,
        events: [
          note(0, 4, "Eb4", "$B4", "$A21B"),
          note(4, 4, "Eb4", "$B4", "$A21E"),
          note(8, 2, "Eb4", "$94", "$A221"),
          note(10, 2, "F4", "$96", "$A222"),
          rest(12, 2, "$80", "$A223"),
          note(14, 2, "G4", "$98", "$A224"),
          rest(16, 2, "$80", "$A225"),
          note(18, 2, "F4", "$96", "$A226"),
          rest(20, 2, "$80", "$A227"),
          note(22, 2, "Eb4", "$94", "$A228"),
          rest(24, 2, "$80", "$A229"),
          note(26, 2, "Eb4", "$94", "$A22A"),
          note(28, 4, "F4", "$B6", "$A22B"),
        ],
      },
      {
        id: "pulse2",
        name: "Pulse 2 harmony",
        color: "#ff7f88",
        wave: "pulse",
        duty: 0.75,
        gain: 0.085,
        events: [
          rest(0, 3, "$06 $80", "$A311"),
          note(3, 8, "Eb4", "$D4", "$A313"),
          note(11, 2, "Eb4", "$94", "$A314"),
          note(13, 2, "F4", "$96", "$A315"),
          rest(15, 2, "$80", "$A316"),
          note(17, 2, "G4", "$98", "$A317"),
          rest(19, 2, "$80", "$A318"),
          note(21, 2, "F4", "$96", "$A319"),
          rest(23, 2, "$80", "$A31A"),
          note(25, 2, "Eb4", "$94", "$A31B"),
          rest(27, 2, "$80", "$A31C"),
          note(29, 3, "Eb4", "$94", "$A31D"),
        ],
      },
      {
        id: "triangle",
        name: "Triangle",
        color: "#68d7d3",
        wave: "triangle",
        gain: 0.105,
        events: [
          "Eb3", "G3", "Eb4", "Eb3", "G3", "C4", "Eb4", "Ab3",
          "G3", "Eb4", "Eb3", "Eb4", "G3", "Eb3", "Eb4", "G3",
        ].map((pitch, index) => note(index * 2, 2, pitch, "·", "$A3F5")),
      },
      {
        id: "noise",
        name: "Noise",
        color: "#a6a8c9",
        wave: "noise",
        gain: 0.045,
        events: Array.from({ length: 8 }, (_, index) =>
          note(index * 4, index % 2 ? 0.8 : 1.3, "noise", "$83", "$A48E"),
        ),
      },
    ],
    code: [
      { address: "$A213", bytes: "02 C0", asm: "SET_DUTY $C0", comment: "bright lead timbre" },
      { address: "$A215", bytes: "03 3D 07 92 10", asm: "SET_ENV / CURVE", comment: "strong, decaying attack" },
      { address: "$A21A", bytes: "21", asm: "NOTE_DELAY 1", comment: "shape the repeated attack" },
      { address: "$A21B", bytes: "B4 08 01 B4 08 00", asm: "Eb4  VIBRATO_1  Eb4  OFF", comment: "two tied-feeling quarters" },
      { address: "$A221", bytes: "94 96 80 98 80 96 80 94 80", asm: "Eb F · G · F · Eb ·", comment: "staccato eighth-note answer" },
      { address: "$A22A", bytes: "94 B6", asm: "Eb4 F4", comment: "eighth into quarter" },
    ],
  },
  {
    id: "turnaround",
    eyebrow: "Measures 31–32 · Loop turnaround",
    title: "The missing chord appears between the channels",
    summary:
      "Rapid A-flat and G arpeggios meet a B–D–F–G ascent. Together they spell G7, a secondary dominant that pulls the music back to C at the loop point.",
    insight:
      "The ROM never stores “G7.” It stores four independent streams whose simultaneous pitch collections make the listener infer G–B–D–F.",
    durationTicks: 32,
    channels: [
      {
        id: "pulse1",
        name: "Pulse 1",
        color: "#ffcf70",
        wave: "pulse",
        duty: 0.75,
        gain: 0.15,
        events: [
          note(0, 4, "G3", "$AC", "$A289"),
          note(4, 4, "F3", "$AA", "$A28A"),
          note(8, 4, "Bb3", "$AF", "$A28B"),
          note(12, 4, "Ab3", "$AD", "$A28C"),
          note(16, 4, "G3", "$AC", "$A28D"),
          note(20, 4, "B3", "$B0", "$A2B5"),
          note(24, 4, "D4", "$B3", "$A2B6"),
          note(28, 3, "F4", "$B6", "$A2B7"),
          note(31, 1, "G4", "$98", "$A2B8"),
        ],
      },
      {
        id: "pulse2",
        name: "Pulse 2 arpeggio",
        color: "#ff7f88",
        wave: "pulse",
        duty: 0.75,
        gain: 0.1,
        events: [
          "Ab4", "Eb4", "C4", "C5", "Ab4", "Eb4", "C4", "C5",
          "G4", "D4", "B3", "G3", "G4", "D4", "B3", "G3",
        ].map((pitch, index) =>
          note(index * 2, 2, pitch, index < 8 ? ["$79", "$74", "$71", "$7D"][index % 4] : ["$78", "$73", "$70", "$6C"][index % 4], "$A34A"),
        ),
      },
      {
        id: "triangle",
        name: "Triangle bass",
        color: "#68d7d3",
        wave: "triangle",
        gain: 0.11,
        events: [
          note(0, 4, "Ab3", "$8D", "$A445"),
          note(4, 4, "C4", "$91", "$A446"),
          note(8, 4, "Eb4", "$94", "$A447"),
          note(12, 4, "Ab3", "$8D", "$A448"),
          note(16, 4, "G3", "$8C", "$A44E"),
          note(20, 4, "B3", "$90", "$A44F"),
          note(24, 4, "D4", "$93", "$A450"),
          note(28, 4, "G4", "$98", "$A451"),
        ],
      },
      {
        id: "noise",
        name: "Noise",
        color: "#a6a8c9",
        wave: "noise",
        gain: 0.05,
        events: Array.from({ length: 8 }, (_, index) =>
          note(index * 4, index % 2 ? 0.8 : 1.3, "noise", "$83", "$A48E"),
        ),
      },
    ],
    code: [
      { address: "$A34A", bytes: "79 74 71 7D", asm: "Ab4 Eb4 C4 C5", comment: "four sixteenths" },
      { address: "$A34E", bytes: "79 74 71 7D", asm: "Ab4 Eb4 C4 C5", comment: "repeat the A-flat color" },
      { address: "$A35A", bytes: "78 73 70 6C", asm: "G4 D4 B3 G3", comment: "G-major arpeggio" },
      { address: "$A35E", bytes: "78 73 70 6C", asm: "G4 D4 B3 G3", comment: "repeat" },
      { address: "$A2B5", bytes: "B0 B3 B6 98", asm: "B3 D4 F4 G4", comment: "adds the seventh: G7" },
      { address: "$A2B9", bytes: "04 00 C8 A1", asm: "LOOP 0, $A1C8", comment: "jump back to measure 9" },
    ],
  },
];

export const opcodeRows = [
  ["$00", "SET_SPEED n", "Set the duration multiplier for this channel."],
  ["$01", "MODULATION n", "Reverse-engineered control used for articulation/modulation; its exact original name is unknown."],
  ["$02", "SET_DUTY n", "Choose the pulse width, changing the apparent instrument."],
  ["$03", "SET_VOLUME_ENV n", "Set volume and APU envelope flags."],
  ["$04", "LOOP count, address", "Jump backward a fixed number of times; count 0 loops forever."],
  ["$05", "SET_NOTE_BASE n", "Move the five-bit pitch window to another register."],
  ["$06", "EXTRA_LENGTH note", "Use dotted/intermediate lengths such as 12 or 24."],
  ["$07", "SET_VOLUME_CURVE a,b", "Configure a software volume ramp."],
  ["$08", "SET_VIBRATO_INDEX n", "Select one four-byte vibrato definition."],
  ["note", "pitch + duration", "Most musical events fit in one byte; pitch 0 means rest."],
];

export function getSection(id) {
  return sections.find((section) => section.id === id) ?? sections[0];
}

export function formatTime(seconds) {
  const minutes = Math.floor(seconds / 60);
  return `${minutes}:${String(Math.floor(seconds % 60)).padStart(2, "0")}`;
}

export function pitchToMidi(pitch) {
  if (!pitch || pitch === "noise") return null;
  const match = /^([A-G])([b#]?)(-?\d)$/.exec(pitch);
  if (!match) return null;
  const semitones = { C: 0, D: 2, E: 4, F: 5, G: 7, A: 9, B: 11 };
  const accidental = match[2] === "b" ? -1 : match[2] === "#" ? 1 : 0;
  return (Number(match[3]) + 1) * 12 + semitones[match[1]] + accidental;
}
