/** NTSC master CPU clock (Hz). */
export const CPU_CLOCK_NTSC = 1_789_772.727_272_727_2;

/** APU frame sequencer rates (NTSC), approx 240 Hz quarter-frames. */
export const FRAME_SEQUENCER_HZ = 240;

/** Hardware length-counter load values ($400x bits 7-3). */
export const LENGTH_TABLE = Object.freeze([
  10, 254, 20, 2, 40, 4, 80, 6, 160, 8, 60, 10, 14, 12, 26, 14, 12, 16, 24, 18,
  48, 20, 96, 22, 192, 24, 72, 26, 16, 28, 32, 30,
]);

/** Noise timer periods (NTSC), indexed by $400E low nibble. */
export const NOISE_PERIODS_NTSC = Object.freeze([
  4, 8, 16, 32, 64, 96, 128, 160, 202, 254, 380, 508, 762, 1016, 2034, 4068,
]);

/** Pulse duty sequencer bit patterns (8 steps). */
export const DUTY_SEQUENCES = Object.freeze([
  Object.freeze([0, 1, 0, 0, 0, 0, 0, 0]), // 12.5%
  Object.freeze([0, 1, 1, 0, 0, 0, 0, 0]), // 25%
  Object.freeze([0, 1, 1, 1, 1, 0, 0, 0]), // 50%
  Object.freeze([1, 0, 0, 1, 1, 1, 1, 1]), // 75%
]);

/** Triangle 32-step waveform. */
export const TRIANGLE_SEQUENCE = Object.freeze([
  15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 0, 1, 2, 3, 4, 5, 6, 7,
  8, 9, 10, 11, 12, 13, 14, 15,
]);

export const DUTY_LABELS = Object.freeze([
  "12.5%",
  "25%",
  "50%",
  "75%",
]);

export const CHANNELS = Object.freeze([
  "pulse1",
  "pulse2",
  "triangle",
  "noise",
]);

export const CHANNEL_LABELS = Object.freeze({
  pulse1: "Pulse 1",
  pulse2: "Pulse 2",
  triangle: "Triangle",
  noise: "Noise",
});
