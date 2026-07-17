import {
  CPU_CLOCK_NTSC,
  DUTY_SEQUENCES,
  LENGTH_TABLE,
  NOISE_PERIODS_NTSC,
  TRIANGLE_SEQUENCE,
} from "./constants.js";

/**
 * Cycle-driven NES 2A03 APU (Pulse1, Pulse2, Triangle, Noise).
 * DMC is stubbed silent for v1. Suitable for AudioWorklet + offline render.
 */
export class NesApu {
  /**
   * @param {{ cpuClock?: number }} [options]
   */
  constructor({ cpuClock = CPU_CLOCK_NTSC } = {}) {
    this.cpuClock = cpuClock;
    this.pulse1 = createPulse();
    this.pulse2 = createPulse();
    this.triangle = createTriangle();
    this.noise = createNoise();
    this.status = 0; // $4015
    this.frameCounterMode = 0; // 0 = 4-step, 1 = 5-step
    this.irqInhibit = true;
    this.frameCycle = 0;
    this.frameStep = 0;
    this.sampleAccumulator = 0;
    this.reset();
  }

  reset() {
    this.pulse1 = createPulse();
    this.pulse2 = createPulse();
    this.triangle = createTriangle();
    this.noise = createNoise();
    this.status = 0;
    this.frameCounterMode = 0;
    this.irqInhibit = true;
    this.frameCycle = 0;
    this.frameStep = 0;
    this.sampleAccumulator = 0;
  }

  /**
   * Write an APU register (CPU address $4000–$4017 subset).
   * @param {number} address
   * @param {number} value
   */
  writeRegister(address, value) {
    const v = value & 0xff;
    const addr = address & 0xffff;
    switch (addr) {
      case 0x4000:
        writePulseControl(this.pulse1, v);
        break;
      case 0x4001:
        writePulseSweep(this.pulse1, v);
        break;
      case 0x4002:
        this.pulse1.timerPeriod = (this.pulse1.timerPeriod & 0x700) | v;
        break;
      case 0x4003:
        writePulseLength(this.pulse1, v, (this.status & 0x01) !== 0);
        break;
      case 0x4004:
        writePulseControl(this.pulse2, v);
        break;
      case 0x4005:
        writePulseSweep(this.pulse2, v);
        break;
      case 0x4006:
        this.pulse2.timerPeriod = (this.pulse2.timerPeriod & 0x700) | v;
        break;
      case 0x4007:
        writePulseLength(this.pulse2, v, (this.status & 0x02) !== 0);
        break;
      case 0x4008:
        this.triangle.linearReload = v & 0x7f;
        this.triangle.controlFlag = (v & 0x80) !== 0;
        this.triangle.halt = this.triangle.controlFlag;
        break;
      case 0x400a:
        this.triangle.timerPeriod = (this.triangle.timerPeriod & 0x700) | v;
        break;
      case 0x400b:
        this.triangle.timerPeriod =
          (this.triangle.timerPeriod & 0xff) | ((v & 0x07) << 8);
        if (this.status & 0x04) {
          this.triangle.lengthCounter = LENGTH_TABLE[v >> 3];
        }
        this.triangle.linearReloadFlag = true;
        this.triangle.dutyIndex = 0;
        break;
      case 0x400c:
        this.noise.volumeOrDecay = v & 0x0f;
        this.noise.constantVolume = (v & 0x10) !== 0;
        this.noise.halt = (v & 0x20) !== 0;
        this.noise.envelopeStart = true;
        break;
      case 0x400e:
        this.noise.modeFlag = (v & 0x80) !== 0;
        this.noise.timerPeriod = NOISE_PERIODS_NTSC[v & 0x0f];
        break;
      case 0x400f:
        if (this.status & 0x08) {
          this.noise.lengthCounter = LENGTH_TABLE[v >> 3];
        }
        this.noise.envelopeStart = true;
        break;
      case 0x4015: {
        this.status = v & 0x1f;
        if (!(v & 0x01)) this.pulse1.lengthCounter = 0;
        if (!(v & 0x02)) this.pulse2.lengthCounter = 0;
        if (!(v & 0x04)) this.triangle.lengthCounter = 0;
        if (!(v & 0x08)) this.noise.lengthCounter = 0;
        break;
      }
      case 0x4017:
        this.frameCounterMode = (v >> 7) & 1;
        this.irqInhibit = (v & 0x40) !== 0;
        this.frameCycle = 0;
        this.frameStep = 0;
        if (this.frameCounterMode === 1) {
          clockQuarterFrame(this);
          clockHalfFrame(this);
        }
        break;
      default:
        break;
    }
  }

  /**
   * Read $4015 status (length counters non-zero flags).
   * @returns {number}
   */
  readStatus() {
    let result = 0;
    if (this.pulse1.lengthCounter > 0) result |= 0x01;
    if (this.pulse2.lengthCounter > 0) result |= 0x02;
    if (this.triangle.lengthCounter > 0) result |= 0x04;
    if (this.noise.lengthCounter > 0) result |= 0x08;
    return result;
  }

  /**
   * Advance the APU by a number of CPU cycles and return one mixed sample
   * in roughly [-1, 1] (nonlinear mixer, peak-normalized lightly).
   *
   * @param {number} cpuCycles
   * @returns {number}
   */
  clock(cpuCycles) {
    const cycles = Math.max(0, cpuCycles | 0);
    for (let i = 0; i < cycles; i += 1) {
      // Triangle clocks every CPU cycle; pulse/noise every other.
      clockTriangleTimer(this.triangle);
      if ((i & 1) === 0) {
        clockPulseTimer(this.pulse1);
        clockPulseTimer(this.pulse2);
        clockNoiseTimer(this.noise);
      }
      this.frameCycle += 1;
      // NTSC 4-step: 7457, 14913, 22371, 29829 CPU cycles (approx).
      const stepCycles = FRAME_STEP_CYCLES[this.frameCounterMode];
      if (this.frameCycle >= stepCycles[this.frameStep]) {
        this.#clockFrameStep();
      }
    }
    return mixSample(this.pulse1, this.pulse2, this.triangle, this.noise);
  }

  /**
   * Render `count` mono samples at `sampleRate` into `out` (Float32Array).
   * @param {Float32Array} out
   * @param {number} sampleRate
   * @param {number} [count=out.length]
   */
  render(out, sampleRate, count = out.length) {
    const cyclesPerSample = this.cpuClock / sampleRate;
    let residual = this.sampleAccumulator;
    for (let i = 0; i < count; i += 1) {
      residual += cyclesPerSample;
      const whole = residual | 0;
      residual -= whole;
      out[i] = this.clock(whole);
    }
    this.sampleAccumulator = residual;
  }

  #clockFrameStep() {
    const mode = this.frameCounterMode;
    const step = this.frameStep;
    if (mode === 0) {
      // 4-step
      if (step === 0 || step === 2) clockQuarterFrame(this);
      if (step === 1 || step === 3) {
        clockQuarterFrame(this);
        clockHalfFrame(this);
      }
      this.frameStep = (step + 1) & 3;
      if (this.frameStep === 0) this.frameCycle = 0;
    } else {
      // 5-step
      if (step === 0 || step === 2) clockQuarterFrame(this);
      if (step === 1 || step === 4) {
        clockQuarterFrame(this);
        clockHalfFrame(this);
      }
      this.frameStep = step + 1;
      if (this.frameStep >= 5) {
        this.frameStep = 0;
        this.frameCycle = 0;
      }
    }
  }
}

/** NTSC frame sequencer boundaries in CPU cycles (from reset / $4017 write). */
const FRAME_STEP_CYCLES = [
  [7457, 14913, 22371, 29829],
  [7457, 14913, 22371, 29829, 37281],
];

function createPulse() {
  return {
    duty: 0,
    dutyIndex: 0,
    timer: 0,
    timerPeriod: 0,
    lengthCounter: 0,
    halt: false,
    constantVolume: true,
    volumeOrDecay: 0,
    envelopeStart: false,
    envelopeValue: 0,
    envelopeCounter: 0,
    sweepEnabled: false,
    sweepPeriod: 0,
    sweepNegate: false,
    sweepShift: 0,
    sweepReload: false,
    sweepCounter: 0,
    targetPeriod: 0,
  };
}

function createTriangle() {
  return {
    timer: 0,
    timerPeriod: 0,
    lengthCounter: 0,
    linearCounter: 0,
    linearReload: 0,
    linearReloadFlag: false,
    controlFlag: false,
    halt: false,
    dutyIndex: 0,
  };
}

function createNoise() {
  return {
    timer: 0,
    timerPeriod: NOISE_PERIODS_NTSC[0],
    lengthCounter: 0,
    halt: false,
    constantVolume: true,
    volumeOrDecay: 0,
    envelopeStart: false,
    envelopeValue: 0,
    envelopeCounter: 0,
    modeFlag: false,
    shiftRegister: 1,
  };
}

function writePulseControl(ch, v) {
  ch.duty = (v >> 6) & 0x03;
  ch.halt = (v & 0x20) !== 0;
  ch.constantVolume = (v & 0x10) !== 0;
  ch.volumeOrDecay = v & 0x0f;
  ch.envelopeStart = true;
}

function writePulseSweep(ch, v) {
  ch.sweepEnabled = (v & 0x80) !== 0;
  ch.sweepPeriod = (v >> 4) & 0x07;
  ch.sweepNegate = (v & 0x08) !== 0;
  ch.sweepShift = v & 0x07;
  ch.sweepReload = true;
}

function writePulseLength(ch, v, enabled) {
  ch.timerPeriod = (ch.timerPeriod & 0xff) | ((v & 0x07) << 8);
  if (enabled) ch.lengthCounter = LENGTH_TABLE[v >> 3];
  ch.dutyIndex = 0;
  ch.envelopeStart = true;
}

function clockPulseTimer(ch) {
  if (ch.timer === 0) {
    ch.timer = ch.timerPeriod;
    ch.dutyIndex = (ch.dutyIndex + 1) & 7;
  } else {
    ch.timer -= 1;
  }
}

function clockTriangleTimer(ch) {
  if (ch.timer === 0) {
    ch.timer = ch.timerPeriod;
    if (ch.lengthCounter > 0 && ch.linearCounter > 0) {
      ch.dutyIndex = (ch.dutyIndex + 1) & 31;
    }
  } else {
    ch.timer -= 1;
  }
}

function clockNoiseTimer(ch) {
  if (ch.timer === 0) {
    ch.timer = ch.timerPeriod;
    const bit0 = ch.shiftRegister & 1;
    const other = ch.modeFlag
      ? (ch.shiftRegister >> 6) & 1
      : (ch.shiftRegister >> 1) & 1;
    const feedback = bit0 ^ other;
    ch.shiftRegister >>= 1;
    ch.shiftRegister |= feedback << 14;
  } else {
    ch.timer -= 1;
  }
}

function clockQuarterFrame(apu) {
  clockEnvelope(apu.pulse1);
  clockEnvelope(apu.pulse2);
  clockEnvelope(apu.noise);
  clockTriangleLinear(apu.triangle);
}

function clockHalfFrame(apu) {
  clockLength(apu.pulse1);
  clockLength(apu.pulse2);
  clockLength(apu.triangle);
  clockLength(apu.noise);
  clockSweep(apu.pulse1, true);
  clockSweep(apu.pulse2, false);
}

function clockEnvelope(ch) {
  if (ch.envelopeStart) {
    ch.envelopeStart = false;
    ch.envelopeValue = 15;
    ch.envelopeCounter = ch.volumeOrDecay;
    return;
  }
  if (ch.envelopeCounter > 0) {
    ch.envelopeCounter -= 1;
    return;
  }
  ch.envelopeCounter = ch.volumeOrDecay;
  if (ch.envelopeValue > 0) {
    ch.envelopeValue -= 1;
  } else if (ch.halt) {
    ch.envelopeValue = 15;
  }
}

function clockTriangleLinear(ch) {
  if (ch.linearReloadFlag) {
    ch.linearCounter = ch.linearReload;
  } else if (ch.linearCounter > 0) {
    ch.linearCounter -= 1;
  }
  if (!ch.controlFlag) ch.linearReloadFlag = false;
}

function clockLength(ch) {
  if (!ch.halt && ch.lengthCounter > 0) ch.lengthCounter -= 1;
}

function clockSweep(ch, onesComplement) {
  const target = sweepTarget(ch, onesComplement);
  ch.targetPeriod = target;
  const mute = ch.timerPeriod < 8 || target > 0x7ff;
  if (ch.sweepCounter === 0 && ch.sweepEnabled && ch.sweepShift > 0 && !mute) {
    ch.timerPeriod = target & 0x7ff;
  }
  if (ch.sweepCounter === 0 || ch.sweepReload) {
    ch.sweepCounter = ch.sweepPeriod;
    ch.sweepReload = false;
  } else {
    ch.sweepCounter -= 1;
  }
}

function sweepTarget(ch, onesComplement) {
  const change = ch.timerPeriod >> ch.sweepShift;
  if (ch.sweepNegate) {
    return ch.timerPeriod - change - (onesComplement ? 1 : 0);
  }
  return ch.timerPeriod + change;
}

function pulseOutput(ch) {
  if (ch.lengthCounter === 0) return 0;
  if (ch.timerPeriod < 8) return 0;
  const target = ch.targetPeriod;
  if (ch.sweepEnabled && ch.sweepShift > 0 && target > 0x7ff) return 0;
  if (!DUTY_SEQUENCES[ch.duty][ch.dutyIndex]) return 0;
  return ch.constantVolume ? ch.volumeOrDecay : ch.envelopeValue;
}

function triangleOutput(ch) {
  if (ch.lengthCounter === 0 || ch.linearCounter === 0) return 0;
  // Ultrasonic periods are nearly silent / alias badly — mute like many emulators.
  if (ch.timerPeriod < 2) return 0;
  return TRIANGLE_SEQUENCE[ch.dutyIndex];
}

function noiseOutput(ch) {
  if (ch.lengthCounter === 0) return 0;
  if (ch.shiftRegister & 1) return 0;
  return ch.constantVolume ? ch.volumeOrDecay : ch.envelopeValue;
}

/**
 * Nonlinear NES mixer → roughly [-0.8, 0.8] mono float.
 * @param {ReturnType<typeof createPulse>} p1
 * @param {ReturnType<typeof createPulse>} p2
 * @param {ReturnType<typeof createTriangle>} tri
 * @param {ReturnType<typeof createNoise>} noise
 */
export function mixSample(p1, p2, tri, noise) {
  const pulse1 = pulseOutput(p1);
  const pulse2 = pulseOutput(p2);
  const triangle = triangleOutput(tri);
  const n = noiseOutput(noise);
  const dmc = 0;

  let pulseOut = 0;
  const pulseSum = pulse1 + pulse2;
  if (pulseSum > 0) {
    pulseOut = 95.88 / (8128 / pulseSum + 100);
  }

  let tndOut = 0;
  const tnd =
    triangle / 8227 + n / 12241 + dmc / 22638;
  if (tnd > 0) {
    tndOut = 159.79 / (1 / tnd + 100);
  }

  // Nonlinear mix is ~0..1 unipolar. Return 0 when idle so silence is true zero.
  return (pulseOut + tndOut) * 1.5;
}

/**
 * Convenience: enable all tone channels with length counters free-running.
 * @param {NesApu} apu
 */
export function enableToneChannels(apu) {
  apu.writeRegister(0x4015, 0x0f);
  // 5-step mode, IRQ inhibit — common for music engines.
  apu.writeRegister(0x4017, 0xc0);
}

/**
 * Gate helpers used by the sequencer (constant volume, halt length = sustain).
 * @param {NesApu} apu
 * @param {"pulse1"|"pulse2"} channel
 * @param {{ duty: number, volume: number, period: number }} params
 */
export function startPulseNote(apu, channel, { duty, volume, period }) {
  const base = channel === "pulse1" ? 0x4000 : 0x4004;
  const d = duty & 3;
  const vol = volume & 0x0f;
  // duty | halt(length) | constant volume | volume
  apu.writeRegister(base, (d << 6) | 0x30 | vol);
  // disable sweep (negate on so target never overflows)
  apu.writeRegister(base + 1, 0x08);
  apu.writeRegister(base + 2, period & 0xff);
  // length load index 00001 (long), period high
  apu.writeRegister(base + 3, 0x08 | ((period >> 8) & 0x07));
}

/**
 * @param {NesApu} apu
 * @param {"pulse1"|"pulse2"} channel
 */
export function stopPulseNote(apu, channel) {
  const base = channel === "pulse1" ? 0x4000 : 0x4004;
  apu.writeRegister(base, 0x30); // constant vol 0, halt
  if (channel === "pulse1") {
    apu.pulse1.lengthCounter = 0;
  } else {
    apu.pulse2.lengthCounter = 0;
  }
}

/**
 * @param {NesApu} apu
 * @param {{ period: number }} params
 */
export function startTriangleNote(apu, { period }) {
  // control flag set, linear counter reload = 0x7F (hold)
  apu.writeRegister(0x4008, 0xff);
  apu.writeRegister(0x400a, period & 0xff);
  apu.writeRegister(0x400b, 0x08 | ((period >> 8) & 0x07));
}

/**
 * @param {NesApu} apu
 */
export function stopTriangleNote(apu) {
  apu.writeRegister(0x4008, 0x80); // control on, reload 0
  apu.triangle.linearCounter = 0;
  apu.triangle.lengthCounter = 0;
}

/**
 * @param {NesApu} apu
 * @param {{ volume: number, periodIndex: number, shortMode?: boolean }} params
 */
export function startNoiseNote(
  apu,
  { volume, periodIndex, shortMode = false },
) {
  const vol = volume & 0x0f;
  apu.writeRegister(0x400c, 0x30 | vol);
  apu.writeRegister(
    0x400e,
    (shortMode ? 0x80 : 0) | (periodIndex & 0x0f),
  );
  apu.writeRegister(0x400f, 0x08);
}

/**
 * @param {NesApu} apu
 */
export function stopNoiseNote(apu) {
  apu.writeRegister(0x400c, 0x30);
  apu.noise.lengthCounter = 0;
}
