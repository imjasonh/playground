// Audio engine for M1/M2: direct HRTF path with occlusion muffling, plus a
// bank of order-1 image-source reflection taps (delay → gain → lowpass → HRTF).

import { setListenerPose, setPannerPosition } from './audioPose.js';

const MAX_REFLECTIONS = 8;
const SPEED_OF_SOUND = 343;

export class HeliAudio {
  constructor() {
    const Ctx = window.AudioContext || window.webkitAudioContext;
    this.ctx = new Ctx();

    this.master = this.ctx.createGain();
    this.master.gain.value = 0;
    this.master.connect(this.ctx.destination);

    const splitter = this.ctx.createChannelSplitter(2);
    this.master.connect(splitter);
    this.leftAnalyser = this.ctx.createAnalyser();
    this.rightAnalyser = this.ctx.createAnalyser();
    this.leftAnalyser.fftSize = 2048;
    this.rightAnalyser.fftSize = 2048;
    splitter.connect(this.leftAnalyser, 0);
    splitter.connect(this.rightAnalyser, 1);
    this._leftBuf = new Float32Array(this.leftAnalyser.fftSize);
    this._rightBuf = new Float32Array(this.rightAnalyser.fftSize);

    // Direct path: synth → dryGain → occludeFilter → occludeGain → panner → master
    this.dryGain = this.ctx.createGain();
    this.dryGain.gain.value = 1;
    this.occludeFilter = this.ctx.createBiquadFilter();
    this.occludeFilter.type = 'lowpass';
    this.occludeFilter.frequency.value = 18000;
    this.occludeGain = this.ctx.createGain();
    this.occludeGain.gain.value = 1;
    this.panner = this.ctx.createPanner();
    this.panner.panningModel = 'HRTF';
    this.panner.distanceModel = 'inverse';
    this.panner.refDistance = 8;
    this.panner.rolloffFactor = 0.9;
    this.dryGain
      .connect(this.occludeFilter)
      .connect(this.occludeGain)
      .connect(this.panner)
      .connect(this.master);

    // Shared wet send into reflection taps.
    this.wetGain = this.ctx.createGain();
    this.wetGain.gain.value = 1;
    this.taps = [];
    for (let i = 0; i < MAX_REFLECTIONS; i++) {
      const delay = this.ctx.createDelay(1.5);
      delay.delayTime.value = 0.01;
      const gain = this.ctx.createGain();
      gain.gain.value = 0;
      const filter = this.ctx.createBiquadFilter();
      filter.type = 'lowpass';
      filter.frequency.value = 4000;
      const panner = this.ctx.createPanner();
      panner.panningModel = 'HRTF';
      panner.distanceModel = 'inverse';
      panner.refDistance = 8;
      panner.rolloffFactor = 0.9;
      // Delay already encodes path length, so kill the panner's extra distance
      // attenuation by using a huge refDistance... actually better: set
      // rolloffFactor 0 so position only steers HRTF direction.
      panner.rolloffFactor = 0;
      this.wetGain.connect(delay);
      delay.connect(gain).connect(filter).connect(panner).connect(this.master);
      this.taps.push({ delay, gain, filter, panner });
    }

    this.occlusionEnabled = true;
    this.reflectionsEnabled = true;
    this.#buildHelicopter();
  }

  #buildHelicopter() {
    const ctx = this.ctx;
    const source = ctx.createGain();
    // Fan out to dry and wet.
    source.connect(this.dryGain);
    source.connect(this.wetGain);

    const chopLfo = ctx.createOscillator();
    chopLfo.type = 'triangle';
    chopLfo.frequency.value = 12;
    const chopDepth = ctx.createGain();
    chopDepth.gain.value = 0.5;
    chopLfo.connect(chopDepth);

    const thump = ctx.createOscillator();
    thump.type = 'sawtooth';
    thump.frequency.value = 55;
    const thumpLow = ctx.createBiquadFilter();
    thumpLow.type = 'lowpass';
    thumpLow.frequency.value = 320;
    const thumpGain = ctx.createGain();
    thumpGain.gain.value = 0.28;
    const thumpChop = ctx.createGain();
    thumpChop.gain.value = 0.55;
    chopDepth.connect(thumpChop.gain);
    thump.connect(thumpLow).connect(thumpChop).connect(thumpGain).connect(source);

    const noiseBuf = ctx.createBuffer(1, ctx.sampleRate * 2, ctx.sampleRate);
    const data = noiseBuf.getChannelData(0);
    for (let i = 0; i < data.length; i++) data[i] = Math.random() * 2 - 1;
    const noise = ctx.createBufferSource();
    noise.buffer = noiseBuf;
    noise.loop = true;
    const washBand = ctx.createBiquadFilter();
    washBand.type = 'bandpass';
    washBand.frequency.value = 1400;
    washBand.Q.value = 0.7;
    const washGain = ctx.createGain();
    washGain.gain.value = 0.09;
    const washChop = ctx.createGain();
    washChop.gain.value = 0.7;
    chopDepth.connect(washChop.gain);
    noise.connect(washBand).connect(washChop).connect(washGain).connect(source);

    const turbine = ctx.createOscillator();
    turbine.type = 'sawtooth';
    turbine.frequency.value = 480;
    const turbine2 = ctx.createOscillator();
    turbine2.type = 'sawtooth';
    turbine2.frequency.value = 487;
    const turbineHi = ctx.createBiquadFilter();
    turbineHi.type = 'bandpass';
    turbineHi.frequency.value = 1600;
    turbineHi.Q.value = 1.2;
    const turbineGain = ctx.createGain();
    turbineGain.gain.value = 0.05;
    turbine.connect(turbineHi);
    turbine2.connect(turbineHi);
    turbineHi.connect(turbineGain).connect(source);

    chopLfo.start();
    thump.start();
    turbine.start();
    turbine2.start();
    noise.start();
  }

  async resume() {
    if (this.ctx.state === 'suspended') await this.ctx.resume();
  }

  fadeIn() {
    const t = this.ctx.currentTime;
    this.master.gain.cancelScheduledValues(t);
    this.master.gain.setValueAtTime(this.master.gain.value, t);
    this.master.gain.linearRampToValueAtTime(1, t + 0.4);
  }

  fadeOut() {
    const t = this.ctx.currentTime;
    this.master.gain.cancelScheduledValues(t);
    this.master.gain.setValueAtTime(this.master.gain.value, t);
    this.master.gain.linearRampToValueAtTime(0, t + 0.4);
  }

  setOcclusionEnabled(on) {
    this.occlusionEnabled = on;
  }

  setReflectionsEnabled(on) {
    this.reflectionsEnabled = on;
    if (!on) {
      const t = this.ctx.currentTime;
      for (const tap of this.taps) {
        tap.gain.gain.cancelScheduledValues(t);
        tap.gain.gain.setTargetAtTime(0, t, 0.05);
      }
    }
  }

  earLevels() {
    this.leftAnalyser.getFloatTimeDomainData(this._leftBuf);
    this.rightAnalyser.getFloatTimeDomainData(this._rightBuf);
    let l = 0;
    let r = 0;
    for (let i = 0; i < this._leftBuf.length; i++) {
      l += this._leftBuf[i] * this._leftBuf[i];
      r += this._rightBuf[i] * this._rightBuf[i];
    }
    const left = Math.sqrt(l / this._leftBuf.length);
    const right = Math.sqrt(r / this._rightBuf.length);
    const total = left + right;
    return {
      left,
      right,
      balance: total === 0 ? 0 : (right - left) / total,
      contextState: this.ctx.state,
    };
  }

  /**
   * @param {number[]} sourcePos
   * @param {number[]} listenerPos
   * @param {number[]} forward
   * @param {number[]} up
   * @param {{ occlusion: number, reflections: Array<{delaySec:number,gain:number,image:number[],hit:number[]}> }} acoustics
   */
  update(sourcePos, listenerPos, forward, up, acoustics = { occlusion: 0, reflections: [] }) {
    const t = this.ctx.currentTime;
    const ramp = 0.05;
    setPannerPosition(this.panner, sourcePos, t);
    setListenerPose(this.ctx.listener, listenerPos, forward, up, t);

    const occ = this.occlusionEnabled ? acoustics.occlusion : 0;
    // Fully occluded: drop ~18 dB and cut to ~700 Hz. Clear: flat and full.
    const dry = 1 - 0.85 * occ;
    const cutoff = 18000 - 17300 * occ;
    this.occludeGain.gain.setTargetAtTime(dry, t, ramp);
    this.occludeFilter.frequency.setTargetAtTime(cutoff, t, ramp);

    const refs = this.reflectionsEnabled ? acoustics.reflections : [];
    for (let i = 0; i < this.taps.length; i++) {
      const tap = this.taps[i];
      const r = refs[i];
      if (!r) {
        tap.gain.gain.setTargetAtTime(0, t, ramp);
        continue;
      }
      // Delay already has the full path; keep a tiny floor so DelayNode is happy.
      const delay = Math.min(1.45, Math.max(0.001, r.delaySec));
      tap.delay.delayTime.setTargetAtTime(delay, t, ramp);
      // Scale image-source gain into a audible but non-dominating wet level.
      const g = Math.min(0.55, r.gain * 18);
      tap.gain.gain.setTargetAtTime(g, t, ramp);
      // Darker for longer paths.
      const freq = Math.max(800, 6000 - r.pathLength * 25);
      tap.filter.frequency.setTargetAtTime(freq, t, ramp);
      // Spatialize from the image location so the reflection arrives from the
      // bounce direction (classic image-source trick).
      setPannerPosition(tap.panner, r.image, t);
    }
  }
}

// Re-export for tests that only care about the constant.
export { MAX_REFLECTIONS, SPEED_OF_SOUND };
