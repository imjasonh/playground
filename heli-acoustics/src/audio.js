// Audio engine: direct HRTF with occlusion, order-1/2 image-source taps, and
// enclosure-driven late reverb (ConvolverNode).

import { setListenerPose, setPannerPosition } from './audioPose.js';
import { buildImpulseResponse, irParamsForEnclosure } from './impulseResponse.js';

const MAX_REFLECTIONS = 12;
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
      // Delay already encodes path length; position only steers HRTF direction.
      panner.rolloffFactor = 0;
      this.wetGain.connect(delay);
      delay.connect(gain).connect(filter).connect(panner).connect(this.master);
      this.taps.push({ delay, gain, filter, panner });
    }

    // Late reverb: diffuse ConvolverNode driven by enclosure (no HRTF).
    this.reverbSend = this.ctx.createGain();
    this.reverbSend.gain.value = 0;
    this.reverbFilter = this.ctx.createBiquadFilter();
    this.reverbFilter.type = 'lowpass';
    this.reverbFilter.frequency.value = 5000;
    this.convolver = this.ctx.createConvolver();
    this.convolver.normalize = true;
    this.reverbOut = this.ctx.createGain();
    this.reverbOut.gain.value = 0.55;
    this.reverbSend
      .connect(this.reverbFilter)
      .connect(this.convolver)
      .connect(this.reverbOut)
      .connect(this.master);
    this._lastIrAmount = -1;
    this.#setImpulseForEnclosure(0.35);

    this.occlusionEnabled = true;
    this.reflectionsEnabled = true;
    this.reverbEnabled = true;
    this.#buildHelicopter();
  }

  #setImpulseForEnclosure(amount) {
    // Rebuild only when enclosure moves enough; IR generation is cheap but
    // swapping every frame still costs.
    if (Math.abs(amount - this._lastIrAmount) < 0.08 && this._lastIrAmount >= 0) return;
    this._lastIrAmount = amount;
    const params = irParamsForEnclosure(amount);
    this.convolver.buffer = buildImpulseResponse(this.ctx, params);
  }

  #buildHelicopter() {
    const ctx = this.ctx;
    const source = ctx.createGain();
    // Fan out to dry, early wet, and late reverb.
    source.connect(this.dryGain);
    source.connect(this.wetGain);
    source.connect(this.reverbSend);

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

  setReverbEnabled(on) {
    this.reverbEnabled = on;
    if (!on) {
      const t = this.ctx.currentTime;
      this.reverbSend.gain.cancelScheduledValues(t);
      this.reverbSend.gain.setTargetAtTime(0, t, 0.08);
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
   * @param {{ occlusion: number, reflections: Array, enclosure?: { amount: number, rt60Sec: number } }} acoustics
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
      const delay = Math.min(1.45, Math.max(0.001, r.delaySec));
      tap.delay.delayTime.setTargetAtTime(delay, t, ramp);
      // Order-2 is weaker already via reflectivity product; keep a shared scale.
      const g = Math.min(0.55, r.gain * 18);
      tap.gain.gain.setTargetAtTime(g, t, ramp);
      const freq = Math.max(700, 6000 - r.pathLength * 25 - (r.order > 1 ? 800 : 0));
      tap.filter.frequency.setTargetAtTime(freq, t, ramp);
      setPannerPosition(tap.panner, r.image, t);
    }

    const enc = acoustics.enclosure?.amount ?? 0;
    if (this.reverbEnabled) {
      this.#setImpulseForEnclosure(enc);
      // Late send rises with enclosure; keep it under the early taps but
      // loud enough to hear (and to pass the reverb A/B probe).
      const send = 0.06 + enc * 0.38;
      this.reverbSend.gain.setTargetAtTime(send, t, 0.1);
      const dampHz = 6500 - enc * 2800;
      this.reverbFilter.frequency.setTargetAtTime(dampHz, t, 0.1);
    }
  }
}

export { MAX_REFLECTIONS, SPEED_OF_SOUND };
