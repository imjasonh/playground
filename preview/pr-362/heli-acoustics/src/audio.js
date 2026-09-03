// M0 audio engine: one synthesized helicopter routed through an HRTF PannerNode
// so direct sound is truly binaural. No reflections yet — that is M2. Geometry
// (orbit position, listener basis) comes from geometry.js; this module only
// wires those numbers into the Web Audio graph.

// Some engines still expose only the deprecated setPosition/setOrientation
// methods; newer ones use k-rate AudioParams. Prefer the params, fall back.
function setListenerPose(listener, pos, forward, up, when) {
  if (listener.positionX) {
    listener.positionX.setValueAtTime(pos[0], when);
    listener.positionY.setValueAtTime(pos[1], when);
    listener.positionZ.setValueAtTime(pos[2], when);
    listener.forwardX.setValueAtTime(forward[0], when);
    listener.forwardY.setValueAtTime(forward[1], when);
    listener.forwardZ.setValueAtTime(forward[2], when);
    listener.upX.setValueAtTime(up[0], when);
    listener.upY.setValueAtTime(up[1], when);
    listener.upZ.setValueAtTime(up[2], when);
  } else {
    listener.setPosition(pos[0], pos[1], pos[2]);
    listener.setOrientation(forward[0], forward[1], forward[2], up[0], up[1], up[2]);
  }
}

function setPannerPosition(panner, pos, when) {
  if (panner.positionX) {
    panner.positionX.setValueAtTime(pos[0], when);
    panner.positionY.setValueAtTime(pos[1], when);
    panner.positionZ.setValueAtTime(pos[2], when);
  } else {
    panner.setPosition(pos[0], pos[1], pos[2]);
  }
}

export class HeliAudio {
  constructor() {
    const Ctx = window.AudioContext || window.webkitAudioContext;
    this.ctx = new Ctx();

    this.master = this.ctx.createGain();
    this.master.gain.value = 0;
    this.master.connect(this.ctx.destination);

    // Tap the stereo output so the HUD can show measured left/right ear energy.
    // This is the live proof that HRTF is producing an asymmetric signal, not
    // just that a panner node exists in the graph.
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

    // HRTF panner: this is what makes left/right/front/back audible in
    // headphones. refDistance/rolloff give a plausible urban falloff.
    this.panner = this.ctx.createPanner();
    this.panner.panningModel = 'HRTF';
    this.panner.distanceModel = 'inverse';
    this.panner.refDistance = 8;
    this.panner.rolloffFactor = 0.9;
    this.panner.connect(this.master);

    this.#buildHelicopter();
  }

  // Measured RMS on each ear after the HRTF panner. Negative balance means
  // louder left; positive means louder right. See meter.js.
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

  // A helicopter is dominated by three layers: a low blade-slap "chop" that
  // pulses a few times a second, a broadband rotor-wash hiss, and a turbine
  // whine an octave-plus above. We amplitude-modulate the first two with a
  // shared low-frequency oscillator to get the signature thwop-thwop.
  #buildHelicopter() {
    const ctx = this.ctx;
    const source = ctx.createGain();
    source.connect(this.panner);

    // Blade-pass modulator (~12 Hz): drives a chop gain around a small DC bias
    // so the rotor never fully cuts out.
    const chopLfo = ctx.createOscillator();
    chopLfo.type = 'triangle';
    chopLfo.frequency.value = 12;
    const chopDepth = ctx.createGain();
    chopDepth.gain.value = 0.5;
    chopLfo.connect(chopDepth);

    // Low thump: filtered sawtooth carrying the chop.
    const thump = ctx.createOscillator();
    thump.type = 'sawtooth';
    thump.frequency.value = 55;
    const thumpLow = ctx.createBiquadFilter();
    thumpLow.type = 'lowpass';
    thumpLow.frequency.value = 320;
    const thumpGain = ctx.createGain();
    thumpGain.gain.value = 0.28;
    const thumpChop = ctx.createGain();
    thumpChop.gain.value = 0.55; // DC bias; LFO rides on top
    chopDepth.connect(thumpChop.gain);
    thump.connect(thumpLow).connect(thumpChop).connect(thumpGain).connect(source);

    // Rotor wash: white noise, band-limited, also chopped.
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

    // Turbine whine: a couple of detuned tones for a metallic engine note.
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

    this.chopLfo = chopLfo;
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

  // sourcePos: [x,y,z] world position of the helicopter.
  // forward/up: listener basis vectors from geometry.forwardVector/upVector.
  update(sourcePos, forward, up) {
    const t = this.ctx.currentTime;
    setPannerPosition(this.panner, sourcePos, t);
    setListenerPose(this.ctx.listener, [0, 0, 0], forward, up, t);
  }
}
