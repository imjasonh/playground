const RPM_SPOOL_UP = 2.5;
const RPM_SPOOL_DOWN = 1.8;
const RPM_CUT_DECAY = 0.8;
class DroneAudio {
  ctx;
  master;
  // Motor oscillators
  osc1;
  osc2;
  osc3;
  motorGain1;
  motorGain2;
  motorGain3;
  // Wind noise
  windGain;
  muted = false;
  rpm = 0;
  // 0..1 normalized motor RPM
  lastTime = 0;
  constructor() {
    this.ctx = new AudioContext();
    this.master = this.ctx.createGain();
    this.master.gain.value = 0;
    this.master.connect(this.ctx.destination);
    this.osc1 = this.ctx.createOscillator();
    this.osc1.type = "sawtooth";
    this.osc1.frequency.value = 200;
    this.motorGain1 = this.ctx.createGain();
    this.motorGain1.gain.value = 0;
    this.osc1.connect(this.motorGain1);
    this.motorGain1.connect(this.master);
    this.osc2 = this.ctx.createOscillator();
    this.osc2.type = "sawtooth";
    this.osc2.frequency.value = 200;
    this.motorGain2 = this.ctx.createGain();
    this.motorGain2.gain.value = 0;
    this.osc2.connect(this.motorGain2);
    this.motorGain2.connect(this.master);
    this.osc3 = this.ctx.createOscillator();
    this.osc3.type = "square";
    this.osc3.frequency.value = 200;
    this.motorGain3 = this.ctx.createGain();
    this.motorGain3.gain.value = 0;
    this.osc3.connect(this.motorGain3);
    this.motorGain3.connect(this.master);
    const bufferSize = this.ctx.sampleRate * 2;
    const noiseBuffer = this.ctx.createBuffer(1, bufferSize, this.ctx.sampleRate);
    const data = noiseBuffer.getChannelData(0);
    for (let i = 0; i < bufferSize; i++) {
      data[i] = Math.random() * 2 - 1;
    }
    const noise = this.ctx.createBufferSource();
    noise.buffer = noiseBuffer;
    noise.loop = true;
    const bandpass = this.ctx.createBiquadFilter();
    bandpass.type = "bandpass";
    bandpass.frequency.value = 2500;
    bandpass.Q.value = 0.6;
    this.windGain = this.ctx.createGain();
    this.windGain.gain.value = 0;
    noise.connect(bandpass);
    bandpass.connect(this.windGain);
    this.windGain.connect(this.master);
    this.osc1.start();
    this.osc2.start();
    this.osc3.start();
    noise.start();
    this.lastTime = this.ctx.currentTime;
  }
  async resume() {
    if (this.ctx.state === "suspended") {
      await this.ctx.resume();
    }
    this.lastTime = this.ctx.currentTime;
  }
  update(audioState) {
    const now = this.ctx.currentTime;
    const dt = Math.min(now - this.lastTime, 0.05);
    this.lastTime = now;
    let targetRpm;
    let spoolRate;
    switch (audioState.throttle) {
      case "full":
        targetRpm = 1;
        spoolRate = RPM_SPOOL_UP;
        break;
      case "idle":
        targetRpm = 0.45;
        spoolRate = this.rpm > 0.45 ? RPM_SPOOL_DOWN : RPM_SPOOL_UP;
        break;
      case "cut":
        targetRpm = 0;
        spoolRate = RPM_CUT_DECAY;
        break;
    }
    const diff = targetRpm - this.rpm;
    this.rpm += diff * spoolRate * dt;
    if (Math.abs(this.rpm - targetRpm) < 1e-3) this.rpm = targetRpm;
    const freq = 200 + this.rpm * 700;
    const ramp = 0.04;
    this.osc1.frequency.linearRampToValueAtTime(freq, now + ramp);
    this.osc2.frequency.linearRampToValueAtTime(freq * 1.07, now + ramp);
    this.osc3.frequency.linearRampToValueAtTime(freq * 0.5, now + ramp);
    const motorVol = this.rpm * 0.12;
    this.motorGain1.gain.linearRampToValueAtTime(motorVol, now + ramp);
    this.motorGain2.gain.linearRampToValueAtTime(motorVol * 0.5, now + ramp);
    this.motorGain3.gain.linearRampToValueAtTime(motorVol * 0.3, now + ramp);
    const windTarget = Math.min(audioState.speed / 30, 1) * 0.1;
    this.windGain.gain.linearRampToValueAtTime(windTarget, now + 0.15);
  }
  fadeIn() {
    if (this.muted) return;
    this.rpm = 0;
    const t = this.ctx.currentTime;
    this.master.gain.linearRampToValueAtTime(1, t + 0.1);
  }
  fadeOut() {
    const t = this.ctx.currentTime;
    this.master.gain.linearRampToValueAtTime(0, t + 0.5);
  }
  setMuted(muted) {
    this.muted = muted;
    const t = this.ctx.currentTime;
    this.master.gain.linearRampToValueAtTime(muted ? 0 : 1, t + 0.05);
  }
  isMuted() {
    return this.muted;
  }
}
export {
  DroneAudio
};
