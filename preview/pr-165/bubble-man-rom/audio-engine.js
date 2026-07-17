import { BPM, TICKS_PER_BEAT, pitchToMidi } from "./music-data.js";

const tickSeconds = 60 / BPM / TICKS_PER_BEAT;

export function createAudioContext(scope = globalThis) {
  const AudioContextConstructor = scope.AudioContext ?? scope.webkitAudioContext;
  if (!AudioContextConstructor) {
    throw new Error("Web Audio is not supported by this browser.");
  }
  return new AudioContextConstructor();
}

export function configureAudioSession(navigatorObject = globalThis.navigator) {
  try {
    if (navigatorObject?.audioSession) {
      navigatorObject.audioSession.type = "playback";
    }
  } catch {
    // Older WebKit builds may expose a read-only or partially implemented API.
  }
}

export async function unlockAudioContext(context) {
  // iOS requires a source to be started synchronously inside the user gesture.
  // Starting a one-sample silent buffer before awaiting resume satisfies that
  // requirement without producing a click.
  const source = context.createBufferSource();
  source.buffer = context.createBuffer(1, 1, context.sampleRate);
  source.connect(context.destination);
  source.start(0);

  if (context.state !== "running") {
    await context.resume();
  }
  if (context.state !== "running") {
    throw new Error(`Audio output is ${context.state}; tap Play again to enable it.`);
  }
}

function pulseWave(context, duty) {
  const harmonics = 48;
  const real = new Float32Array(harmonics);
  const imag = new Float32Array(harmonics);

  for (let n = 1; n < harmonics; n += 1) {
    real[n] = (2 * Math.sin(Math.PI * n * duty) * Math.cos(Math.PI * n * duty)) / (Math.PI * n);
    imag[n] = (2 * Math.sin(Math.PI * n * duty) * Math.sin(Math.PI * n * duty)) / (Math.PI * n);
  }

  return context.createPeriodicWave(real, imag, { disableNormalization: false });
}

function frequencyForPitch(pitch) {
  const midi = pitchToMidi(pitch);
  return midi === null ? null : 440 * 2 ** ((midi - 69) / 12);
}

function scheduleTone(context, output, channel, event, sectionStart) {
  if (!event.pitch) return;
  const startsAt = sectionStart + event.start * tickSeconds;
  const duration = Math.max(0.025, event.duration * tickSeconds);
  const endsAt = startsAt + duration;

  if (channel.wave === "noise") {
    const frames = Math.ceil(context.sampleRate * Math.min(duration, 0.09));
    const buffer = context.createBuffer(1, frames, context.sampleRate);
    const samples = buffer.getChannelData(0);
    let value = 0x4a35;
    for (let index = 0; index < frames; index += 1) {
      const bit = ((value >> 0) ^ (value >> 1)) & 1;
      value = (value >> 1) | (bit << 14);
      samples[index] = (value & 1) * 2 - 1;
    }

    const source = context.createBufferSource();
    const gain = context.createGain();
    const filter = context.createBiquadFilter();
    filter.type = "highpass";
    filter.frequency.value = 1600;
    gain.gain.setValueAtTime(channel.gain, startsAt);
    gain.gain.exponentialRampToValueAtTime(0.001, startsAt + Math.min(duration, 0.08));
    source.buffer = buffer;
    source.connect(filter).connect(gain).connect(output);
    source.start(startsAt);
    source.stop(startsAt + Math.min(duration, 0.1));
    return;
  }

  const oscillator = context.createOscillator();
  const gain = context.createGain();
  oscillator.frequency.setValueAtTime(frequencyForPitch(event.pitch), startsAt);

  if (channel.wave === "pulse") {
    oscillator.setPeriodicWave(pulseWave(context, channel.duty ?? 0.5));
  } else {
    oscillator.type = "triangle";
  }

  const attack = channel.wave === "triangle" ? 0.006 : 0.003;
  const release = Math.min(0.028, duration * 0.18);
  gain.gain.setValueAtTime(0.0001, startsAt);
  gain.gain.exponentialRampToValueAtTime(channel.gain, startsAt + attack);
  gain.gain.setValueAtTime(channel.gain, Math.max(startsAt + attack, endsAt - release));
  gain.gain.exponentialRampToValueAtTime(0.0001, endsAt);

  oscillator.connect(gain).connect(output);
  oscillator.start(startsAt);
  oscillator.stop(endsAt + 0.01);
}

export class SectionPlayer {
  constructor({ onFrame, onStop }) {
    this.context = null;
    this.onFrame = onFrame;
    this.onStop = onStop;
    this.animationFrame = null;
    this.stopTimer = null;
    this.playing = false;
  }

  async play(section, mutedChannels = new Set()) {
    this.stop(false);
    configureAudioSession();
    this.context ??= createAudioContext();
    await unlockAudioContext(this.context);

    const master = this.context.createGain();
    const compressor = this.context.createDynamicsCompressor();
    const analyser = this.context.createAnalyser();
    const channelBuses = new Map();
    const waveform = new Float32Array(256);
    master.gain.value = 0.72;
    compressor.threshold.value = -16;
    compressor.knee.value = 12;
    compressor.ratio.value = 5;
    analyser.fftSize = 256;
    analyser.smoothingTimeConstant = 0.35;
    master.connect(compressor).connect(analyser).connect(this.context.destination);

    const sectionStart = this.context.currentTime + 0.055;
    const duration = section.durationTicks * tickSeconds;
    section.channels.forEach((channel) => {
      const bus = this.context.createGain();
      bus.gain.value = mutedChannels.has(channel.id) ? 0 : 1;
      bus.connect(master);
      channelBuses.set(channel.id, bus);
      channel.events.forEach((event) =>
        scheduleTone(this.context, bus, channel, event, sectionStart),
      );
    });

    this.playing = true;
    this.activeOutput = master;
    this.analyser = analyser;
    this.waveform = waveform;
    this.channelBuses = channelBuses;
    this.startedAt = sectionStart;
    this.duration = duration;
    this.section = section;

    const draw = () => {
      if (!this.playing) return;
      const elapsed = Math.max(0, this.context.currentTime - this.startedAt);
      const progress = Math.min(1, elapsed / this.duration);
      this.analyser.getFloatTimeDomainData(this.waveform);
      const sumOfSquares = this.waveform.reduce((sum, sample) => sum + sample * sample, 0);
      const audioLevel = Math.sqrt(sumOfSquares / this.waveform.length);
      this.onFrame?.({ elapsed, progress, tick: elapsed / tickSeconds, audioLevel });
      if (progress < 1) this.animationFrame = requestAnimationFrame(draw);
    };
    this.animationFrame = requestAnimationFrame(draw);
    this.stopTimer = window.setTimeout(() => this.stop(), (duration + 0.12) * 1000);
  }

  stop(notify = true) {
    if (this.animationFrame) cancelAnimationFrame(this.animationFrame);
    if (this.stopTimer) clearTimeout(this.stopTimer);
    this.activeOutput?.gain.cancelScheduledValues(0);
    this.activeOutput?.gain.setTargetAtTime(0.0001, this.context?.currentTime ?? 0, 0.012);
    const wasPlaying = this.playing;
    this.playing = false;
    this.animationFrame = null;
    this.stopTimer = null;
    if (wasPlaying && notify) this.onStop?.();
  }

  setMuted(channelId, muted) {
    const bus = this.channelBuses?.get(channelId);
    if (!bus || !this.context) return;
    bus.gain.setTargetAtTime(muted ? 0 : 1, this.context.currentTime, 0.01);
  }
}

export { tickSeconds };
