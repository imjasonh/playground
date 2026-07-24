import { BPM, TICKS_PER_BEAT, pitchToMidi } from "./music-data.js";

const tickSeconds = 60 / BPM / TICKS_PER_BEAT;
const pulseWaveCache = new WeakMap();

export function playbackTickForElapsed(
  elapsedSeconds,
  durationTicks,
  loopStartTick,
) {
  const rawElapsedTicks = elapsedSeconds / tickSeconds;
  const nearestTick = Math.round(rawElapsedTicks);
  const elapsedTicks =
    Math.abs(rawElapsedTicks - nearestTick) < 1e-9
      ? nearestTick
      : rawElapsedTicks;
  if (!Number.isFinite(loopStartTick) || elapsedTicks < durationTicks) {
    return Math.min(durationTicks, elapsedTicks);
  }
  const loopDurationTicks = durationTicks - loopStartTick;
  return loopStartTick + ((elapsedTicks - durationTicks) % loopDurationTicks);
}

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
  let contextWaves = pulseWaveCache.get(context);
  if (!contextWaves) {
    contextWaves = new Map();
    pulseWaveCache.set(context, contextWaves);
  }
  if (contextWaves.has(duty)) return contextWaves.get(duty);

  const harmonics = 48;
  const real = new Float32Array(harmonics);
  const imag = new Float32Array(harmonics);

  for (let n = 1; n < harmonics; n += 1) {
    real[n] = (2 * Math.sin(Math.PI * n * duty) * Math.cos(Math.PI * n * duty)) / (Math.PI * n);
    imag[n] = (2 * Math.sin(Math.PI * n * duty) * Math.sin(Math.PI * n * duty)) / (Math.PI * n);
  }

  const wave = context.createPeriodicWave(real, imag, { disableNormalization: false });
  contextWaves.set(duty, wave);
  return wave;
}

export function frequencyForPitch(pitch, transpose = 0) {
  const midi = pitchToMidi(pitch);
  return midi === null ? null : 440 * 2 ** ((midi + transpose - 69) / 12);
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
    gain.gain.setValueAtTime(event.gain ?? channel.gain, startsAt);
    gain.gain.exponentialRampToValueAtTime(0.001, startsAt + Math.min(duration, 0.08));
    source.buffer = buffer;
    source.connect(filter).connect(gain).connect(output);
    source.start(startsAt);
    source.stop(startsAt + Math.min(duration, 0.1));
    return;
  }

  const oscillator = context.createOscillator();
  const gain = context.createGain();
  oscillator.frequency.setValueAtTime(
    frequencyForPitch(event.pitch, channel.transpose ?? 0),
    startsAt,
  );

  if (channel.wave === "pulse") {
    oscillator.setPeriodicWave(pulseWave(context, event.duty ?? channel.duty ?? 0.5));
  } else {
    oscillator.type = "triangle";
  }

  const attack = channel.wave === "triangle" ? 0.006 : 0.003;
  const release = Math.min(0.028, duration * 0.18);
  gain.gain.setValueAtTime(0.0001, startsAt);
  const eventGain = event.gain ?? channel.gain;
  gain.gain.exponentialRampToValueAtTime(eventGain, startsAt + attack);
  gain.gain.setValueAtTime(eventGain, Math.max(startsAt + attack, endsAt - release));
  gain.gain.exponentialRampToValueAtTime(0.0001, endsAt);

  oscillator.connect(gain).connect(output);
  if (event.vibrato) {
    const vibrato = context.createOscillator();
    const vibratoDepth = context.createGain();
    vibrato.frequency.value = 6;
    vibratoDepth.gain.value = 12;
    vibrato.connect(vibratoDepth).connect(oscillator.detune);
    vibrato.start(startsAt);
    vibrato.stop(endsAt);
  }
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
    this.schedulerTimer = null;
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
    });

    const loopStartTick = section.loopStartTick;
    const loopDurationTicks =
      Number.isFinite(loopStartTick) ? section.durationTicks - loopStartTick : 0;
    this.playing = true;
    this.activeOutput = master;
    this.analyser = analyser;
    this.waveform = waveform;
    this.channelBuses = channelBuses;
    this.startedAt = sectionStart;
    this.duration = duration;
    this.section = section;

    const scheduleStates = section.channels.map((channel) => ({
      channel,
      index: 0,
      loopCount: 0,
      baseTime: sectionStart,
      offsetTick: 0,
      firstLoopIndex: channel.events.findIndex(
        (event) => event.start >= loopStartTick,
      ),
      done: false,
    }));
    const scheduleUpcoming = () => {
      const horizon = this.context.currentTime + 1.5;
      scheduleStates.forEach((state) => {
        while (!state.done) {
          if (state.index >= state.channel.events.length) {
            if (!loopDurationTicks || state.firstLoopIndex < 0) {
              state.done = true;
              break;
            }
            state.baseTime =
              sectionStart +
              duration +
              state.loopCount * loopDurationTicks * tickSeconds;
            state.offsetTick = loopStartTick;
            state.index = state.firstLoopIndex;
            state.loopCount += 1;
          }

          const event = state.channel.events[state.index];
          const eventTime =
            state.baseTime + (event.start - state.offsetTick) * tickSeconds;
          if (eventTime > horizon) break;
          scheduleTone(
            this.context,
            channelBuses.get(state.channel.id),
            state.channel,
            { ...event, start: 0 },
            eventTime,
          );
          state.index += 1;
        }
      });
    };
    scheduleUpcoming();
    this.schedulerTimer = window.setInterval(scheduleUpcoming, 250);

    const draw = () => {
      if (!this.playing) return;
      const absoluteElapsed = Math.max(0, this.context.currentTime - this.startedAt);
      const playbackTick = playbackTickForElapsed(
        absoluteElapsed,
        section.durationTicks,
        loopStartTick,
      );
      const elapsed = playbackTick * tickSeconds;
      const progress = Math.min(1, elapsed / this.duration);
      this.analyser.getFloatTimeDomainData(this.waveform);
      const sumOfSquares = this.waveform.reduce((sum, sample) => sum + sample * sample, 0);
      const audioLevel = Math.sqrt(sumOfSquares / this.waveform.length);
      this.onFrame?.({ elapsed, progress, tick: elapsed / tickSeconds, audioLevel });
      if (loopDurationTicks || progress < 1) {
        this.animationFrame = requestAnimationFrame(draw);
      }
    };
    this.animationFrame = requestAnimationFrame(draw);
    if (!loopDurationTicks) {
      this.stopTimer = window.setTimeout(() => this.stop(), (duration + 0.12) * 1000);
    }
  }

  stop(notify = true) {
    if (this.animationFrame) cancelAnimationFrame(this.animationFrame);
    if (this.stopTimer) clearTimeout(this.stopTimer);
    if (this.schedulerTimer) clearInterval(this.schedulerTimer);
    if (this.activeOutput) {
      // Disconnecting is more reliable than rewriting AudioParam automation
      // while many future notes are scheduled; iOS WebKit can terminate the
      // audio process when those timelines are mutated during playback.
      this.activeOutput.gain.value = 0;
      this.activeOutput.disconnect();
    }
    const wasPlaying = this.playing;
    this.playing = false;
    this.animationFrame = null;
    this.stopTimer = null;
    this.schedulerTimer = null;
    if (wasPlaying && notify) this.onStop?.();
  }

  setMuted(channelId, muted) {
    const bus = this.channelBuses?.get(channelId);
    if (!bus || !this.context) return;
    bus.gain.setTargetAtTime(muted ? 0 : 1, this.context.currentTime, 0.01);
  }
}

export { tickSeconds };
