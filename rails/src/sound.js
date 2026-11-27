// Lightweight WebAudio sound effects for live game nights (no audio files needed).
let audioCtx = null;
let enabled = true;

function ctx() {
  if (!enabled) return null;
  if (!audioCtx && typeof window !== "undefined") {
    const Ctor = window.AudioContext || window.webkitAudioContext;
    if (Ctor) audioCtx = new Ctor();
  }
  if (audioCtx && audioCtx.state === "suspended") {
    audioCtx.resume().catch(() => {});
  }
  return audioCtx;
}

export function setSoundEnabled(v) {
  enabled = Boolean(v);
}

export function isSoundEnabled() {
  return enabled;
}

function tone(freq, duration, type = "sine", gainVal = 0.08, delay = 0) {
  const c = ctx();
  if (!c) return;
  const now = c.currentTime + delay;
  const osc = c.createOscillator();
  const g = c.createGain();
  osc.type = type;
  osc.frequency.setValueAtTime(freq, now);
  g.gain.setValueAtTime(0.0001, now);
  g.gain.exponentialRampToValueAtTime(gainVal, now + 0.015);
  g.gain.exponentialRampToValueAtTime(0.0001, now + duration);
  osc.connect(g);
  g.connect(c.destination);
  osc.start(now);
  osc.stop(now + duration + 0.02);
}

export function playTurnChime() {
  tone(523.25, 0.16, "triangle", 0.09, 0);
  tone(659.25, 0.22, "triangle", 0.09, 0.1);
}

export function playBuildClick() {
  tone(260, 0.06, "square", 0.04, 0);
}

export function playDeliverChime() {
  tone(587.33, 0.12, "sine", 0.09, 0);
  tone(783.99, 0.14, "sine", 0.09, 0.09);
  tone(1046.5, 0.26, "sine", 0.1, 0.18);
}

export function playVictoryFanfare() {
  [523.25, 659.25, 783.99, 1046.5].forEach((f, i) => {
    tone(f, 0.35, "triangle", 0.11, i * 0.11);
  });
}
