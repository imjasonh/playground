// Listener / panner pose helpers shared by the realtime graph. Kept free of
// the synth so pose-setting stays easy to reason about.

export function setListenerPose(listener, pos, forward, up, when) {
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

export function setPannerPosition(panner, pos, when) {
  if (panner.positionX) {
    panner.positionX.setValueAtTime(pos[0], when);
    panner.positionY.setValueAtTime(pos[1], when);
    panner.positionZ.setValueAtTime(pos[2], when);
  } else {
    panner.setPosition(pos[0], pos[1], pos[2]);
  }
}
