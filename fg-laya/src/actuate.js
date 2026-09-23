import { clamp } from "./geo.js";

const BANK = {
  "left-hard": -28,
  left: -18,
  level: null,
  right: 18,
  "right-hard": 28,
};

const PITCH = {
  "down-hard": -6,
  down: -2,
  hold: 2,
  up: 6,
  "up-hard": 9,
};

const RUDDER = {
  left: -0.18,
  center: 0,
  right: 0.18,
};

const THROTTLE_ABS = {
  cut: 0.35,
  less: null,
  hold: null,
  more: null,
  full: 0.92,
};

/**
 * Map one System One answer set onto control surfaces. The model picks labels.
 * Labels become bank and pitch targets, then a small P loop writes deflections
 * so a "left-hard" at 40 degrees of bank rolls back toward 24 instead of
 * adding more aileron.
 */
export function answersToTargets(answers, current, state) {
  const roll = Number(state.roll_deg) || 0;
  const pitch = Number(state.pitch_deg) || 0;
  const headingErr = Number(state.heading_err_deg) || 0;
  const ias = Number(state.airspeed_kt) || 100;

  const aileronChoice = answers.aileron?.choice ?? "level";
  let desiredBank = BANK[aileronChoice];
  if (desiredBank == null) {
    desiredBank = clamp(headingErr * 0.65, -22, 22);
  }
  if (ias < 70) {
    desiredBank = clamp(desiredBank, -12, 12);
  }
  const aileron = clamp((desiredBank - roll) / 22, -0.42, 0.42);

  const elevatorChoice = answers.elevator?.choice ?? "hold";
  let desiredPitch = PITCH[elevatorChoice] ?? 2;
  const altErr = Number(state.altitude_err_ft) || 0;
  if (ias < 65) {
    desiredPitch = Math.min(desiredPitch, -2);
  } else if (altErr < -250) {
    desiredPitch = Math.max(desiredPitch, 5);
  }
  const elevator = clamp((desiredPitch - pitch) / 6, -0.45, 0.55);

  const rudder = RUDDER[answers.rudder?.choice] ?? 0;

  let throttle = current.throttle;
  const thr = answers.throttle?.choice ?? "hold";
  if (thr === "cut" || thr === "full") {
    throttle = THROTTLE_ABS[thr];
  } else if (thr === "less") {
    throttle = clamp(current.throttle - 0.05, 0.28, 1);
  } else if (thr === "more") {
    throttle = clamp(current.throttle + 0.05, 0.28, 1);
  }
  if (ias < 65 || altErr < -300) {
    throttle = Math.max(throttle, 0.85);
  }

  return {
    aileron: clamp(aileron, -1, 1),
    elevator: clamp(elevator, -1, 1),
    rudder: clamp(rudder, -1, 1),
    throttle: clamp(throttle, 0, 1),
  };
}

export function slewControls(current, target, dt, rate = 2.4) {
  const step = rate * dt;
  return {
    aileron: approach(current.aileron, target.aileron, step),
    elevator: approach(current.elevator, target.elevator, step),
    rudder: approach(current.rudder, target.rudder, step),
    throttle: approach(current.throttle, target.throttle, step * 0.6),
  };
}

function approach(from, to, step) {
  const d = to - from;
  if (Math.abs(d) <= step) {
    return to;
  }
  return from + Math.sign(d) * step;
}

export function arrivedYes(answers) {
  const noul = answers.arrived?.noul;
  return Number(noul) >= 0.5;
}
