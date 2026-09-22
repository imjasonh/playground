import { clamp } from "./geo.js";

const AILERON = {
  "left-hard": -0.7,
  left: -0.32,
  level: 0,
  right: 0.32,
  "right-hard": 0.7,
};

const ELEVATOR = {
  "down-hard": -0.45,
  down: -0.18,
  hold: 0,
  up: 0.18,
  "up-hard": 0.4,
};

const RUDDER = {
  left: -0.28,
  center: 0,
  right: 0.28,
};

const THROTTLE_ABS = {
  cut: 0.28,
  less: null,
  hold: null,
  more: null,
  full: 0.95,
};

/**
 * Map one System One answer set onto control surfaces. The model picks labels.
 * This file only turns those labels into deflections, then slews so the
 * surfaces do not jump.
 */
export function answersToTargets(answers, current, state) {
  const aileronChoice = answers.aileron?.choice ?? "level";
  let aileron = AILERON[aileronChoice] ?? 0;
  if (aileronChoice === "level") {
    const roll = Number(state.roll_deg) || 0;
    const headingErr = Number(state.heading_err_deg) || 0;
    const desiredBank = clamp(headingErr * 0.75, -30, 30);
    aileron = clamp((desiredBank - roll) / 40, -0.22, 0.22);
  }

  const elevator = ELEVATOR[answers.elevator?.choice] ?? 0;
  const rudder = RUDDER[answers.rudder?.choice] ?? 0;

  let throttle = current.throttle;
  const thr = answers.throttle?.choice ?? "hold";
  if (thr === "cut" || thr === "full") {
    throttle = THROTTLE_ABS[thr];
  } else if (thr === "less") {
    throttle = clamp(current.throttle - 0.07, 0.15, 1);
  } else if (thr === "more") {
    throttle = clamp(current.throttle + 0.07, 0.15, 1);
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
