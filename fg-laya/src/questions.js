/**
 * Typed System One questions. Same primitives as Laya and Jev: choice, score,
 * noul. Every flight control is one of these. The model never writes a number
 * onto an axis directly.
 */
export const QUESTION_KINDS = ["choice", "score", "noul"];

export function flightQuestions() {
  return {
    aileron: {
      type: "choice",
      instructions:
        "Pick the aileron command. Bank toward the desired heading. Do not exceed about 30 degrees of bank. Level the wings when the heading is close and the bank is already about right.",
      criteria: {
        "left-hard": "Roll left hard. Large left heading error, or the right bank is much too steep.",
        left: "Roll left. The desired heading is left of the nose, or you need a shallower right bank.",
        level: "Hold or return toward the bank you want for this heading error. Use when the turn is already about right.",
        right: "Roll right. The desired heading is right of the nose, or you need a shallower left bank.",
        "right-hard": "Roll right hard. Large right heading error, or the left bank is much too steep.",
      },
    },
    elevator: {
      type: "choice",
      instructions:
        "Pick the elevator command. Hold the target altitude and a safe pitch. Pitch down if the airplane is too slow or too high. Pitch up if it is too low and still has speed.",
      criteria: {
        "down-hard": "Push the nose down. Use when pitch is very nose-up, airspeed is low, or the airplane is much too high.",
        down: "Lower the nose a little. Slightly high, slightly slow, or a bit too nose-up.",
        hold: "Hold this pitch. Altitude and speed are close and pitch is already reasonable.",
        up: "Raise the nose a little. Slightly low or a bit too fast, and airspeed is safe.",
        "up-hard": "Pull up. Much too low, and airspeed is not near the stall.",
      },
    },
    throttle: {
      type: "choice",
      instructions: "Pick the throttle command that holds the target airspeed.",
      criteria: {
        cut: "Reduce power a lot. Well above the target speed, or diving with too much energy.",
        less: "Reduce power a little. A bit fast.",
        hold: "Hold this throttle. On speed.",
        more: "Add power a little. A bit slow.",
        full: "Add a lot of power. Well below the target speed, or climbing and getting slow.",
      },
    },
    rudder: {
      type: "choice",
      instructions: "Pick the rudder command that keeps the slip near zero. In a bank, use a little rudder in the direction of the turn.",
      criteria: {
        left: "Left rudder. The ball is right, or you are in a left bank without enough rudder.",
        center: "Center the rudder. Slip is small and the turn is coordinated.",
        right: "Right rudder. The ball is left, or you are in a right bank without enough rudder.",
      },
    },
    arrived: {
      type: "noul",
      instructions: "The airplane has reached the current waypoint and should retarget.",
      criteria: {
        true: "Distance to the waypoint is inside the arrival radius.",
        false: "Still inbound to this waypoint.",
      },
    },
  };
}

export function validateQuestion(question) {
  if (!QUESTION_KINDS.includes(question?.type)) {
    throw new Error("Question type must be choice, score, or noul.");
  }
  if (!String(question.instructions ?? "").trim()) {
    throw new Error("Instructions are empty.");
  }
  if (question.type === "choice" && choiceLabels(question).length < 2) {
    throw new Error("A choice question needs at least two options.");
  }
  if (question.type === "score" && scoreLevels(question).length < 2) {
    throw new Error("A score question needs at least two levels.");
  }
}

export function choiceLabels(question) {
  const criteria = question.criteria;
  if (Array.isArray(criteria)) {
    return criteria.map((item) => (typeof item === "string" ? item : item.label));
  }
  return Object.keys(criteria ?? {});
}

export function scoreLevels(question) {
  return Array.isArray(question.criteria) ? question.criteria.slice() : [];
}

export function optionLabels(question) {
  if (question.type === "choice") {
    return choiceLabels(question);
  }
  if (question.type === "score") {
    return scoreLevels(question).map((_, i) => String(i));
  }
  return ["false", "true"];
}
