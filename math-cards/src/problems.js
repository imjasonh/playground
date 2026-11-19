/**
 * @fileoverview Math problems and the two answers a card offers for each.
 *
 * A problem kind generates operands and the answer, and lists believable
 * wrong answers for a problem it generated. A mode is the set of kinds a
 * player practices together. More than two addends or larger numbers go in
 * KINDS as another kind, or as options to an existing one.
 *
 * Every kind stays within first and second grade: sums and differences
 * within 100, and multiplication and division facts with factors up to 5,
 * the equal groups and arrays of second grade.
 */

/**
 * @typedef {object} Problem
 * @property {string} kind Key in KINDS.
 * @property {!Array<number>} operands
 * @property {string} operator Symbol shown between operands.
 * @property {string} spoken Word a screen reader says for the operator.
 * @property {number} answer
 */

/**
 * @typedef {object} Card
 * @property {string} kind
 * @property {!Array<number>} operands
 * @property {string} operator
 * @property {string} spoken
 * @property {number} answer
 * @property {!Array<number>} choices Two answers, left then right. One is
 *     the answer.
 */

/**
 * Returns an integer from min to max, inclusive.
 * @param {function(): number} rng Returns a number in [0, 1).
 * @param {number} min
 * @param {number} max
 * @return {number}
 */
export function randomInt(rng, min, max) {
  return min + Math.floor(rng() * (max - min + 1));
}

/**
 * Returns the number with its decimal digits in reverse order.
 * @param {number} n
 * @return {number}
 */
function reverseDigits(n) {
  return Number(String(n).split('').reverse().join(''));
}

/**
 * Returns wrong answers near a sum or difference: off by one or two, a
 * missed or extra carry or borrow (off by ten), or the digits swapped.
 * @param {number} answer
 * @return {!Set<number>}
 */
function nearMisses(answer) {
  const candidates = new Set([
    answer - 1,
    answer + 1,
    answer - 2,
    answer + 2,
    answer - 10,
    answer + 10,
  ]);
  if (answer >= 10 && answer <= 99 && answer % 10 !== 0) {
    candidates.add(reverseDigits(answer));
  }
  return candidates;
}

/**
 * Removes the answer and anything below min or above max.
 * @param {!Set<number>} candidates
 * @param {number} answer
 * @param {number} min
 * @param {number=} max
 * @return {!Array<number>}
 */
function wrongOnly(candidates, answer, min, max = Infinity) {
  return [...candidates].filter((n) => n !== answer && n >= min && n <= max);
}

const addition = {
  name: 'Addition',
  defaults: {max: 100},

  /**
   * Picks the sum first, uniformly from 2 to max, so small and large sums
   * come up equally often. Both addends are at least 1.
   * @param {function(): number} rng
   * @param {{max: number}} options
   * @return {!Problem}
   */
  generate(rng, {max}) {
    const sum = randomInt(rng, 2, max);
    const a = randomInt(rng, 1, sum - 1);
    return {
      kind: 'addition',
      operands: [a, sum - a],
      operator: '+',
      spoken: 'plus',
      answer: sum,
    };
  },

  /**
   * Wrong answers a child might give, from nearMisses. None is negative or
   * above max, so the range alone never gives the answer away.
   * @param {!Problem} problem
   * @param {{max: number}} options
   * @return {!Array<number>}
   */
  distractors({answer}, {max}) {
    return wrongOnly(nearMisses(answer), answer, 0, max);
  },
};

const subtraction = {
  name: 'Subtraction',
  defaults: {max: 100},

  /**
   * Picks the first number from 2 to max, then takes away at least 1 and
   * leaves at least 1.
   * @param {function(): number} rng
   * @param {{max: number}} options
   * @return {!Problem}
   */
  generate(rng, {max}) {
    const a = randomInt(rng, 2, max);
    const b = randomInt(rng, 1, a - 1);
    return {
      kind: 'subtraction',
      operands: [a, b],
      operator: '−',
      spoken: 'minus',
      answer: a - b,
    };
  },

  /**
   * Wrong answers from nearMisses, plus the sum for a child who added.
   * @param {!Problem} problem
   * @param {{max: number}} options
   * @return {!Array<number>}
   */
  distractors({operands: [a, b], answer}, {max}) {
    const candidates = nearMisses(answer);
    candidates.add(a + b);
    return wrongOnly(candidates, answer, 0, max);
  },
};

const multiplication = {
  name: 'Multiplication',
  defaults: {maxFactor: 5},

  /**
   * Multiplies two factors from 1 to maxFactor.
   * @param {function(): number} rng
   * @param {{maxFactor: number}} options
   * @return {!Problem}
   */
  generate(rng, {maxFactor}) {
    const a = randomInt(rng, 1, maxFactor);
    const b = randomInt(rng, 1, maxFactor);
    return {
      kind: 'multiplication',
      operands: [a, b],
      operator: '×',
      spoken: 'times',
      answer: a * b,
    };
  },

  /**
   * Wrong answers a child might give: one group too many or too few, the
   * sum of the factors, or off by one.
   * @param {!Problem} problem
   * @return {!Array<number>}
   */
  distractors({operands: [a, b], answer}) {
    const candidates = new Set([
      answer + a,
      answer - a,
      answer + b,
      answer - b,
      a + b,
      answer + 1,
      answer - 1,
    ]);
    return wrongOnly(candidates, answer, 0);
  },
};

const division = {
  name: 'Division',
  defaults: {maxFactor: 5},

  /**
   * Divides a product of two factors from 1 to maxFactor by one of them,
   * so it always comes out even.
   * @param {function(): number} rng
   * @param {{maxFactor: number}} options
   * @return {!Problem}
   */
  generate(rng, {maxFactor}) {
    const divisor = randomInt(rng, 1, maxFactor);
    const quotient = randomInt(rng, 1, maxFactor);
    return {
      kind: 'division',
      operands: [divisor * quotient, divisor],
      operator: '÷',
      spoken: 'divided by',
      answer: quotient,
    };
  },

  /**
   * Wrong answers a child might give: off by one, the divisor itself, or
   * the difference for a child who subtracted.
   * @param {!Problem} problem
   * @return {!Array<number>}
   */
  distractors({operands: [dividend, divisor], answer}) {
    const candidates = new Set([
      answer - 1,
      answer + 1,
      divisor,
      dividend - divisor,
    ]);
    return wrongOnly(candidates, answer, 0);
  },
};

/** Problem kinds by key. */
export const KINDS = {addition, subtraction, multiplication, division};

/** The kinds each mode deals, by mode key. */
export const MODES = {
  'addition': ['addition'],
  'subtraction': ['subtraction'],
  'multiply-divide': ['multiplication', 'division'],
};

/**
 * Reports whether key names a mode.
 * @param {?string} key
 * @return {boolean}
 */
export function isMode(key) {
  return typeof key === 'string' && Object.hasOwn(MODES, key);
}

/**
 * Reports whether two problems ask the same question.
 * @param {!Problem} a
 * @param {!Problem} b
 * @return {boolean}
 */
export function sameProblem(a, b) {
  return a.kind === b.kind && a.operator === b.operator &&
      a.operands.length === b.operands.length &&
      a.operands.every((n, i) => n === b.operands[i]);
}

/**
 * Makes a card: a problem, the answer, and one wrong answer, in random
 * left and right order.
 * @param {string} kindKey Key in KINDS.
 * @param {function(): number} rng Returns a number in [0, 1).
 * @param {?Problem=} previous The card before this one, which the new
 *     card won't repeat.
 * @param {!Object=} options Overrides the kind's defaults.
 * @return {!Card}
 */
export function makeCard(kindKey, rng, previous = null, options = {}) {
  if (!Object.hasOwn(KINDS, kindKey)) {
    throw new Error(`unknown problem kind ${kindKey}`);
  }
  const kind = KINDS[kindKey];
  const settings = {...kind.defaults, ...options};
  let problem = kind.generate(rng, settings);
  for (let tries = 0; previous && sameProblem(problem, previous) &&
      tries < 20; tries++) {
    problem = kind.generate(rng, settings);
  }
  const wrong = kind.distractors(problem, settings);
  const distractor = wrong.length > 0 ?
      wrong[randomInt(rng, 0, wrong.length - 1)] :
      problem.answer + 1;
  const choices = rng() < 0.5 ?
      [problem.answer, distractor] :
      [distractor, problem.answer];
  return {...problem, choices};
}

/**
 * Makes a card of one of the mode's kinds, picked at random.
 * @param {string} modeKey Key in MODES.
 * @param {function(): number} rng Returns a number in [0, 1).
 * @param {?Problem=} previous The card before this one, which the new
 *     card won't repeat.
 * @return {!Card}
 */
export function dealCard(modeKey, rng, previous = null) {
  if (!isMode(modeKey)) {
    throw new Error(`unknown mode ${modeKey}`);
  }
  const kinds = MODES[modeKey];
  return makeCard(kinds[randomInt(rng, 0, kinds.length - 1)], rng, previous);
}

/**
 * Returns the problem as text, such as "23 + 45".
 * @param {!Problem} problem
 * @return {string}
 */
export function problemText(problem) {
  return problem.operands.join(` ${problem.operator} `);
}

/**
 * Returns the problem as a screen reader should say it, such as
 * "23 plus 45".
 * @param {!Problem} problem
 * @return {string}
 */
export function spokenProblem(problem) {
  return problem.operands.join(` ${problem.spoken} `);
}
