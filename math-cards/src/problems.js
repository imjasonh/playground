/**
 * @fileoverview Math problems and the two answers a card offers for each.
 *
 * A problem kind generates operands and the answer, and lists believable
 * wrong answers for a problem it generated. Subtraction, multiplication,
 * division, more than two addends, and larger numbers each go in KINDS as
 * another kind, or as options to an existing one.
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
   * Wrong answers a child might give: off by one or two, a missed or extra
   * carry (off by ten), or the digits swapped. None is negative or above
   * max, so the range alone never gives the answer away.
   * @param {!Problem} problem
   * @param {{max: number}} options
   * @return {!Array<number>}
   */
  distractors({answer}, {max}) {
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
    candidates.delete(answer);
    return [...candidates].filter((n) => n >= 0 && n <= max);
  },
};

/** Problem kinds by key. */
export const KINDS = {addition};

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
  const kind = KINDS[kindKey];
  if (!kind) {
    throw new Error(`unknown problem kind ${kindKey}`);
  }
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
