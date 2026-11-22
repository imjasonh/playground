// The player's side of a puzzle: marks, conflicts, the win check, and
// hints. No DOM, so Node can test it.
//
// Marks use the solver's cell states: UNKNOWN for a blank cell, STAR for a
// queen or star, and EMPTY for a cell marked ×.

import {
  EMPTY,
  STAR,
  UNKNOWN,
  implied,
  makeShape,
  nextStep,
} from './puzzle.js';

export const REGION_NAMES = [
  'purple',
  'orange',
  'blue',
  'green',
  'gray',
  'red',
  'yellow',
  'teal',
  'pink',
  'brown',
];

export function shapeOf(puzzle) {
  return makeShape(puzzle.size, puzzle.stars, puzzle.regions);
}

// A tap moves a cell from blank to ×, from × to a star, and back to blank.
export function cycleMark(mark) {
  if (mark === UNKNOWN) {
    return EMPTY;
  }
  return mark === EMPTY ? STAR : UNKNOWN;
}

// Returns the star cells that break a rule: they touch another star, or
// share a row, column, or region with too many stars.
export function conflicts(shape, marks) {
  const bad = new Set();
  for (let cell = 0; cell < marks.length; cell += 1) {
    if (marks[cell] !== STAR) {
      continue;
    }
    for (const other of shape.neighbors[cell]) {
      if (marks[other] === STAR) {
        bad.add(cell);
      }
    }
  }
  for (const unit of shape.units) {
    const stars = unit.filter((cell) => marks[cell] === STAR);
    if (stars.length > shape.stars) {
      stars.forEach((cell) => bad.add(cell));
    }
  }
  return bad;
}

export function isWon(shape, marks) {
  return shape.units.every((unit) =>
    unit.filter((cell) => marks[cell] === STAR).length === shape.stars) &&
      conflicts(shape, marks).size === 0;
}

// Returns the blank cells that the stars rule out: the cells around each
// star, and the rest of each row, column, or region that has all its stars.
export function dots(shape, marks) {
  if (conflicts(shape, marks).size > 0) {
    return new Set();
  }
  const stars = marks.map((mark) => (mark === STAR ? STAR : UNKNOWN));
  const known = implied(shape, stars);
  const result = new Set();
  for (let cell = 0; cell < marks.length; cell += 1) {
    if (marks[cell] === UNKNOWN && known[cell] === EMPTY) {
      result.add(cell);
    }
  }
  return result;
}

function capitalize(text) {
  return text.charAt(0).toUpperCase() + text.slice(1);
}

function joinList(items) {
  if (items.length <= 2) {
    return items.join(' and ');
  }
  return `${items.slice(0, -1).join(', ')}, and ${items.at(-1)}`;
}

function unitKind(shape, u) {
  const {size} = shape;
  if (u < size) {
    return {kind: 'row', index: u};
  }
  if (u < 2 * size) {
    return {kind: 'column', index: u - size};
  }
  return {kind: 'region', index: u - 2 * size};
}

// Names units of one kind, such as "row 3", "columns 2 and 5", or "the
// purple and blue regions".
function nameUnits(shape, units) {
  const parts = units.map((u) => unitKind(shape, u));
  const {kind} = parts[0];
  if (kind === 'region') {
    const colors = parts.map((p) => REGION_NAMES[p.index]);
    const noun = parts.length === 1 ? 'region' : 'regions';
    return `the ${joinList(colors)} ${noun}`;
  }
  const numbers = parts.map((p) => String(p.index + 1));
  const noun = parts.length === 1 ? kind : `${kind}s`;
  return `${noun} ${joinList(numbers)}`;
}

function nouns(game) {
  return game.stars === 1 ?
      {one: 'queen', many: 'queens'} :
      {one: 'star', many: 'stars'};
}

// Explains step in a sentence or two, for the hint line.
export function describeStep(puzzle, step) {
  const shape = shapeOf(puzzle);
  const {one, many} = nouns(puzzle);
  const piece = (count) => (count === 1 ? one : many);
  switch (step.rule) {
    case 'forced': {
      const unit = nameUnits(shape, step.units);
      const count = step.place.length;
      if (count === 1) {
        return `${capitalize(unit)} has one open cell left, so its ` +
            `${one} goes there.`;
      }
      return `${capitalize(unit)} has ${count} open cells left and needs ` +
          `${count} ${many}, so each one holds a ${one}.`;
    }
    case 'touch': {
      const unit = nameUnits(shape, step.units);
      return `A ${one} here would leave ${unit} without room for its ` +
          `${piece(puzzle.stars)}. Mark it ×.`;
    }
    case 'group': {
      const {count} = step;
      const from = nameUnits(shape, step.units.slice(0, count));
      const into = step.units.slice(count);
      const intoName = nameUnits(shape, into);
      const pieces = piece(count * puzzle.stars);
      if (count === 1) {
        return `${capitalize(from)} can only hold its ${pieces} in ` +
            `${intoName}. That uses up ${intoName}'s ${pieces}, so mark ` +
            `the rest of ${intoName} ×.`;
      }
      const {kind} = unitKind(shape, into[0]);
      return `${capitalize(from)} can only hold their ${pieces} in ` +
          `${intoName}. That uses up all the ${pieces} in those ` +
          `${kind}s, so mark their other cells ×.`;
    }
    case 'forcing':
      return `If this cell held a ${one}, the basic rules would soon ` +
          'leave a row, column, or region without room for its ' +
          `${piece(puzzle.stars)}. Mark it ×.`;
    case 'reveal':
      return `This cell holds a ${one}.`;
    default:
      throw new Error(`unknown rule ${step.rule}`);
  }
}

// Finds a hint for marks. A mark that disagrees with the solution comes
// first. Otherwise the hint is the easiest step the rules find, or, if
// they find none, a star from the solution.
//
// Returns {rule, cells, place, clear, reason, text}: the rule behind the
// hint ('mistake' for a wrong mark), the cells to change, which of them
// hold stars and which are empty, the cells that explain why, and the
// explanation.
export function findHint(puzzle, marks) {
  const {one, many} = nouns(puzzle);
  const wrongStars = [];
  const wrongMarks = [];
  for (let cell = 0; cell < marks.length; cell += 1) {
    if (marks[cell] === STAR && !puzzle.solution[cell]) {
      wrongStars.push(cell);
    } else if (marks[cell] === EMPTY && puzzle.solution[cell]) {
      wrongMarks.push(cell);
    }
  }
  if (wrongStars.length > 0) {
    const text = wrongStars.length === 1 ?
        `This ${one} isn't part of the solution.` :
        `These ${many} aren't part of the solution.`;
    return {rule: 'mistake', cells: wrongStars, place: [], clear: wrongStars,
      reason: [], text};
  }
  if (wrongMarks.length > 0) {
    const text = wrongMarks.length === 1 ?
        `This cell is marked ×, but it holds a ${one}.` :
        `These cells are marked ×, but they hold ${many}.`;
    return {rule: 'mistake', cells: wrongMarks, place: wrongMarks, clear: [],
      reason: [], text};
  }
  const shape = shapeOf(puzzle);
  let step = nextStep(shape, marks);
  if (!step) {
    const known = implied(shape, marks);
    const cell = puzzle.solution.findIndex(
        (star, i) => star && known[i] !== STAR);
    if (cell < 0) {
      return null;
    }
    step = {rule: 'reveal', place: [cell], clear: [], reason: [], units: []};
  }
  return {
    rule: step.rule,
    cells: [...step.place, ...step.clear],
    place: step.place,
    clear: step.clear,
    reason: step.reason,
    text: describeStep(puzzle, step),
  };
}
