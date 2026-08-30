/**
 * Playable spiral puzzle state: letters the solver has entered,
 * selection, and check/reveal helpers.
 */
export function createPlayState(puzzle) {
  return {
    puzzle,
    guesses: Array(puzzle.size).fill(""),
    selected: 0,
    activeDir: "inward",
    activeClueIndex: 0,
    revealed: false,
    checked: false,
  };
}

export function letterAt(state, index) {
  if (state.revealed) return state.puzzle.letters[index];
  return state.guesses[index] || "";
}

export function setLetter(state, index, ch) {
  if (state.revealed) return state;
  const guesses = state.guesses.slice();
  guesses[index] = ch ? ch.toUpperCase() : "";
  return { ...state, guesses, checked: false };
}

export function clearGuesses(state) {
  return {
    ...state,
    guesses: Array(state.puzzle.size).fill(""),
    revealed: false,
    checked: false,
  };
}

export function revealAll(state) {
  return {
    ...state,
    guesses: state.puzzle.letters.split(""),
    revealed: true,
    checked: false,
  };
}

export function checkGuesses(state) {
  return { ...state, checked: true };
}

export function cellStatus(state, index) {
  const guess = state.guesses[index];
  if (!guess) return "empty";
  if (state.revealed) return "revealed";
  if (!state.checked) return "filled";
  return guess === state.puzzle.letters[index] ? "correct" : "wrong";
}

/** Cell indices (0-based) covered by a clue span. */
export function spanIndices(span) {
  const a = span.start;
  const b = span.end;
  const indices = [];
  if (a <= b) {
    for (let n = a; n <= b; n += 1) indices.push(n - 1);
  } else {
    for (let n = a; n >= b; n -= 1) indices.push(n - 1);
  }
  return indices;
}

export function selectClue(state, dir, clueIndex) {
  const list = state.puzzle[dir];
  const span = list[clueIndex];
  if (!span) return state;
  const indices = spanIndices(span);
  return {
    ...state,
    activeDir: dir,
    activeClueIndex: clueIndex,
    selected: indices[0] ?? state.selected,
  };
}

export function activeSpan(state) {
  return state.puzzle[state.activeDir][state.activeClueIndex] ?? null;
}

export function isSolved(state) {
  return state.guesses.every((ch, i) => ch === state.puzzle.letters[i]);
}

export function filledCount(state) {
  return state.guesses.filter(Boolean).length;
}
