export const ROWS = 5;
export const COLS = 11;
export const CELL_COUNT = ROWS * COLS;

/** Number of starter pieces fixed on the board per difficulty (1 = easiest). */
export const DIFFICULTY_STARTER_PIECES = {
  1: 11,
  2: 10,
  3: 9,
  4: 8,
  5: 6,
  6: 0,
};

export const DIFFICULTY_LABELS = {
  1: 'Level 1 — fill 1 piece',
  2: 'Level 2 — fill 2 pieces',
  3: 'Level 3 — fill 3 pieces',
  4: 'Level 4 — fill 4 pieces',
  5: 'Level 5 — fill 6 pieces',
  6: 'Level 6 — free play (empty board)',
};
