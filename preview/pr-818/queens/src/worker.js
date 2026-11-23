// Builds puzzles off the main thread. An expert board can take a few
// seconds on a phone.

import {generatePuzzle} from './puzzle.js';

self.addEventListener('message', (event) => {
  const {key, game, level, seed} = event.data;
  self.postMessage({key, puzzle: generatePuzzle(game, level, seed)});
});
