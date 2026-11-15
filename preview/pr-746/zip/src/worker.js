// Builds puzzles off the main thread. A hard board can take a few seconds
// on a phone.

import {generatePuzzle} from './zip.js';

self.addEventListener('message', (event) => {
  const {key, level, seed} = event.data;
  self.postMessage({key, puzzle: generatePuzzle(level, seed)});
});
