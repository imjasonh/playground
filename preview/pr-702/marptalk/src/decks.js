const SOURCE_ROOT = 'https://github.com/imjasonh/playground/blob/main/marptalk';

/** The decks that ship with the app, in picker order. */
export const DECKS = [
  {id: 'git-objects', title: 'How Git stores your code'},
  {id: 'game-of-life', title: "Conway's Game of Life"},
  {id: 'gps', title: 'How GPS finds you'},
];

/**
 * @param {string} id
 * @return {string} The deck's path relative to index.html.
 */
export function deckPath(id) {
  return `decks/${id}.md`;
}

/**
 * @param {string} id
 * @return {string} The deck's Markdown on GitHub at the head of main.
 */
export function deckSourceUrl(id) {
  return `${SOURCE_ROOT}/${deckPath(id)}`;
}
