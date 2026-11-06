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
