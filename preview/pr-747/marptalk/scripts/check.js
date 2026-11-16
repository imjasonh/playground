/**
 * Checks marptalk decks and prints what to fix.
 *
 * Usage: node marptalk/scripts/check.js deck.md [more.md ...]
 *
 * Exits 1 when any deck has findings.
 */
import {readFileSync} from 'node:fs';
import {argv, exit, stderr, stdout} from 'node:process';

import {deckDurationMs, parseDeck} from '../src/deck.js';
import {lintDeck} from '../src/lint.js';

const files = argv.slice(2);
if (!files.length) {
  stderr.write('usage: node scripts/check.js deck.md [more.md ...]\n');
  exit(2);
}

let failed = false;
for (const file of files) {
  const markdown = readFileSync(file, 'utf8');
  const deck = parseDeck(markdown);
  const minutes = (deckDurationMs(deck) / 60000).toFixed(1);
  const findings = lintDeck(markdown);
  stdout.write(
    `${file}: "${deck.title}", ${deck.slides.length} slides, ` +
      `about ${minutes} min at 1x\n`,
  );
  for (const {slide, message} of findings) {
    stdout.write(`  ${slide ? `slide ${slide}` : 'deck'}: ${message}\n`);
  }
  if (findings.length) failed = true;
}
exit(failed ? 1 : 0);
