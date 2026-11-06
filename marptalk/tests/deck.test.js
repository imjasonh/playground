import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import test from 'node:test';

import {deckDurationMs, parseDeck} from '../src/deck.js';
import {DECKS, deckPath, deckSourceUrl} from '../src/decks.js';
import {lintDeck} from '../src/lint.js';
import {MAX_CUE_CHARS} from '../src/script.js';

const SAMPLE = `---
marp: true
title: "Sample deck"
lang: fr-FR
---

# First

<!-- _class: lead -->
<!-- Bonjour. Ceci est la première diapositive. -->

---

# Second

<!--
Notes can span
several lines.
-->
<!-- And a second comment joins the first. -->

---

# Third has no notes
`;

test('parseDeck pairs each slide with its own notes', () => {
  const deck = parseDeck(SAMPLE);
  assert.equal(deck.slides.length, 3);
  assert.deepEqual(deck.slides[0].cues, [
    'Bonjour.',
    'Ceci est la première diapositive.',
  ]);
  assert.equal(
    deck.slides[1].notes,
    'Notes can span\nseveral lines.\n\nAnd a second comment joins the first.',
  );
  assert.deepEqual(deck.slides[2].cues, []);
});

test('parseDeck reads title and lang', () => {
  const deck = parseDeck(SAMPLE);
  assert.equal(deck.title, 'Sample deck');
  assert.equal(deck.lang, 'fr-FR');
});

test('parseDeck falls back to the first heading and en-US', () => {
  const deck = parseDeck('# Only *heading*\n\n<!-- Hi. -->\n');
  assert.equal(deck.title, 'Only heading');
  assert.equal(deck.lang, 'en-US');
});

test('parseDeck renders one SVG per slide and no script', () => {
  const deck = parseDeck(SAMPLE + '\n<script>alert(1)</script>\n');
  assert.equal(deck.html.match(/<svg data-marpit-svg/g).length, 3);
  assert.doesNotMatch(deck.html, /<script/);
});

test('deckDurationMs scales with rate', () => {
  const deck = parseDeck(SAMPLE);
  const normal = deckDurationMs(deck, 1);
  assert.ok(normal > 0);
  assert.equal(deckDurationMs(deck, 2), normal / 2);
});

test('deckSourceUrl links to the deck on main', () => {
  assert.equal(
    deckSourceUrl('gps'),
    'https://github.com/imjasonh/playground/blob/main/marptalk/decks/gps.md',
  );
});

test('lintDeck reports what makes a deck worse to listen to', () => {
  const md = `---
theme: default
---

# One

<!-- See **this** at https://example.com -> now. -->

---

# Two

---

# Three

${'word '.repeat(60)}

<!-- ${'Talk. '.repeat(170)} -->
`;
  const messages = lintDeck(md).map((f) => `${f.slide}: ${f.message}`);
  const expected = [
    /^0: .*marp: true/,
    /^1: .*Markdown/,
    /^1: .*URL/,
    /^1: .*arrows/,
    /^2: No voiceover/,
    /^3: Voiceover is 170 words/,
    /^3: Slide shows 61 words/,
  ];
  assert.equal(messages.length, expected.length, messages.join('\n'));
  expected.forEach((re, i) => assert.match(messages[i], re));
});

test('lintDeck flags math, which is not rendered', () => {
  const md = '---\nmarp: true\n---\n\n# E\n\n$E = mc^2$\n\n<!-- Energy. -->\n';
  assert.match(lintDeck(md)[0].message, /Math/);
});

test('lintDeck ignores dollar signs that are not math', () => {
  const md =
    '---\nmarp: true\n---\n\n# Cost\n\nIt costs $50.\n\n```console\n' +
    '$ ls\n```\n\n<!-- Fifty dollars. -->\n';
  assert.deepEqual(lintDeck(md), []);
});

for (const {id, title} of DECKS) {
  test(`bundled deck ${id} renders and passes lint`, () => {
    const markdown = readFileSync(
      new URL(`../${deckPath(id)}`, import.meta.url),
      'utf8',
    );
    const deck = parseDeck(markdown);
    assert.equal(deck.title, title);
    assert.ok(deck.slides.length >= 5);
    for (const slide of deck.slides) {
      for (const cue of slide.cues) assert.ok(cue.length <= MAX_CUE_CHARS);
    }
    assert.deepEqual(lintDeck(markdown), []);
  });
}
