import assert from 'node:assert/strict';
import {test} from 'node:test';

import {findWords} from '../src/words.js';

/**
 * @param {!Array<{text: string, breakBefore: boolean}>} pieces
 * @return {!Array<string>} Each word's text.
 */
function wordTexts(pieces) {
  return findWords(pieces).map((slices) =>
    slices
      .map(({piece, start, end}) => pieces[piece].text.slice(start, end))
      .join(''),
  );
}

test('findWords keeps punctuation with its word', () => {
  assert.deepEqual(wordTexts([{text: 'Hello, world!', breakBefore: true}]), [
    'Hello,',
    'world!',
  ]);
});

test('findWords skips every kind of whitespace', () => {
  assert.deepEqual(
    wordTexts([{text: '  leading\ttabs\n\nand  trailing ', breakBefore: true}]),
    ['leading', 'tabs', 'and', 'trailing'],
  );
});

test('findWords joins a word across inline elements', () => {
  // Ship the <a>new</a>, <b>bold</b>thing by <a>Friday</a>.
  const pieces = [
    {text: 'Ship the ', breakBefore: true},
    {text: 'new', breakBefore: false},
    {text: ', ', breakBefore: false},
    {text: 'bold', breakBefore: false},
    {text: 'thing by ', breakBefore: false},
    {text: 'Friday', breakBefore: false},
    {text: '.', breakBefore: false},
  ];
  assert.deepEqual(wordTexts(pieces), [
    'Ship',
    'the',
    'new,',
    'boldthing',
    'by',
    'Friday.',
  ]);
  assert.deepEqual(findWords(pieces).at(-1), [
    {piece: 5, start: 0, end: 6},
    {piece: 6, start: 0, end: 1},
  ]);
});

test('findWords splits words at a break', () => {
  // <li>one</li><li>two</li> and line<br>break
  assert.deepEqual(
    wordTexts([
      {text: 'one', breakBefore: true},
      {text: 'two', breakBefore: true},
      {text: 'line', breakBefore: true},
      {text: 'break', breakBefore: true},
    ]),
    ['one', 'two', 'line', 'break'],
  );
});

test('findWords splits words at whitespace between pieces', () => {
  assert.deepEqual(
    wordTexts([
      {text: 'a', breakBefore: true},
      {text: '\n', breakBefore: false},
      {text: 'b', breakBefore: false},
      {text: '', breakBefore: false},
      {text: 'c', breakBefore: false},
    ]),
    ['a', 'bc'],
  );
});
