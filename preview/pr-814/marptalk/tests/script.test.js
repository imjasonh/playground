import assert from 'node:assert/strict';
import test from 'node:test';

import {
  MAX_CUE_CHARS,
  countWords,
  estimateMs,
  splitSentences,
  toCues,
  toSpokenText,
} from '../src/script.js';

test('toSpokenText drops Markdown a voice would read aloud', () => {
  assert.equal(
    toSpokenText(
      '**Bold** and *italic* and `code` and [a link](https://x.test).\n' +
        '- a bullet\n\n## heading',
    ),
    'Bold and italic and code and a link. a bullet heading',
  );
});

test('toSpokenText keeps underscores inside words', () => {
  assert.equal(toSpokenText('call read_file now'), 'call read_file now');
});

test('splitSentences keeps abbreviations and decimals together', () => {
  assert.deepEqual(
    splitSentences('Pi is about 3.14. Dr. Smith agreed! Did you?'),
    ['Pi is about 3.14.', 'Dr. Smith agreed!', 'Did you?'],
  );
});

test('toCues splits long sentences at clause boundaries', () => {
  const long =
    'Git stores every version of every file as a blob, names each blob ' +
    'by the hash of its contents, and groups blobs into trees that mirror ' +
    'your directories, so identical files are stored exactly once.';
  const cues = toCues(long);
  assert.ok(cues.length > 1);
  for (const c of cues) assert.ok(c.length <= MAX_CUE_CHARS, c);
  assert.equal(cues.join(' '), long);
  assert.match(cues[0], /,$/);
});

test('toCues splits a run-on with no punctuation at spaces', () => {
  const words = Array.from({length: 60}, (_, i) => `word${i}`).join(' ');
  const cues = toCues(words);
  for (const c of cues) assert.ok(c.length <= MAX_CUE_CHARS);
  assert.equal(cues.join(' '), words);
});

test('toCues returns nothing for empty notes', () => {
  assert.deepEqual(toCues(''), []);
  assert.deepEqual(toCues('   \n '), []);
});

test('estimateMs scales with words and rate', () => {
  const text = 'one two three four five six seven eight nine ten.';
  assert.equal(countWords(text), 10);
  const normal = estimateMs(text, 1);
  assert.ok(normal > 3000 && normal < 5000, `${normal}`);
  assert.equal(estimateMs(text, 2), normal / 2);
  assert.equal(estimateMs('', 1), 0);
});
