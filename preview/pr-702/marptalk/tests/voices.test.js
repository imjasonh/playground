import assert from 'node:assert/strict';
import test from 'node:test';

import {pickVoice, voicesFor} from '../src/voices.js';

const voices = [
  {name: 'Alex', lang: 'en-US', voiceURI: 'alex', default: true},
  {name: 'Daniel', lang: 'en-GB', voiceURI: 'daniel'},
  {name: 'Google US English', lang: 'en-US', voiceURI: 'google-us'},
  {name: 'Ava (Premium)', lang: 'en_US', voiceURI: 'ava'},
  {name: 'Amélie', lang: 'fr-CA', voiceURI: 'amelie'},
];

test('voicesFor keeps the deck language and ranks quality voices first', () => {
  const names = voicesFor(voices, 'en-US').map((v) => v.name);
  assert.deepEqual(names, [
    'Ava (Premium)',
    'Google US English',
    'Alex',
    'Daniel',
  ]);
});

test('voicesFor falls back to every voice when none match', () => {
  assert.equal(voicesFor(voices, 'ja-JP').length, voices.length);
});

test('pickVoice prefers the saved voice when it suits the deck', () => {
  assert.equal(pickVoice(voices, 'en-US', 'daniel').name, 'Daniel');
  assert.equal(pickVoice(voices, 'fr-FR', 'daniel').name, 'Amélie');
  assert.equal(pickVoice([], 'en-US'), null);
});
