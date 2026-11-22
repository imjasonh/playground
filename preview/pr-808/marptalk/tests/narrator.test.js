import assert from 'node:assert/strict';
import test from 'node:test';

import {Narrator} from '../src/narrator.js';
import {FakeSynth, FakeTimer, FakeUtterance} from './fakes.js';

function setup() {
  const synth = new FakeSynth();
  const timer = new FakeTimer();
  const narrator = new Narrator({synth, Utterance: FakeUtterance, timer});
  const events = [];
  for (const type of ['cue', 'end', 'speecherror']) {
    narrator.addEventListener(type, (e) =>
      events.push(e.detail ? [type, e.detail] : [type]),
    );
  }
  return {synth, timer, narrator, events};
}

test('speaks each cue in order and then ends', () => {
  const {synth, narrator, events} = setup();
  narrator.start(['One.', 'Two.']);
  assert.deepEqual(synth.texts, ['One.']);
  synth.finish();
  assert.deepEqual(synth.texts, ['One.', 'Two.']);
  synth.finish();
  assert.deepEqual(events, [
    ['cue', {index: 0, text: 'One.'}],
    ['cue', {index: 1, text: 'Two.'}],
    ['end'],
  ]);
  assert.equal(narrator.active, false);
});

test('pause cancels speech and resume repeats the paused cue', () => {
  const {synth, narrator, events} = setup();
  narrator.start(['One.', 'Two.']);
  synth.finish();
  narrator.pause();
  assert.equal(synth.speaking, false);
  // The interrupted utterance's events must not advance the narrator.
  assert.equal(narrator.index, 1);
  narrator.resume();
  assert.deepEqual(synth.texts, ['One.', 'Two.', 'Two.']);
  synth.finish();
  assert.deepEqual(events.at(-1), ['end']);
});

test('a rate change restarts the current cue at the new rate', () => {
  const {synth, narrator} = setup();
  narrator.start(['One.', 'Two.']);
  narrator.setRate(1.5);
  assert.deepEqual(synth.texts, ['One.', 'One.']);
  assert.equal(synth.spoken[1].rate, 1.5);
  synth.finish();
  assert.equal(synth.spoken[2].rate, 1.5);
});

test('a late end event from a stopped utterance is ignored', () => {
  const {synth, narrator, events} = setup();
  narrator.start(['One.', 'Two.']);
  const stale = synth.spoken[0];
  narrator.stop();
  narrator.start(['Other.']);
  stale.onend({});
  assert.deepEqual(synth.texts, ['One.', 'Other.']);
  assert.equal(events.filter(([t]) => t === 'end').length, 0);
});

test('a synthesis error shows the cue for its estimated length', () => {
  const {synth, timer, narrator, events} = setup();
  narrator.start(['Blocked by autoplay.', 'Next.']);
  synth.fail('not-allowed');
  assert.deepEqual(events[1], ['speecherror', {error: 'not-allowed'}]);
  assert.equal(synth.texts.length, 1);
  timer.tick(10000);
  assert.deepEqual(synth.texts, ['Blocked by autoplay.', 'Next.']);
});

test('a dropped utterance times out instead of stalling', () => {
  const {synth, timer, narrator} = setup();
  narrator.start(['Never ends.', 'Next.']);
  timer.tick(60000);
  assert.deepEqual(synth.texts, ['Never ends.', 'Next.']);
});

test('muted narration advances on estimated timing without speaking', () => {
  const {synth, timer, narrator, events} = setup();
  narrator.setMuted(true);
  narrator.start(['One two three.', 'Four five six.']);
  assert.equal(synth.spoken.length, 0);
  timer.tick(30000);
  assert.deepEqual(
    events.map(([t]) => t),
    ['cue', 'cue', 'end'],
  );
});

test('no speech synthesis falls back to timed captions', () => {
  const timer = new FakeTimer();
  const narrator = new Narrator({synth: null, Utterance: null, timer});
  let ended = false;
  narrator.addEventListener('end', () => (ended = true));
  narrator.start(['Hello there.']);
  assert.equal(narrator.muted, true);
  narrator.setMuted(false);
  assert.equal(narrator.muted, true);
  timer.tick(10000);
  assert.equal(ended, true);
});

test('network voices get a keepalive while speaking', () => {
  const {synth, timer, narrator} = setup();
  narrator.setVoice({lang: 'en-US', localService: false});
  narrator.start([
    'This cue runs long enough that a network voice would still be ' +
      'talking ten seconds after it began.',
  ]);
  timer.tick(10000);
  assert.equal(synth.pauses, 1);
  assert.equal(synth.paused, false);
  synth.finish();
  timer.tick(30000);
  assert.equal(synth.pauses, 1);
  assert.equal(timer.pending, 0);
});

test('word boundaries report the cue they belong to', () => {
  const {synth, narrator} = setup();
  const words = [];
  narrator.addEventListener('word', (e) => words.push(e.detail));
  narrator.start(['Hello world.']);
  synth.current.onboundary({name: 'word', charIndex: 6, charLength: 5});
  synth.current.onboundary({name: 'sentence', charIndex: 0, charLength: 12});
  assert.deepEqual(words, [{index: 0, charIndex: 6, charLength: 5}]);
});
