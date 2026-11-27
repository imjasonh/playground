import assert from 'node:assert/strict';
import test from 'node:test';

import {Narrator} from '../src/narrator.js';
import {Player} from '../src/player.js';
import {FakeSynth, FakeTimer, FakeUtterance} from './fakes.js';

function setup(cuesPerSlide) {
  const synth = new FakeSynth();
  const timer = new FakeTimer();
  const narrator = new Narrator({synth, Utterance: FakeUtterance, timer});
  const deck = {slides: cuesPerSlide.map((cues) => ({notes: '', cues}))};
  const player = new Player(deck, narrator, {timer, gapMs: 500, holdMs: 2000});
  const slides = [];
  player.addEventListener('slide', (e) => slides.push(e.detail.index));
  return {synth, timer, narrator, player, slides};
}

test('playback narrates each slide and advances after a gap', () => {
  const {synth, timer, player, slides} = setup([['A1.', 'A2.'], ['B1.']]);
  let finished = false;
  player.addEventListener('finished', () => (finished = true));
  player.play();
  synth.finish();
  synth.finish();
  assert.equal(player.index, 0);
  timer.tick(500);
  assert.deepEqual(slides, [1]);
  synth.finish();
  assert.equal(finished, true);
  assert.equal(player.playing, false);
  assert.deepEqual(synth.texts, ['A1.', 'A2.', 'B1.']);
});

test('navigating during the gap does not also auto-advance', () => {
  const {synth, timer, player} = setup([['A.'], ['B.'], ['C.']]);
  player.play();
  synth.finish();
  player.next();
  assert.equal(player.index, 1);
  timer.tick(5000);
  assert.equal(player.index, 1);
  assert.deepEqual(synth.texts, ['A.', 'B.']);
});

test('navigating mid-cue stops the old narration', () => {
  const {synth, timer, player} = setup([['A.'], ['B.'], ['C.']]);
  player.play();
  player.goTo(2);
  assert.deepEqual(synth.texts, ['A.', 'C.']);
  synth.finish();
  timer.tick(5000);
  assert.equal(player.index, 2);
  assert.equal(player.playing, false);
});

test('pause and play resume at the interrupted cue', () => {
  const {synth, player} = setup([['A1.', 'A2.', 'A3.']]);
  player.play();
  synth.finish();
  player.pause();
  assert.equal(player.playing, false);
  player.play();
  assert.deepEqual(synth.texts, ['A1.', 'A2.', 'A2.']);
});

test('pausing between slides resumes on the next slide', () => {
  const {synth, player} = setup([['A.'], ['B.']]);
  player.play();
  synth.finish();
  player.pause();
  player.play();
  assert.equal(player.index, 1);
  assert.deepEqual(synth.texts, ['A.', 'B.']);
});

test('play after the last slide finishes starts over', () => {
  const {synth, player} = setup([['A.'], ['B.']]);
  player.goTo(1);
  player.play();
  synth.finish();
  player.play();
  assert.equal(player.index, 0);
  assert.deepEqual(synth.texts, ['B.', 'A.']);
});

test('a slide without notes holds, scaled by speed, then advances', () => {
  const {synth, timer, player, narrator} = setup([[], ['B.']]);
  narrator.setRate(2);
  player.play();
  timer.tick(999);
  assert.equal(player.index, 0);
  timer.tick(1 + 250);
  assert.equal(player.index, 1);
  assert.deepEqual(synth.texts, ['B.']);
});

test('navigating while paused does not speak', () => {
  const {synth, player} = setup([['A.'], ['B.']]);
  player.next();
  player.prev();
  assert.equal(synth.spoken.length, 0);
});

test('playCue starts the current slide at that cue', () => {
  const {synth, player} = setup([['A1.', 'A2.', 'A3.']]);
  player.playCue(2);
  assert.equal(player.playing, true);
  assert.deepEqual(synth.texts, ['A3.']);
});

test('goTo clamps to the deck', () => {
  const {player} = setup([['A.'], ['B.']]);
  player.goTo(99);
  assert.equal(player.index, 1);
  player.goTo(-3);
  assert.equal(player.index, 0);
});
