import assert from 'node:assert/strict';
import test from 'node:test';

import {
  MAX_TEXT_BYTES,
  acceptList,
  buildPrompt,
  checkFile,
  extensionOf,
  fileKind,
} from '../src/attachments.js';

function file(name, type, size = 10) {
  return {name, type, size};
}

test('extensionOf lowercases and ignores dotfiles', () => {
  assert.equal(extensionOf('Notes.MD'), 'md');
  assert.equal(extensionOf('archive.tar.gz'), 'gz');
  assert.equal(extensionOf('.bashrc'), '');
  assert.equal(extensionOf('Makefile'), '');
});

test('fileKind sorts files by how the model takes them', () => {
  assert.equal(fileKind(file('cat.png', 'image/png')), 'image');
  assert.equal(fileKind(file('memo.m4a', 'audio/mp4')), 'audio');
  assert.equal(fileKind(file('notes.txt', 'text/plain')), 'text');
  assert.equal(fileKind(file('data.json', 'application/json')), 'text');
  assert.equal(fileKind(file('main.go', '')), 'text');
  assert.equal(fileKind(file('main.rs', 'application/rls-services+xml')), 'text');
  assert.equal(fileKind(file('logo.svg', 'image/svg+xml')), 'text');
  assert.equal(fileKind(file('paper.pdf', 'application/pdf')), null);
  assert.equal(fileKind(file('clip.mp4', 'video/mp4')), null);
});

test('checkFile rejects unsupported kinds, media, and large text', () => {
  assert.deepEqual(checkFile(file('cat.png', 'image/png'), ['image']), {
    kind: 'image',
  });
  assert.match(
    checkFile(file('cat.png', 'image/png'), []).error,
    /cat\.png: .*doesn't accept images/,
  );
  assert.match(
    checkFile(file('memo.wav', 'audio/wav'), ['image']).error,
    /doesn't accept audio/,
  );
  assert.match(
    checkFile(file('paper.pdf', 'application/pdf'), ['image']).error,
    /paper\.pdf: the model can't read/,
  );
  assert.deepEqual(
    checkFile(file('big.txt', 'text/plain', MAX_TEXT_BYTES), []),
    {kind: 'text'},
  );
  assert.match(
    checkFile(file('big.txt', 'text/plain', MAX_TEXT_BYTES + 1), []).error,
    /512 KB/,
  );
});

test('acceptList offers media only when the device takes it', () => {
  const textOnly = acceptList([]).split(',');
  assert.ok(textOnly.includes('text/*'));
  assert.ok(textOnly.includes('.md'));
  assert.ok(!textOnly.includes('image/*'));
  const all = acceptList(['image', 'audio']).split(',');
  assert.ok(all.includes('image/*'));
  assert.ok(all.includes('audio/*'));
});

test('buildPrompt returns plain text without attachments', () => {
  assert.equal(buildPrompt('hello', []), 'hello');
});

test('buildPrompt orders text files, media, then the typed text', () => {
  const image = new Blob(['png']);
  const audio = new Blob(['wav']);
  const prompt = buildPrompt('Compare these.', [
    {kind: 'image', name: 'a.png', file: image, text: null},
    {kind: 'text', name: 'notes.md', file: new Blob(), text: '# Notes'},
    {kind: 'audio', name: 'b.wav', file: audio, text: null},
  ]);
  assert.deepEqual(prompt, [
    {
      role: 'user',
      content: [
        {type: 'text', value: 'Contents of the file notes.md:\n\n# Notes'},
        {type: 'image', value: image},
        {type: 'audio', value: audio},
        {type: 'text', value: 'Compare these.'},
      ],
    },
  ]);
});

test('buildPrompt leaves out empty typed text', () => {
  const image = new Blob(['png']);
  assert.deepEqual(
    buildPrompt('', [{kind: 'image', name: 'a.png', file: image, text: null}]),
    [{role: 'user', content: [{type: 'image', value: image}]}],
  );
});
