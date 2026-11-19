import assert from 'node:assert/strict';
import {test} from 'node:test';

import {
  decodeDoc,
  encodeDoc,
  readReceipt,
  receiptHash,
  sign,
} from '../src/receipt.js';

const DOC = '# Plan\n\nShip it **Friday**. Ünïcödé and emoji 🚀 survive.\n';

test('encodeDoc and decodeDoc round-trip, URL-safe', async () => {
  const encoded = await encodeDoc(DOC);
  assert.match(encoded, /^[A-Za-z0-9_-]+$/);
  assert.equal(await decodeDoc(encoded), DOC);
});

test('encodeDoc compresses repetitive docs', async () => {
  const doc = 'All work and no play. '.repeat(500);
  const encoded = await encodeDoc(doc);
  assert.ok(encoded.length < doc.length / 20, `${encoded.length} chars`);
  assert.equal(await decodeDoc(encoded), doc);
});

test('encodeDoc handles docs larger than one fromCharCode chunk', async () => {
  const doc = Array.from({length: 40000}, (_, i) => `w${i * 7919}`).join(' ');
  assert.equal(await decodeDoc(await encodeDoc(doc)), doc);
});

test('decodeDoc rejects text that is not a doc', async () => {
  await assert.rejects(decodeDoc('not base64!'));
  await assert.rejects(decodeDoc('AAAA'));
});

test('sign depends on the doc and the time', async () => {
  const proof = await sign(DOC, 90);
  assert.match(proof, /^[0-9a-f]{32}$/);
  assert.equal(await sign(DOC, 90), proof);
  assert.notEqual(await sign(DOC, 91), proof);
  assert.notEqual(await sign(`${DOC} `, 90), proof);
});

test('readReceipt verifies a receipt from receiptHash', async () => {
  const hash = await receiptHash(DOC, 252);
  assert.deepEqual(await readReceipt(`#${hash}`), {
    markdown: DOC,
    seconds: 252,
    verified: true,
  });
});

test('readReceipt flags an edited time', async () => {
  const params = new URLSearchParams(await receiptHash(DOC, 252));
  params.set('t', '10');
  const receipt = await readReceipt(params.toString());
  assert.equal(receipt?.verified, false);
  assert.equal(receipt?.markdown, DOC);
});

test('readReceipt flags an edited doc', async () => {
  const params = new URLSearchParams(await receiptHash(DOC, 252));
  params.set('d', await encodeDoc(DOC.replace('Friday', 'Monday')));
  const receipt = await readReceipt(params.toString());
  assert.equal(receipt?.verified, false);
  assert.match(receipt?.markdown ?? '', /Monday/);
});

test('readReceipt flags a missing or malformed proof', async () => {
  const params = new URLSearchParams(await receiptHash(DOC, 5));
  params.delete('p');
  assert.equal((await readReceipt(params.toString()))?.verified, false);
  params.set('p', 'x');
  params.set('t', '5.0');
  assert.equal((await readReceipt(params.toString()))?.verified, false);
});

test('readReceipt returns null without a doc', async () => {
  assert.equal(await readReceipt(''), null);
  assert.equal(await readReceipt('#'), null);
  assert.equal(await readReceipt('#t=1&p=abc'), null);
});

test('readReceipt throws on a damaged doc', async () => {
  await assert.rejects(readReceipt('#d=%%%'));
});
