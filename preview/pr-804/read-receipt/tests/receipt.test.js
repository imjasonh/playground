import assert from 'node:assert/strict';
import {test} from 'node:test';

import {
  decodeDoc,
  encodeDoc,
  longestLink,
  readReceipt,
  receiptFragment,
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

// 2026-11-19T02:58:00Z
const FINISHED = 1795057080;

test('sign depends on the doc, the time, and the finish', async () => {
  const proof = await sign(DOC, 90, FINISHED);
  assert.match(proof, /^[0-9a-f]{32}$/);
  assert.equal(await sign(DOC, 90, FINISHED), proof);
  assert.notEqual(await sign(DOC, 91, FINISHED), proof);
  assert.notEqual(await sign(DOC, 90, FINISHED + 1), proof);
  assert.notEqual(await sign(`${DOC} `, 90, FINISHED), proof);
});

test('readReceipt verifies a receipt from receiptFragment', async () => {
  const hash = await receiptFragment(DOC, 252, FINISHED);
  assert.deepEqual(await readReceipt(`#${hash}`), {
    markdown: DOC,
    reading: {seconds: 252, finished: new Date('2026-11-19T02:58:00Z')},
  });
});

test('readReceipt verifies a version 1 receipt, which has no finish', async () => {
  const hash =
    'v=1&t=42&p=77c4af98083ee0a412cccb030b113f51' +
    '&d=U1bwz0nh4nJUKEstKs7Mz1MwVChKTU7NLCjR4wIA';
  assert.deepEqual(await readReceipt(hash), {
    markdown: '# Old\n\nA version 1 receipt.\n',
    reading: {seconds: 42, finished: null},
  });
  const params = new URLSearchParams(hash);
  params.set('f', String(FINISHED));
  assert.equal((await readReceipt(params.toString()))?.reading?.finished, null);
});

test('readReceipt flags an edited time', async () => {
  const params = new URLSearchParams(await receiptFragment(DOC, 252, FINISHED));
  params.set('t', '10');
  const receipt = await readReceipt(params.toString());
  assert.deepEqual(receipt, {markdown: DOC, reading: null});
});

test('readReceipt flags an edited or missing finish', async () => {
  const params = new URLSearchParams(await receiptFragment(DOC, 252, FINISHED));
  params.set('f', String(FINISHED - 86400));
  assert.deepEqual(await readReceipt(params.toString()), {
    markdown: DOC,
    reading: null,
  });
  params.delete('f');
  assert.equal((await readReceipt(params.toString()))?.reading, null);
});

test('readReceipt flags a downgrade to version 1', async () => {
  const params = new URLSearchParams(await receiptFragment(DOC, 252, FINISHED));
  params.set('v', '1');
  assert.equal((await readReceipt(params.toString()))?.reading, null);
});

test('readReceipt flags an edited doc', async () => {
  const params = new URLSearchParams(await receiptFragment(DOC, 252, FINISHED));
  params.set('d', await encodeDoc(DOC.replace('Friday', 'Monday')));
  const receipt = await readReceipt(params.toString());
  assert.equal(receipt?.reading, null);
  assert.match(receipt?.markdown ?? '', /Monday/);
});

test('readReceipt flags a missing or malformed proof', async () => {
  const params = new URLSearchParams(await receiptFragment(DOC, 5, FINISHED));
  params.delete('p');
  assert.equal((await readReceipt(params.toString()))?.reading, null);
  params.set('p', 'x');
  params.set('t', '5.0');
  assert.equal((await readReceipt(params.toString()))?.reading, null);
});

test('longestLink covers any reading time and finish time', async () => {
  const base = 'https://example.com/read-receipt/';
  const longest = await longestLink(base, DOC);
  const real = `${base}#${await receiptFragment(DOC, 12_345_678, FINISHED)}`;
  assert.ok(real.length <= longest, `${real.length} > ${longest}`);
  const most = '9'.repeat(15);
  const params = new URLSearchParams(await receiptFragment(DOC, 0, 0));
  params.set('t', most);
  params.set('f', most);
  assert.equal(longest, `${base}#${params}`.length);
});

test('readReceipt returns null without a doc', async () => {
  assert.equal(await readReceipt(''), null);
  assert.equal(await readReceipt('#'), null);
  assert.equal(await readReceipt('#t=1&p=abc'), null);
});

test('readReceipt throws on a damaged doc', async () => {
  await assert.rejects(readReceipt('#d=%%%'));
});
