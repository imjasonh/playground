import assert from 'node:assert/strict';
import test from 'node:test';

import {IDBFactory} from 'fake-indexeddb';

import {CONVERSATION_VERSION, newConversation} from '../src/history.js';
import {DB_NAME, openStore} from '../src/store.js';

function record(id, updatedAt, fields = {}) {
  return {...newConversation({id, now: updatedAt}), ...fields};
}

function readRaw(factory) {
  return new Promise((resolve, reject) => {
    const request = factory.open(DB_NAME);
    request.onsuccess = () => {
      const db = request.result;
      const all = db
        .transaction('conversations')
        .objectStore('conversations')
        .getAll();
      all.onsuccess = () => {
        db.close();
        resolve(all.result);
      };
      all.onerror = () => reject(all.error);
    };
    request.onerror = () => reject(request.error);
  });
}

test('put, list, and delete round-trip conversations', async () => {
  const store = await openStore(new IDBFactory());
  await store.put(record('old', 1, {title: 'Old'}));
  await store.put(record('new', 3, {title: 'New'}));
  await store.put(record('mid', 2, {title: 'Mid'}));
  assert.deepEqual(
    (await store.list()).map((r) => r.id),
    ['new', 'mid', 'old'],
  );

  await store.put(record('old', 4, {title: 'Old, updated'}));
  const [first] = await store.list();
  assert.equal(first.id, 'old');
  assert.equal(first.title, 'Old, updated');

  await store.delete('mid');
  assert.deepEqual(
    (await store.list()).map((r) => r.id),
    ['old', 'new'],
  );
  store.close();
});

test('writes are committed when their promise resolves', async () => {
  const factory = new IDBFactory();
  const store = await openStore(factory);
  await store.put(record('a', 1));
  store.close();
  assert.deepEqual(
    (await readRaw(factory)).map((r) => r.id),
    ['a'],
  );
});

test('list skips records it cannot read and leaves them stored', async () => {
  const factory = new IDBFactory();
  const store = await openStore(factory);
  await store.put(record('ok', 1));
  await store.put(record('future', 2, {version: CONVERSATION_VERSION + 1}));
  assert.deepEqual(
    (await store.list()).map((r) => r.id),
    ['ok'],
  );
  store.close();

  const raw = await readRaw(factory);
  assert.deepEqual(raw.map((r) => r.id).sort(), ['future', 'ok']);
});

test('list upgrades older records it can read', async () => {
  const store = await openStore(new IDBFactory());
  const v1 = {...record('legacy', 1), version: 1};
  delete v1.summary;
  await store.put(v1);
  const [upgraded] = await store.list();
  assert.equal(upgraded.version, CONVERSATION_VERSION);
  assert.equal(upgraded.summary, null);
  store.close();
});

test('conversations keep attachment blobs', async () => {
  const store = await openStore(new IDBFactory());
  const image = new Blob(['png bytes'], {type: 'image/png'});
  await store.put(
    record('a', 1, {
      messages: [
        {
          role: 'user',
          text: 'Look',
          attachments: [{kind: 'image', name: 'a.png', file: image, text: null}],
        },
      ],
    }),
  );
  const [saved] = await store.list();
  const file = saved.messages[0].attachments[0].file;
  assert.equal(await file.text(), 'png bytes');
  assert.equal(file.type, 'image/png');
  store.close();
});
