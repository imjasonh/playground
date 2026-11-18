// Saves conversations in IndexedDB, which can hold the image and audio
// attachments as Blobs. The database version covers the object stores;
// each record's own `version` covers its format (see history.js).

import {migrate} from './history.js';

export const DB_NAME = 'chrome-ai';
export const DB_VERSION = 1;
const CONVERSATIONS = 'conversations';

function settle(request) {
  return new Promise((resolve, reject) => {
    request.onsuccess = () => resolve(request.result);
    request.onerror = () => reject(request.error);
  });
}

// A write is durable once its transaction commits, not when its request
// succeeds.
function commit(transaction) {
  return new Promise((resolve, reject) => {
    transaction.oncomplete = () => resolve();
    transaction.onerror = () => reject(transaction.error);
    transaction.onabort = () => reject(transaction.error);
  });
}

function upgrade(db, oldVersion) {
  if (oldVersion < 1) {
    db.createObjectStore(CONVERSATIONS, {keyPath: 'id'});
  }
}

/**
 * Opens the conversation store.
 * @param {!IDBFactory} factory Usually `indexedDB`.
 * @return {!Promise<{list: function(): !Promise<!Array<!Object>>,
 *     put: function(!Object): !Promise<void>,
 *     delete: function(string): !Promise<void>,
 *     close: function()}>}
 */
export async function openStore(factory) {
  const request = factory.open(DB_NAME, DB_VERSION);
  request.onupgradeneeded = (e) => upgrade(request.result, e.oldVersion);
  const db = await settle(request);
  // Another tab with a newer version of the app needs this tab to let go.
  db.onversionchange = () => db.close();

  function write(change) {
    const transaction = db.transaction(CONVERSATIONS, 'readwrite');
    change(transaction.objectStore(CONVERSATIONS));
    return commit(transaction);
  }

  return {
    /** Returns the readable conversations, most recently updated first. */
    async list() {
      const records = await settle(
        db.transaction(CONVERSATIONS).objectStore(CONVERSATIONS).getAll(),
      );
      return records
        .map((record) => migrate(record))
        .filter((record) => record !== null)
        .sort((a, b) => b.updatedAt - a.updatedAt);
    },
    put(record) {
      return write((conversations) => conversations.put(record));
    },
    delete(id) {
      return write((conversations) => conversations.delete(id));
    },
    close() {
      db.close();
    },
  };
}
