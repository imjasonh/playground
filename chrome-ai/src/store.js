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

  function objects(mode) {
    return db.transaction(CONVERSATIONS, mode).objectStore(CONVERSATIONS);
  }

  return {
    /** Returns the readable conversations, most recently updated first. */
    async list() {
      const records = await settle(objects('readonly').getAll());
      return records
        .map((record) => migrate(record))
        .filter((record) => record !== null)
        .sort((a, b) => b.updatedAt - a.updatedAt);
    },
    async put(record) {
      await settle(objects('readwrite').put(record));
    },
    async delete(id) {
      await settle(objects('readwrite').delete(id));
    },
    close() {
      db.close();
    },
  };
}
