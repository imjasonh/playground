// The saved conversation record, its versions, and how a saved conversation
// turns back into prompt messages.
//
// A record looks like this:
//
//   {
//     version: 1,
//     id: string,
//     title: string,
//     createdAt: number,  // milliseconds since the epoch
//     updatedAt: number,
//     messages: [{
//       role: 'user' | 'assistant',
//       text: string,  // Markdown for assistant messages
//       attachments: [{kind, name, file: ?Blob, text: ?string}],
//     }],
//   }
//
// To change the format, bump CONVERSATION_VERSION and add a step to
// MIGRATIONS that upgrades a record from the previous version.

import {userContent} from './attachments.js';

export const CONVERSATION_VERSION = 1;

/** Maps a version to a function that upgrades a record to the next one. */
const MIGRATIONS = Object.freeze({});

const TITLE_LENGTH = 60;
const UNTITLED = 'New chat';

/**
 * Returns an empty conversation record.
 * @param {{id: string, now: number}} fields
 * @return {!Object}
 */
export function newConversation({id, now}) {
  return {
    version: CONVERSATION_VERSION,
    id,
    title: UNTITLED,
    createdAt: now,
    updatedAt: now,
    messages: [],
  };
}

/**
 * Returns a title from the first user message: its text, cut to 60
 * characters, or else the name of its first attachment.
 * @param {!Array<!Object>} messages
 * @return {string}
 */
export function titleFor(messages) {
  const first = messages.find((m) => m.role === 'user');
  if (!first) {
    return UNTITLED;
  }
  const text = first.text.replace(/\s+/g, ' ').trim();
  if (text === '') {
    return first.attachments[0]?.name ?? UNTITLED;
  }
  if (text.length <= TITLE_LENGTH) {
    return text;
  }
  return `${text.slice(0, TITLE_LENGTH - 1).trimEnd()}…`;
}

/**
 * Returns the part of an attachment to save. Text files keep their text and
 * drop the file; images and audio keep the file.
 * @param {{kind: string, name: string, file: ?Blob, text: ?string}} attachment
 * @return {{kind: string, name: string, file: ?Blob, text: ?string}}
 */
export function storedAttachment({kind, name, file, text}) {
  if (kind === 'text') {
    return {kind, name, file: null, text};
  }
  return {kind, name, file, text: null};
}

/**
 * Upgrades a stored record to `current`. Returns null when the record isn't
 * a conversation, has no upgrade path, or comes from a newer version of the
 * app; callers skip those records and leave them in storage.
 * @param {*} record
 * @param {{migrations: (!Object|undefined), current: (number|undefined)}=}
 *     options
 * @return {?Object}
 */
export function migrate(
  record,
  {migrations = MIGRATIONS, current = CONVERSATION_VERSION} = {},
) {
  if (!Number.isInteger(record?.version)) {
    return null;
  }
  let upgraded = record;
  while (upgraded.version < current) {
    const step = migrations[upgraded.version];
    if (!step) {
      return null;
    }
    upgraded = step(upgraded);
  }
  return upgraded.version === current ? upgraded : null;
}

/**
 * Turns saved messages into Prompt API messages. An image or audio
 * attachment that `media` doesn't include becomes a note in the text.
 * @param {!Array<!Object>} messages
 * @param {!Array<string>} media The media types the session accepts.
 * @return {!Array<{role: string, content: (string|!Array<!Object>)}>}
 */
export function toPromptMessages(messages, media) {
  return messages.map((message) => {
    if (message.role === 'assistant') {
      return {role: 'assistant', content: message.text};
    }
    const usable = message.attachments.filter(
      (a) => a.kind === 'text' || media.includes(a.kind),
    );
    const notes = message.attachments
      .filter((a) => !usable.includes(a))
      .map((a) => `[The user attached ${a.name}, which isn't available.]`);
    const text = [...notes, message.text].filter(Boolean).join('\n\n');
    return {role: 'user', content: userContent(text, usable)};
  });
}

/**
 * Formats when a conversation was last updated: the time for today, the
 * month and day for this year, and the full date before that.
 * @param {number} timestamp
 * @param {number} now
 * @param {string=} locale
 * @return {string}
 */
export function formatWhen(timestamp, now, locale = undefined) {
  const date = new Date(timestamp);
  const today = new Date(now);
  let options = {year: 'numeric', month: 'short', day: 'numeric'};
  if (date.toDateString() === today.toDateString()) {
    options = {hour: 'numeric', minute: '2-digit'};
  } else if (date.getFullYear() === today.getFullYear()) {
    options = {month: 'short', day: 'numeric'};
  }
  return new Intl.DateTimeFormat(locale, options).format(date);
}
