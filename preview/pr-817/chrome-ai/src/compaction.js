// Keeps long chats inside the context window. When a session fills up, the
// model summarizes the older messages, and a new session starts from that
// summary plus the most recent exchanges.

import {toPromptMessages} from './history.js';
import {restoreSession} from './model.js';

/** Compact after a reply once the session holds this much of its window. */
export const COMPACT_AFTER = 0.7;

/** Compact before a message that would push the session past this. */
export const COMPACT_BEFORE = 0.9;

/** Exchanges kept word for word after a compaction. */
export const KEEP_EXCHANGES = 2;

const SUMMARIZER_INSTRUCTIONS =
  'You condense chat transcripts. Summarize the conversation so that an ' +
  'assistant can continue it without the transcript. Keep facts, names, ' +
  "numbers, decisions, code, the user's goals and preferences, open " +
  'questions, and what any attached files, images, or audio contained. ' +
  'Write terse notes in the third person, under 250 words. Reply with the ' +
  'summary only.';

/**
 * Reports whether a session holding `used` of `total` tokens, plus `incoming`
 * more, has passed `limit` (a fraction of the window).
 * @param {?{used: number, total: number}} usage
 * @param {number} limit
 * @param {number=} incoming
 * @return {boolean}
 */
export function isOver(usage, limit, incoming = 0) {
  if (!usage) {
    return false;
  }
  return usage.used + incoming >= usage.total * limit;
}

/**
 * Returns the index of the first message to keep word for word: the start of
 * the last `keep` exchanges in messages[from, end). Returns null when that
 * leaves nothing before it to summarize.
 * @param {!Array<{role: string}>} messages
 * @param {{from: (number|undefined), end: (number|undefined),
 *     keep: (number|undefined)}=} options
 * @return {?number}
 */
export function foldPoint(
  messages,
  {from = 0, end = messages.length, keep = KEEP_EXCHANGES} = {},
) {
  let seen = 0;
  for (let i = end - 1; i >= from; i--) {
    if (messages[i].role === 'user') {
      seen++;
      if (seen === keep) {
        return i > from ? i : null;
      }
    }
  }
  return null;
}

/**
 * Returns the initial prompts for the summarizer session: instructions that
 * include the previous summary, then the messages to fold into it.
 * @param {?string} previous The summary so far, if any.
 * @param {!Array<!Object>} transcript Prompt API messages.
 * @return {!Array<!Object>}
 */
export function summarizerPrompts(previous, transcript) {
  const instructions = previous
    ? `${SUMMARIZER_INSTRUCTIONS}\n\nThe conversation before this ` +
      `transcript was already summarized as follows. Fold it into your ` +
      `summary.\n\n${previous}`
    : SUMMARIZER_INSTRUCTIONS;
  return [{role: 'system', content: instructions}, ...transcript];
}

/**
 * Asks the model for a summary of `messages`, merged with `previous`. Uses a
 * separate session, which it destroys before it returns. When the messages
 * don't fit in one session, summarizes the oldest ones first and folds the
 * rest into that summary.
 * @param {object} api The `LanguageModel` global.
 * @param {{media: !Array<string>, previous: ?string,
 *     messages: !Array<!Object>, signal: (AbortSignal|undefined)}} options
 *     `messages` are saved messages, as in history.js.
 * @return {!Promise<string>}
 */
export async function summarize(api, {media, previous, messages, signal}) {
  const prompts = summarizerPrompts(
    previous,
    toPromptMessages(messages, media),
  );
  const {session, dropped} = await restoreSession(api, prompts, {media});
  if (dropped > 0) {
    session.destroy();
    if (messages.length === 1) {
      // One message too long for a whole session; nothing to summarize it in.
      return previous ?? '';
    }
    const split = dropped < messages.length ? dropped : messages.length >> 1;
    const head = await summarize(api, {
      media,
      previous,
      messages: messages.slice(0, split),
      signal,
    });
    return summarize(api, {
      media,
      previous: head,
      messages: messages.slice(split),
      signal,
    });
  }
  try {
    const text = await session.prompt(
      'Summarize the conversation so far.',
      {signal},
    );
    return text.trim();
  } finally {
    session.destroy();
  }
}
