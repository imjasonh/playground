// Wrappers around Chrome's built-in Prompt API (the `LanguageModel` global).
// They take the API or a session as an argument so Node tests can pass fakes.

/** Input types besides text that a session can accept. */
export const MEDIA_TYPES = Object.freeze(['image', 'audio']);

/**
 * Returns the options for `availability()` and `create()`. A session rejects
 * input types that it didn't declare here when it was created.
 * @param {!Array<string>=} media Entries from `MEDIA_TYPES`.
 * @return {!Object}
 */
export function chatOptions(media = []) {
  return {
    expectedInputs: [
      {type: 'text', languages: ['en']},
      ...media.map((type) => ({type})),
    ],
    expectedOutputs: [{type: 'text', languages: ['en']}],
  };
}

/**
 * Returns the entries of `MEDIA_TYPES` that the model accepts on this device,
 * including ones that still need a download.
 * @param {object} api The `LanguageModel` global.
 * @return {!Promise<!Array<string>>}
 */
export async function supportedMedia(api) {
  const results = await Promise.all(
    MEDIA_TYPES.map(async (type) => {
      try {
        const status = await api.availability(chatOptions([type]));
        return status === 'unavailable' ? null : type;
      } catch {
        return null;
      }
    }),
  );
  return results.filter((type) => type !== null);
}

/**
 * Returns the Prompt API from `scope`, or null when the browser lacks it.
 * @param {object} scope Usually `globalThis`.
 * @return {?object}
 */
export function findLanguageModel(scope) {
  const api = scope?.LanguageModel;
  if (
    api &&
    typeof api.availability === 'function' &&
    typeof api.create === 'function'
  ) {
    return api;
  }
  return null;
}

/**
 * Returns the status line for an availability state. `unsupported` means the
 * browser has no `LanguageModel` global at all.
 * @param {string} status
 * @return {string}
 */
export function availabilityMessage(status) {
  switch (status) {
    case 'unsupported':
      return (
        "This browser doesn't have Chrome's built-in language model. " +
        'Open this page in desktop Chrome with the Prompt API enabled.'
      );
    case 'unavailable':
      return "Chrome's built-in language model isn't available on this device.";
    case 'downloadable':
      return 'Chrome needs to download the model before you can chat.';
    case 'downloading':
      return 'Chrome is downloading the model.';
    case 'available':
      return '';
    default:
      return `Unknown model status: ${status}`;
  }
}

/**
 * Formats a `downloadprogress` event's `loaded` fraction (0 to 1).
 * @param {number} loaded
 * @return {string}
 */
export function formatProgress(loaded) {
  const percent = Math.round(Math.min(Math.max(loaded, 0), 1) * 100);
  return `Downloading model: ${percent}%`;
}

/**
 * Creates a chat session. Creating a session can start the model download,
 * which Chrome allows only during a user gesture.
 * @param {object} api The `LanguageModel` global.
 * @param {{media: (!Array<string>|undefined),
 *     onProgress: (function(number))|undefined,
 *     onOverflow: (function())|undefined}=} options
 * @return {!Promise<object>}
 */
export async function createSession(
  api,
  {media = [], onProgress, onOverflow} = {},
) {
  const session = await api.create({
    ...chatOptions(media),
    monitor(m) {
      m.addEventListener('downloadprogress', (e) => onProgress?.(e.loaded));
    },
  });
  if (onOverflow) {
    session.addEventListener('contextoverflow', onOverflow);
    // Chrome before the rename fires `quotaoverflow` instead.
    session.addEventListener('quotaoverflow', onOverflow);
  }
  return session;
}

/**
 * Streams the model's reply to `input`. Calls `onText` with the reply so far
 * after each chunk, and resolves to the whole reply.
 * @param {object} session
 * @param {string|!Array<!Object>} input A string or a list of messages.
 * @param {{signal: (AbortSignal|undefined),
 *     onText: (function(string))|undefined}=} options
 * @return {!Promise<string>}
 */
export async function streamReply(session, input, {signal, onText} = {}) {
  let reply = '';
  for await (const chunk of session.promptStreaming(input, {signal})) {
    reply += chunk;
    onText?.(reply);
  }
  return reply;
}

/**
 * Describes how much of the context window the session has used, or returns
 * an empty string when the session doesn't report it.
 * @param {object} session
 * @return {string}
 */
export function contextUsage(session) {
  const used = session?.contextUsage ?? session?.inputUsage;
  const total = session?.contextWindow ?? session?.inputQuota;
  if (!Number.isFinite(used) || !Number.isFinite(total)) {
    return '';
  }
  const fmt = (n) => n.toLocaleString('en-US');
  return `${fmt(used)} of ${fmt(total)} tokens used`;
}
