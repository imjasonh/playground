// Wrappers around Chrome's built-in Prompt API (the `LanguageModel` global).
// They take the API or a session as an argument so Node tests can pass fakes.

export const CHAT_OPTIONS = Object.freeze({
  expectedInputs: [{type: 'text', languages: ['en']}],
  expectedOutputs: [{type: 'text', languages: ['en']}],
});

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
 * @param {{onProgress: (function(number))|undefined,
 *     onOverflow: (function())|undefined}=} callbacks
 * @return {!Promise<object>}
 */
export async function createSession(api, {onProgress, onOverflow} = {}) {
  const session = await api.create({
    ...CHAT_OPTIONS,
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
 * Streams the model's reply to `text`. Calls `onText` with the reply so far
 * after each chunk, and resolves to the whole reply.
 * @param {object} session
 * @param {string} text
 * @param {{signal: (AbortSignal|undefined),
 *     onText: (function(string))|undefined}=} options
 * @return {!Promise<string>}
 */
export async function streamReply(session, text, {signal, onText} = {}) {
  let reply = '';
  for await (const chunk of session.promptStreaming(text, {signal})) {
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
