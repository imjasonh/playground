/**
 * Fetch one GTFS-realtime feed and decode it. The transport (fetch) and proxy
 * are both injectable so this is unit-testable without a network, and so the UI
 * can swap in a different proxy at runtime.
 */

import { buildFetchUrl } from './proxy.js';
import { decodeFeedMessage } from './gtfsRealtime.js';

/** Error carrying a coarse `kind` so the UI can explain failures helpfully. */
export class FeedError extends Error {
  /** @param {string} message @param {'network'|'http'|'decode'} kind @param {*} [cause] */
  constructor(message, kind, cause) {
    super(message);
    this.name = 'FeedError';
    this.kind = kind;
    if (cause !== undefined) this.cause = cause;
  }
}

/**
 * @param {{url: string, proxyTemplate?: string, fetchImpl?: typeof fetch, signal?: AbortSignal}} options
 * @returns {Promise<{message: object, byteLength: number, requestUrl: string}>}
 */
export async function fetchFeed({ url, proxyTemplate = '', fetchImpl, signal } = {}) {
  const doFetch = fetchImpl || (typeof fetch !== 'undefined' ? fetch.bind(globalThis) : null);
  if (!doFetch) throw new FeedError('No fetch implementation available', 'network');

  const requestUrl = buildFetchUrl(proxyTemplate, url);

  let response;
  try {
    response = await doFetch(requestUrl, {
      signal,
      headers: { Accept: 'application/x-protobuf, application/octet-stream, */*' },
    });
  } catch (err) {
    if (err && err.name === 'AbortError') throw err;
    throw new FeedError(`Network request failed: ${err && err.message ? err.message : err}`, 'network', err);
  }

  if (!response.ok) {
    throw new FeedError(`Feed request failed (HTTP ${response.status})`, 'http');
  }

  let bytes;
  try {
    bytes = new Uint8Array(await response.arrayBuffer());
  } catch (err) {
    throw new FeedError(`Could not read feed body: ${err && err.message ? err.message : err}`, 'network', err);
  }

  let message;
  try {
    message = decodeFeedMessage(bytes);
  } catch (err) {
    throw new FeedError(`Could not decode GTFS-realtime data: ${err && err.message ? err.message : err}`, 'decode', err);
  }

  return { message, byteLength: bytes.length, requestUrl };
}
