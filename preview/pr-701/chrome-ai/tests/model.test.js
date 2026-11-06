import assert from 'node:assert/strict';
import test from 'node:test';

import {
  CHAT_OPTIONS,
  availabilityMessage,
  contextUsage,
  createSession,
  findLanguageModel,
  formatProgress,
  streamReply,
} from '../src/model.js';

function streamOf(chunks) {
  return new ReadableStream({
    start(c) {
      for (const chunk of chunks) {
        c.enqueue(chunk);
      }
      c.close();
    },
  });
}

class FakeSession extends EventTarget {
  constructor(chunks = []) {
    super();
    this.chunks = chunks;
    this.calls = [];
  }

  promptStreaming(text, options) {
    this.calls.push({text, options});
    if (options?.signal?.aborted) {
      throw new DOMException('Aborted', 'AbortError');
    }
    return streamOf(this.chunks);
  }
}

function fakeApi({session = new FakeSession(), progress = []} = {}) {
  return {
    createOptions: null,
    availability: async () => 'available',
    async create(options) {
      this.createOptions = options;
      const monitor = new EventTarget();
      options.monitor?.(monitor);
      for (const loaded of progress) {
        const e = new Event('downloadprogress');
        e.loaded = loaded;
        monitor.dispatchEvent(e);
      }
      return session;
    },
  };
}

test('findLanguageModel returns the API only when it is complete', () => {
  const api = fakeApi();
  assert.equal(findLanguageModel({LanguageModel: api}), api);
  assert.equal(findLanguageModel({}), null);
  assert.equal(findLanguageModel(undefined), null);
  assert.equal(findLanguageModel({LanguageModel: {create() {}}}), null);
});

test('availabilityMessage covers each state', () => {
  assert.equal(availabilityMessage('available'), '');
  for (const status of [
    'unsupported',
    'unavailable',
    'downloadable',
    'downloading',
  ]) {
    assert.notEqual(availabilityMessage(status), '', status);
  }
  assert.match(availabilityMessage('later'), /later/);
});

test('formatProgress rounds and clamps the fraction', () => {
  assert.equal(formatProgress(0), 'Downloading model: 0%');
  assert.equal(formatProgress(0.426), 'Downloading model: 43%');
  assert.equal(formatProgress(1.2), 'Downloading model: 100%');
  assert.equal(formatProgress(-1), 'Downloading model: 0%');
});

test('createSession passes chat options and reports download progress', async () => {
  const seen = [];
  const api = fakeApi({progress: [0, 0.5, 1]});
  await createSession(api, {onProgress: (loaded) => seen.push(loaded)});
  assert.deepEqual(seen, [0, 0.5, 1]);
  assert.deepEqual(api.createOptions.expectedInputs, CHAT_OPTIONS.expectedInputs);
  assert.deepEqual(
    api.createOptions.expectedOutputs,
    CHAT_OPTIONS.expectedOutputs,
  );
});

test('createSession forwards both overflow event names', async () => {
  const session = new FakeSession();
  let overflows = 0;
  await createSession(fakeApi({session}), {onOverflow: () => overflows++});
  session.dispatchEvent(new Event('contextoverflow'));
  session.dispatchEvent(new Event('quotaoverflow'));
  assert.equal(overflows, 2);
});

test('streamReply joins chunks and reports the reply so far', async () => {
  const session = new FakeSession(['Hel', 'lo', ', world']);
  const seen = [];
  const controller = new AbortController();
  const reply = await streamReply(session, 'hi', {
    signal: controller.signal,
    onText: (text) => seen.push(text),
  });
  assert.equal(reply, 'Hello, world');
  assert.deepEqual(seen, ['Hel', 'Hello', 'Hello, world']);
  assert.equal(session.calls[0].text, 'hi');
  assert.equal(session.calls[0].options.signal, controller.signal);
});

test('streamReply rejects when the signal is already aborted', async () => {
  const controller = new AbortController();
  controller.abort();
  await assert.rejects(
    streamReply(new FakeSession(['x']), 'hi', {signal: controller.signal}),
    {name: 'AbortError'},
  );
});

test('contextUsage reads current and legacy property names', () => {
  assert.equal(
    contextUsage({contextUsage: 1234, contextWindow: 9216}),
    '1,234 of 9,216 tokens used',
  );
  assert.equal(
    contextUsage({inputUsage: 10, inputQuota: 6144}),
    '10 of 6,144 tokens used',
  );
  assert.equal(contextUsage({}), '');
  assert.equal(contextUsage(null), '');
});
