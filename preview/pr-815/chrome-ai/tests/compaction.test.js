import assert from 'node:assert/strict';
import test from 'node:test';

import {
  foldPoint,
  isOver,
  summarize,
  summarizerPrompts,
} from '../src/compaction.js';

function user(text) {
  return {role: 'user', text, attachments: []};
}

function assistant(text) {
  return {role: 'assistant', text, attachments: []};
}

test('isOver compares usage plus incoming tokens to a fraction', () => {
  const usage = {used: 600, total: 1000};
  assert.equal(isOver(usage, 0.7), false);
  assert.equal(isOver(usage, 0.6), true);
  assert.equal(isOver(usage, 0.9, 299), false);
  assert.equal(isOver(usage, 0.9, 300), true);
  assert.equal(isOver(null, 0.1), false);
});

test('foldPoint keeps the last exchanges and folds the rest', () => {
  const messages = [
    user('1'), assistant('1'),
    user('2'), assistant('2'),
    user('3'), assistant('3'),
  ];
  assert.equal(foldPoint(messages), 2);
  assert.equal(foldPoint(messages, {keep: 1}), 4);
  assert.equal(foldPoint(messages, {end: 4}), null);
  assert.equal(foldPoint(messages, {end: 4, keep: 1}), 2);
  assert.equal(foldPoint(messages, {from: 2}), null);
  assert.equal(foldPoint(messages, {from: 2, keep: 1}), 4);
  assert.equal(foldPoint([]), null);
});

test('foldPoint counts a user message without a reply as an exchange', () => {
  const messages = [user('1'), assistant('1'), user('2'), user('3')];
  assert.equal(foldPoint(messages), 2);
});

test('summarizerPrompts puts the previous summary in the instructions', () => {
  const transcript = [{role: 'user', content: 'hi'}];
  const [first, ...rest] = summarizerPrompts(null, transcript);
  assert.equal(first.role, 'system');
  assert.doesNotMatch(first.content, /already summarized/);
  assert.deepEqual(rest, transcript);

  const [withPrevious] = summarizerPrompts('They like tea.', transcript);
  assert.match(withPrevious.content, /already summarized[\s\S]*They like tea\./);
});

test('summarize prompts a separate session and destroys it', async () => {
  let created;
  let destroyed = false;
  const api = {
    async create(options) {
      created = options;
      return {
        prompt: async (text) => {
          assert.match(text, /Summarize/);
          return '  The user asked about tea.\n';
        },
        destroy: () => {
          destroyed = true;
        },
      };
    },
  };
  const text = await summarize(api, {
    media: ['image'],
    previous: 'Earlier notes.',
    messages: [user('Tea?'), assistant('Yes.')],
  });
  assert.equal(text, 'The user asked about tea.');
  assert.equal(destroyed, true);
  assert.equal(created.initialPrompts[0].role, 'system');
  assert.match(created.initialPrompts[0].content, /Earlier notes\./);
  assert.deepEqual(created.initialPrompts.slice(1), [
    {role: 'user', content: 'Tea?'},
    {role: 'assistant', content: 'Yes.'},
  ]);
  assert.deepEqual(
    created.expectedInputs.map((input) => input.type),
    ['text', 'image'],
  );
});

test('summarize works in pieces when the messages do not fit', async () => {
  const sessions = [];
  const api = {
    async create(options) {
      const [system, ...transcript] = options.initialPrompts;
      if (transcript.length > 2) {
        throw new DOMException('Too long', 'QuotaExceededError');
      }
      const previous = system.content.match(/follows\. .*\n\n(.*)$/s)?.[1];
      const session = {
        destroyed: false,
        prompt: async () =>
          [previous, ...transcript.map((m) => m.content)]
            .filter(Boolean)
            .join('+'),
        destroy() {
          this.destroyed = true;
        },
      };
      sessions.push(session);
      return session;
    },
  };
  const messages = ['a', 'b', 'c', 'd', 'e', 'f'].map((text, i) =>
    i % 2 === 0 ? user(text) : assistant(text),
  );
  const text = await summarize(api, {media: [], previous: 'p', messages});
  assert.equal(text, 'p+a+b+c+d+e+f');
  assert.ok(sessions.every((s) => s.destroyed));
});

test('summarize gives up on a single message that cannot fit', async () => {
  const api = {
    async create(options) {
      if (options.initialPrompts.length > 1) {
        throw new DOMException('Too long', 'QuotaExceededError');
      }
      return {prompt: async () => 'unused', destroy() {}};
    },
  };
  assert.equal(
    await summarize(api, {media: [], previous: 'p', messages: [user('huge')]}),
    'p',
  );
});

test('summarize destroys the session when the prompt fails', async () => {
  let destroyed = false;
  const api = {
    create: async () => ({
      prompt: async () => {
        throw new DOMException('Stopped', 'AbortError');
      },
      destroy: () => {
        destroyed = true;
      },
    }),
  };
  await assert.rejects(
    summarize(api, {media: [], previous: null, messages: [user('a')]}),
    {name: 'AbortError'},
  );
  assert.equal(destroyed, true);
});
