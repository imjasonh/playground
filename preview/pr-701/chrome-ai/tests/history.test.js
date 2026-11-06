import assert from 'node:assert/strict';
import test from 'node:test';

import {
  CONVERSATION_VERSION,
  formatWhen,
  migrate,
  newConversation,
  storedAttachment,
  titleFor,
  toPromptMessages,
} from '../src/history.js';

function user(text, attachments = []) {
  return {role: 'user', text, attachments};
}

function assistant(text) {
  return {role: 'assistant', text, attachments: []};
}

test('newConversation starts empty at the current version', () => {
  assert.deepEqual(newConversation({id: 'a', now: 5}), {
    version: CONVERSATION_VERSION,
    id: 'a',
    title: 'New chat',
    createdAt: 5,
    updatedAt: 5,
    messages: [],
  });
});

test('titleFor uses the first user message', () => {
  assert.equal(titleFor([]), 'New chat');
  assert.equal(titleFor([user('  What is\n\nPrompt API? ')]), 'What is Prompt API?');
  const long = titleFor([user('x'.repeat(100))]);
  assert.equal(long.length, 60);
  assert.ok(long.endsWith('…'));
  assert.equal(
    titleFor([user('', [{kind: 'image', name: 'cat.png'}])]),
    'cat.png',
  );
});

test('storedAttachment keeps text for text files and blobs for media', () => {
  const file = new Blob(['x']);
  assert.deepEqual(
    storedAttachment({kind: 'text', name: 'a.md', file, text: '# A', url: 'u'}),
    {kind: 'text', name: 'a.md', file: null, text: '# A'},
  );
  assert.deepEqual(
    storedAttachment({kind: 'image', name: 'a.png', file, text: null, url: 'u'}),
    {kind: 'image', name: 'a.png', file, text: null},
  );
});

test('migrate passes current records through and skips unknown ones', () => {
  const record = newConversation({id: 'a', now: 1});
  assert.equal(migrate(record), record);
  assert.equal(migrate({...record, version: CONVERSATION_VERSION + 1}), null);
  assert.equal(migrate({id: 'a'}), null);
  assert.equal(migrate(null), null);
});

test('migrate runs each step up to the current version', () => {
  const migrations = {
    1: (r) => ({...r, version: 2, title: r.name}),
    2: (r) => ({...r, version: 3, tags: []}),
  };
  assert.deepEqual(
    migrate({version: 1, name: 'old'}, {migrations, current: 3}),
    {version: 3, name: 'old', title: 'old', tags: []},
  );
  assert.equal(migrate({version: 0}, {migrations, current: 3}), null);
});

test('toPromptMessages rebuilds user content and assistant replies', () => {
  const image = new Blob(['png']);
  const messages = [
    user('Describe this.', [
      {kind: 'image', name: 'a.png', file: image, text: null},
      {kind: 'text', name: 'n.md', file: null, text: 'notes'},
    ]),
    assistant('A **cat**.'),
    user('Thanks'),
  ];
  assert.deepEqual(toPromptMessages(messages, ['image']), [
    {
      role: 'user',
      content: [
        {type: 'text', value: 'Contents of the file n.md:\n\nnotes'},
        {type: 'image', value: image},
        {type: 'text', value: 'Describe this.'},
      ],
    },
    {role: 'assistant', content: 'A **cat**.'},
    {role: 'user', content: 'Thanks'},
  ]);
});

test('toPromptMessages notes media the session no longer accepts', () => {
  const messages = [
    user('Listen.', [
      {kind: 'audio', name: 'memo.wav', file: new Blob(), text: null},
    ]),
  ];
  assert.deepEqual(toPromptMessages(messages, []), [
    {
      role: 'user',
      content: "[The user attached memo.wav, which isn't available.]\n\nListen.",
    },
  ]);
});

test('formatWhen shows the time today and the date otherwise', () => {
  const now = new Date(2026, 10, 6, 15, 30).getTime();
  assert.match(
    formatWhen(new Date(2026, 10, 6, 9, 5).getTime(), now, 'en-US'),
    /^9:05\sAM$/u,
  );
  assert.equal(
    formatWhen(new Date(2026, 2, 14).getTime(), now, 'en-US'),
    'Mar 14',
  );
  assert.equal(
    formatWhen(new Date(2025, 11, 31).getTime(), now, 'en-US'),
    'Dec 31, 2025',
  );
});
