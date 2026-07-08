import assert from 'node:assert/strict';
import test from 'node:test';
import {
  agentDesktopDeeplink,
  agentWebUrl,
  buildCreateBody,
  extractAgentsList,
  needsAttention,
  normalizeAgent,
  relativeTime,
  repoShortName,
  sortAgents,
  statusTone,
} from '../ui/js/api.js';
import { createCursorProxyHandler } from '../server/handler.mjs';
import { mockListAgents } from '../ui/js/mock.js';

test('agent URLs and deeplinks', () => {
  assert.equal(
    agentWebUrl('bc-abc'),
    'https://cursor.com/agents/bc-abc',
  );
  assert.equal(
    agentDesktopDeeplink('bc-abc'),
    'cursor://anysphere.cursor-deeplink/background-agent?bcId=bc-abc',
  );
});

test('normalizeAgent maps v1-ish payloads', () => {
  const agent = normalizeAgent({
    id: 'bc-1',
    name: 'Hello',
    status: 'RUNNING',
    repos: [{ url: 'https://github.com/acme/payments' }],
    model: { id: 'composer-2.5' },
    target: { prUrl: 'https://github.com/acme/payments/pull/1', branchName: 'cursor/x' },
  });
  assert.equal(agent.id, 'bc-1');
  assert.equal(agent.repoLabel, 'acme/payments');
  assert.equal(agent.model, 'composer-2.5');
  assert.equal(agent.prUrl, 'https://github.com/acme/payments/pull/1');
  assert.equal(agent.desktopUrl, agentDesktopDeeplink('bc-1'));
});

test('sortAgents prioritizes live work', () => {
  const sorted = sortAgents([
    normalizeAgent({ id: 'a', name: 'a', status: 'FINISHED' }),
    normalizeAgent({ id: 'b', name: 'b', status: 'RUNNING' }),
    normalizeAgent({ id: 'c', name: 'c', status: 'ERROR' }),
  ]);
  assert.deepEqual(
    sorted.map((a) => a.id),
    ['b', 'a', 'c'],
  );
});

test('needsAttention and statusTone', () => {
  assert.equal(needsAttention({ status: 'IDLE' }), true);
  assert.equal(needsAttention({ status: 'RUNNING' }), false);
  assert.equal(statusTone('RUNNING'), 'live');
  assert.equal(statusTone('ERROR'), 'error');
});

test('buildCreateBody validates prompt', () => {
  assert.throws(() => buildCreateBody({ prompt: '  ' }), /Prompt is required/);
  const body = buildCreateBody({
    prompt: 'Ship it',
    repository: 'https://github.com/acme/x',
    ref: 'main',
    model: 'composer-2.5',
  });
  assert.equal(body.prompt.text, 'Ship it');
  assert.equal(body.repos[0].url, 'https://github.com/acme/x');
  assert.equal(body.model.id, 'composer-2.5');
});

test('repoShortName and relativeTime', () => {
  assert.equal(repoShortName('https://github.com/acme/payments.git'), 'acme/payments');
  const now = Date.parse('2026-07-08T12:00:00Z');
  assert.equal(relativeTime('2026-07-08T11:59:30Z', now), '30s ago');
  assert.equal(relativeTime('2026-07-08T11:00:00Z', now), '1h ago');
});

test('extractAgentsList accepts agents or items', () => {
  const fromAgents = extractAgentsList(mockListAgents());
  assert.ok(fromAgents.length >= 3);
  const fromItems = extractAgentsList({
    items: [{ id: 'bc-x', name: 'X', status: 'IDLE' }],
  });
  assert.equal(fromItems[0].id, 'bc-x');
});

test('mock proxy health and list agents', async () => {
  const handler = createCursorProxyHandler({
    forceMock: true,
    version: '0.1.0',
  });
  assert.equal(handler.mode(), 'mock');

  const health = await invoke(handler, 'GET', '/api/health');
  assert.equal(health.status, 200);
  assert.equal(health.body.mode, 'mock');
  assert.equal(health.body.version, '0.1.0');

  const list = await invoke(handler, 'GET', '/api/agents');
  assert.equal(list.status, 200);
  assert.ok(Array.isArray(list.body.agents));
  assert.ok(list.body.agents.length > 0);
});

test('mock proxy create + follow-up + cancel', async () => {
  const handler = createCursorProxyHandler({ forceMock: true, version: '0.1.0' });

  const created = await invoke(handler, 'POST', '/api/agents', {
    prompt: { text: 'Write tests' },
    repos: [{ url: 'https://github.com/acme/x', startingRef: 'main' }],
  });
  assert.equal(created.status, 200);
  const id = created.body.agent.id;
  assert.ok(id.startsWith('bc-demo-new-'));

  const follow = await invoke(handler, 'POST', `/api/agents/${id}/runs`, {
    prompt: { text: 'Also add docs' },
  });
  assert.equal(follow.status, 200);
  assert.equal(follow.body.run.status, 'RUNNING');

  const cancel = await invoke(handler, 'POST', `/api/agents/${id}/cancel`);
  assert.equal(cancel.status, 200);
  assert.equal(cancel.body.status, 'IDLE');
});

test('unconfigured live mode rejects without key', async () => {
  const handler = createCursorProxyHandler({
    apiKey: '',
    forceMock: false,
    mock: false,
    version: '0.1.0',
  });
  const res = await invoke(handler, 'GET', '/api/agents');
  assert.equal(res.status, 401);
  assert.equal(res.body.error, 'unconfigured');
});

async function invoke(handler, method, path, body) {
  const chunks = [];
  let statusCode = 200;
  const req = {
    method,
    async *[Symbol.asyncIterator]() {
      if (body != null) {
        yield Buffer.from(JSON.stringify(body));
      }
    },
  };
  const res = {
    writeHead(code) {
      statusCode = code;
    },
    end(payload) {
      chunks.push(Buffer.from(payload || ''));
    },
  };
  const url = new URL(path, 'http://127.0.0.1:8787');
  await handler(req, res, url);
  const raw = Buffer.concat(chunks).toString('utf8');
  return { status: statusCode, body: raw ? JSON.parse(raw) : null };
}
