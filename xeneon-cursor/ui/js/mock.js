/**
 * Mock Cursor Cloud Agents API responses for offline / browser-only demos.
 */

import { agentDesktopDeeplink, agentWebUrl } from './api.js';

const now = Date.now();

function iso(offsetMs) {
  return new Date(now + offsetMs).toISOString();
}

export const MOCK_AGENTS = [
  {
    id: 'bc-demo-running-001',
    name: 'Fix flaky auth tests',
    status: 'RUNNING',
    summary: 'Reproducing CI failure and tightening wait helpers…',
    createdAt: iso(-25 * 60_000),
    updatedAt: iso(-30_000),
    model: { id: 'composer-2.5' },
    repos: [{ url: 'https://github.com/acme/payments', startingRef: 'main' }],
    url: agentWebUrl('bc-demo-running-001'),
    git: { branches: [{ name: 'cursor/fix-auth-tests' }] },
  },
  {
    id: 'bc-demo-idle-002',
    name: 'Add Xeneon HUD polish',
    status: 'IDLE',
    summary: 'Opened PR with touch-friendly agent cards. Waiting for review.',
    createdAt: iso(-3 * 60 * 60_000),
    updatedAt: iso(-12 * 60_000),
    model: { id: 'claude-4.5-sonnet-thinking' },
    repos: [{ url: 'https://github.com/imjasonh/playground', startingRef: 'main' }],
    url: agentWebUrl('bc-demo-idle-002'),
    target: {
      branchName: 'cursor/xeneon-cursor-manager',
      prUrl: 'https://github.com/imjasonh/playground/pull/99',
    },
  },
  {
    id: 'bc-demo-error-003',
    name: 'Migrate webhook handlers',
    status: 'ERROR',
    summary: 'Setup failed: missing CLOUDFLARE_API_TOKEN in environment.',
    createdAt: iso(-6 * 60 * 60_000),
    updatedAt: iso(-90 * 60_000),
    model: { id: 'gpt-5.5' },
    repos: [{ url: 'https://github.com/acme/edge-api', startingRef: 'main' }],
    url: agentWebUrl('bc-demo-error-003'),
  },
  {
    id: 'bc-demo-finished-004',
    name: 'Document Cloud Agents API',
    status: 'FINISHED',
    summary: 'Added README section and endpoint table.',
    createdAt: iso(-26 * 60 * 60_000),
    updatedAt: iso(-20 * 60 * 60_000),
    model: { id: 'composer-2.5' },
    repos: [{ url: 'https://github.com/acme/docs', startingRef: 'main' }],
    url: agentWebUrl('bc-demo-finished-004'),
    target: {
      prUrl: 'https://github.com/acme/docs/pull/12',
      branchName: 'cursor/docs-cloud-agents',
    },
  },
];

export function mockListAgents() {
  return {
    agents: MOCK_AGENTS.map((a) => ({
      ...a,
      desktopUrl: agentDesktopDeeplink(a.id),
    })),
    nextCursor: null,
  };
}

export function mockMe() {
  return {
    apiKeyName: 'Xeneon Cursor Manager (mock)',
    userEmail: 'you@example.com',
    createdAt: iso(-30 * 24 * 60 * 60_000),
  };
}

export function mockModels() {
  return {
    models: [
      'composer-2.5',
      'claude-4.5-sonnet-thinking',
      'gpt-5.5',
    ],
  };
}

export function mockRepositories() {
  return {
    repositories: [
      {
        owner: 'imjasonh',
        name: 'playground',
        repository: 'https://github.com/imjasonh/playground',
      },
      {
        owner: 'acme',
        name: 'payments',
        repository: 'https://github.com/acme/payments',
      },
    ],
  };
}

export function mockCreateAgent(body) {
  const id = `bc-demo-new-${Date.now().toString(36)}`;
  const agent = {
    id,
    name: body?.prompt?.text?.slice(0, 48) || 'New agent',
    status: 'CREATING',
    summary: 'Provisioning cloud VM…',
    createdAt: iso(0),
    updatedAt: iso(0),
    model: body?.model || { id: 'composer-2.5' },
    repos: body?.repos || [],
    url: agentWebUrl(id),
    autoCreatePR: body?.autoCreatePR ?? true,
  };
  MOCK_AGENTS.unshift(agent);
  return {
    agent,
    run: {
      id: `run-${id}`,
      status: 'CREATING',
      createdAt: iso(0),
    },
  };
}

export function mockFollowUp(agentId, body) {
  const agent = MOCK_AGENTS.find((a) => a.id === agentId);
  if (agent) {
    agent.status = 'RUNNING';
    agent.summary = `Follow-up: ${String(body?.prompt?.text || '').slice(0, 80)}`;
    agent.updatedAt = iso(0);
  }
  return {
    run: {
      id: `run-follow-${Date.now().toString(36)}`,
      status: 'RUNNING',
      agentId,
    },
  };
}

export function mockCancel(agentId) {
  const agent = MOCK_AGENTS.find((a) => a.id === agentId);
  if (agent) {
    agent.status = 'IDLE';
    agent.summary = 'Run cancelled from Xeneon HUD.';
    agent.updatedAt = iso(0);
  }
  return { id: agentId, status: 'IDLE' };
}

export function mockArchive(agentId) {
  const idx = MOCK_AGENTS.findIndex((a) => a.id === agentId);
  if (idx >= 0) MOCK_AGENTS.splice(idx, 1);
  return { id: agentId, archived: true };
}
