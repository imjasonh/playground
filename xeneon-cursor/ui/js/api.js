/**
 * Shared Cursor Cloud Agents API helpers (browser + Node).
 */

export const DEFAULT_API_BASE = 'https://api.cursor.com';

export function agentWebUrl(agentId) {
  return `https://cursor.com/agents/${encodeURIComponent(agentId)}`;
}

export function agentDesktopDeeplink(agentId) {
  return `cursor://anysphere.cursor-deeplink/background-agent?bcId=${encodeURIComponent(agentId)}`;
}

export function authHeaders(apiKey, extra = {}) {
  if (!apiKey) {
    throw new Error('Missing CURSOR_API_KEY');
  }
  return {
    Authorization: `Bearer ${apiKey}`,
    Accept: 'application/json',
    ...extra,
  };
}

export function normalizeAgent(raw) {
  if (!raw || typeof raw !== 'object') return null;
  const id = raw.id || raw.agentId || null;
  if (!id) return null;

  const status =
    raw.status ||
    raw.latestRun?.status ||
    raw.currentRun?.status ||
    'UNKNOWN';

  const repos = Array.isArray(raw.repos)
    ? raw.repos
    : raw.source?.repository
      ? [{ url: raw.source.repository, startingRef: raw.source.ref }]
      : [];

  const repoLabel = repos[0]
    ? repoShortName(repos[0].url || repos[0].repository)
    : raw.source?.repository
      ? repoShortName(raw.source.repository)
      : 'no-repo';

  const prUrl =
    raw.prUrl ||
    raw.target?.prUrl ||
    raw.git?.pullRequests?.[0]?.url ||
    null;

  const branch =
    raw.target?.branchName ||
    raw.git?.branches?.[0]?.name ||
    null;

  return {
    id,
    name: raw.name || 'Untitled agent',
    status: String(status).toUpperCase(),
    summary: raw.summary || raw.latestRun?.summary || '',
    createdAt: raw.createdAt || raw.created_at || null,
    updatedAt: raw.updatedAt || raw.updated_at || null,
    model: raw.model?.id || raw.model || null,
    repos,
    repoLabel,
    prUrl,
    branch,
    url: raw.url || agentWebUrl(id),
    desktopUrl: agentDesktopDeeplink(id),
    archived: Boolean(raw.archived || raw.isArchived),
    raw,
  };
}

export function repoShortName(url) {
  if (!url) return 'repo';
  try {
    const cleaned = String(url).replace(/\.git$/, '');
    const parts = cleaned.split('/').filter(Boolean);
    if (parts.length >= 2) {
      return `${parts[parts.length - 2]}/${parts[parts.length - 1]}`;
    }
  } catch {
    // fall through
  }
  return String(url);
}

export function statusTone(status) {
  const s = String(status || '').toUpperCase();
  if (['RUNNING', 'CREATING', 'ACTIVE', 'WAITING_FOR_BACKGROUND_WORK'].includes(s)) {
    return 'live';
  }
  if (['FINISHED', 'COMPLETED', 'IDLE'].includes(s)) {
    return 'done';
  }
  if (['ERROR', 'FAILED', 'EXPIRED'].includes(s)) {
    return 'error';
  }
  if (['ARCHIVED'].includes(s)) {
    return 'muted';
  }
  return 'idle';
}

export function needsAttention(agent) {
  const s = String(agent?.status || '').toUpperCase();
  return ['IDLE', 'FINISHED', 'COMPLETED', 'ERROR', 'FAILED'].includes(s);
}

export function sortAgents(agents) {
  const rank = (a) => {
    const s = String(a.status || '').toUpperCase();
    if (['RUNNING', 'CREATING', 'WAITING_FOR_BACKGROUND_WORK'].includes(s)) return 0;
    if (['IDLE', 'FINISHED', 'COMPLETED'].includes(s)) return 1;
    if (['ERROR', 'FAILED'].includes(s)) return 2;
    return 3;
  };
  return [...agents].sort((a, b) => {
    const d = rank(a) - rank(b);
    if (d !== 0) return d;
    const at = Date.parse(a.updatedAt || a.createdAt || 0) || 0;
    const bt = Date.parse(b.updatedAt || b.createdAt || 0) || 0;
    return bt - at;
  });
}

export function extractAgentsList(payload) {
  if (!payload) return [];
  const list = payload.agents || payload.items || payload.data || [];
  if (!Array.isArray(list)) return [];
  return list.map(normalizeAgent).filter(Boolean);
}

export function buildCreateBody({ prompt, repository, ref = 'main', model, autoCreatePR = true }) {
  const text = String(prompt || '').trim();
  if (!text) throw new Error('Prompt is required');

  const body = {
    prompt: { text },
    autoCreatePR: Boolean(autoCreatePR),
  };

  if (repository) {
    body.repos = [
      {
        url: repository,
        startingRef: ref || 'main',
      },
    ];
  }

  if (model) {
    body.model = typeof model === 'string' ? { id: model } : model;
  }

  return body;
}

export function relativeTime(iso, now = Date.now()) {
  if (!iso) return '';
  const t = Date.parse(iso);
  if (Number.isNaN(t)) return '';
  const delta = Math.max(0, now - t);
  const sec = Math.floor(delta / 1000);
  if (sec < 60) return `${sec}s ago`;
  const min = Math.floor(sec / 60);
  if (min < 60) return `${min}m ago`;
  const hr = Math.floor(min / 60);
  if (hr < 48) return `${hr}h ago`;
  const day = Math.floor(hr / 24);
  return `${day}d ago`;
}
