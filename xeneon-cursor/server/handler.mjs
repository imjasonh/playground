/**
 * Request handler for /api/* — shared by the Node proxy.
 */

import {
  mockArchive,
  mockCancel,
  mockCreateAgent,
  mockFollowUp,
  mockListAgents,
  mockMe,
  mockModels,
  mockRepositories,
} from '../ui/js/mock.js';

export function createCursorProxyHandler(options) {
  const {
    apiBase = 'https://api.cursor.com',
    version = '0.1.0',
  } = options;

  let apiKey = options.apiKey || '';
  let forceMock = Boolean(options.forceMock || options.mock);

  function mode() {
    if (forceMock) return 'mock';
    return apiKey ? 'live' : 'unconfigured';
  }

  function setApiKey(next) {
    apiKey = next || '';
  }

  async function handle(req, res, url) {
    const route = url.pathname.replace(/^\/api/, '') || '/';

    if (route === '/health') {
      return json(res, 200, {
        ok: true,
        mode: mode() === 'unconfigured' ? 'live' : mode(),
        configured: Boolean(apiKey) || forceMock,
        version,
        apiBase,
      });
    }

    if (forceMock || (!apiKey && options.mock)) {
      return handleMock(req, res, route);
    }

    if (!apiKey) {
      return json(res, 401, {
        error: 'unconfigured',
        message: 'Set CURSOR_API_KEY or run with --mock',
      });
    }

    return proxyToCursor(req, res, route);
  }

  async function handleMock(req, res, route) {
    const method = (req.method || 'GET').toUpperCase();
    const body = method === 'GET' || method === 'HEAD' ? null : await readJson(req);

    if (route === '/me' && method === 'GET') return json(res, 200, mockMe());
    if (route === '/models' && method === 'GET') return json(res, 200, mockModels());
    if (route === '/repositories' && method === 'GET') return json(res, 200, mockRepositories());
    if (route === '/agents' && method === 'GET') return json(res, 200, mockListAgents());
    if (route === '/agents' && method === 'POST') return json(res, 200, mockCreateAgent(body));

    const agentMatch = route.match(/^\/agents\/([^/]+)(?:\/(runs|cancel|archive))?$/);
    if (agentMatch) {
      const agentId = decodeURIComponent(agentMatch[1]);
      const action = agentMatch[2];
      if (!action && method === 'GET') {
        const list = mockListAgents().agents;
        const agent = list.find((a) => a.id === agentId);
        if (!agent) return json(res, 404, { error: 'not_found' });
        return json(res, 200, agent);
      }
      if (action === 'runs' && method === 'POST') {
        return json(res, 200, mockFollowUp(agentId, body));
      }
      if (action === 'cancel' && method === 'POST') {
        return json(res, 200, mockCancel(agentId));
      }
      if (action === 'archive' && method === 'POST') {
        return json(res, 200, mockArchive(agentId));
      }
    }

    return json(res, 404, { error: 'not_found', route });
  }

  async function proxyToCursor(req, res, route) {
    const method = (req.method || 'GET').toUpperCase();
    const bodyBuf =
      method === 'GET' || method === 'HEAD' ? null : Buffer.from(await readRaw(req));

    // Map friendly local routes onto Cloud Agents API v1 (with a few v0 fallbacks).
    const mapped = mapRoute(method, route, bodyBuf);
    if (mapped.error) {
      return json(res, mapped.status || 400, { error: mapped.error, message: mapped.message });
    }

    try {
      const upstream = await fetch(mapped.url, {
        method: mapped.method,
        headers: {
          Authorization: `Bearer ${apiKey}`,
          Accept: 'application/json',
          ...(mapped.body ? { 'Content-Type': 'application/json' } : {}),
        },
        body: mapped.body || undefined,
      });

      const text = await upstream.text();
      res.writeHead(upstream.status, {
        'Content-Type': upstream.headers.get('content-type') || 'application/json',
        'Cache-Control': 'no-store',
      });
      res.end(text);
    } catch (err) {
      return json(res, 502, {
        error: 'upstream_error',
        message: String(err?.message || err),
      });
    }
  }

  function mapRoute(method, route, bodyBuf) {
    if (route === '/me' && method === 'GET') {
      return { method: 'GET', url: `${apiBase}/v1/me` };
    }
    if (route === '/models' && method === 'GET') {
      return { method: 'GET', url: `${apiBase}/v1/models` };
    }
    if (route === '/repositories' && method === 'GET') {
      return { method: 'GET', url: `${apiBase}/v1/repositories` };
    }
    if (route === '/agents' && method === 'GET') {
      return { method: 'GET', url: `${apiBase}/v1/agents?limit=50` };
    }
    if (route === '/agents' && method === 'POST') {
      return { method: 'POST', url: `${apiBase}/v1/agents`, body: bodyBuf };
    }

    const agentMatch = route.match(/^\/agents\/([^/]+)(?:\/(runs|cancel|archive|unarchive))?$/);
    if (!agentMatch) {
      return { error: 'not_found', message: `Unknown route ${route}`, status: 404 };
    }

    const agentId = decodeURIComponent(agentMatch[1]);
    const action = agentMatch[2];

    if (!action && method === 'GET') {
      return { method: 'GET', url: `${apiBase}/v1/agents/${encodeURIComponent(agentId)}` };
    }
    if (action === 'runs' && method === 'POST') {
      return {
        method: 'POST',
        url: `${apiBase}/v1/agents/${encodeURIComponent(agentId)}/runs`,
        body: bodyBuf,
      };
    }
    if (action === 'cancel' && method === 'POST') {
      // Cancel the latest run when possible; clients may also pass runId in body.
      let runId = null;
      try {
        if (bodyBuf?.length) runId = JSON.parse(bodyBuf.toString('utf8'))?.runId;
      } catch {
        // ignore
      }
      if (runId) {
        return {
          method: 'POST',
          url: `${apiBase}/v1/agents/${encodeURIComponent(agentId)}/runs/${encodeURIComponent(runId)}/cancel`,
        };
      }
      // Fallback: stop via legacy v0 endpoint when run id is unknown.
      return {
        method: 'POST',
        url: `${apiBase}/v0/agents/${encodeURIComponent(agentId)}/stop`,
      };
    }
    if (action === 'archive' && method === 'POST') {
      return {
        method: 'POST',
        url: `${apiBase}/v1/agents/${encodeURIComponent(agentId)}/archive`,
      };
    }
    if (action === 'unarchive' && method === 'POST') {
      return {
        method: 'POST',
        url: `${apiBase}/v1/agents/${encodeURIComponent(agentId)}/unarchive`,
      };
    }

    return { error: 'not_found', message: `Unknown route ${route}`, status: 404 };
  }

  handle.mode = mode;
  handle.setApiKey = setApiKey;
  return handle;
}

function json(res, status, payload) {
  res.writeHead(status, {
    'Content-Type': 'application/json; charset=utf-8',
    'Cache-Control': 'no-store',
  });
  res.end(JSON.stringify(payload));
}

async function readRaw(req) {
  const chunks = [];
  for await (const chunk of req) chunks.push(chunk);
  return Buffer.concat(chunks);
}

async function readJson(req) {
  const raw = await readRaw(req);
  if (!raw.length) return null;
  try {
    return JSON.parse(raw.toString('utf8'));
  } catch {
    return null;
  }
}
