import {
  buildCreateBody,
  extractAgentsList,
  needsAttention,
  normalizeAgent,
  relativeTime,
  sortAgents,
  statusTone,
} from './api.js';

const state = {
  agents: [],
  selectedId: null,
  me: null,
  models: [],
  repos: [],
  mode: 'live',
  version: '0.1.0',
  pollTimer: null,
  modalMode: 'create', // create | followup
};

const els = {
  rail: document.getElementById('agentRail'),
  detail: document.getElementById('detail'),
  agentCount: document.getElementById('agentCount'),
  selectedMeta: document.getElementById('selectedMeta'),
  connPill: document.getElementById('connPill'),
  connLabel: document.getElementById('connLabel'),
  refreshBtn: document.getElementById('refreshBtn'),
  cycleBtn: document.getElementById('cycleBtn'),
  newBtn: document.getElementById('newBtn'),
  modalBackdrop: document.getElementById('modalBackdrop'),
  newForm: document.getElementById('newForm'),
  modalTitle: document.getElementById('modalTitle'),
  promptInput: document.getElementById('promptInput'),
  repoInput: document.getElementById('repoInput'),
  refInput: document.getElementById('refInput'),
  modelInput: document.getElementById('modelInput'),
  repoList: document.getElementById('repoList'),
  cancelModalBtn: document.getElementById('cancelModalBtn'),
  submitModalBtn: document.getElementById('submitModalBtn'),
  toast: document.getElementById('toast'),
  versionLabel: document.getElementById('versionLabel'),
};

function bridge() {
  return window.XeneonCursor || null;
}

async function api(path, options = {}) {
  const b = bridge();
  if (b?.request) {
    return b.request(path, options);
  }

  const res = await fetch(`/api${path}`, {
    method: options.method || 'GET',
    headers: {
      Accept: 'application/json',
      ...(options.body ? { 'Content-Type': 'application/json' } : {}),
      ...(options.headers || {}),
    },
    body: options.body ? JSON.stringify(options.body) : undefined,
  });

  const text = await res.text();
  let data = null;
  try {
    data = text ? JSON.parse(text) : null;
  } catch {
    data = { raw: text };
  }

  if (!res.ok) {
    const msg = data?.message || data?.error || `HTTP ${res.status}`;
    throw new Error(msg);
  }
  return data;
}

function setConn(kind, label) {
  els.connPill.classList.remove('ok', 'warn', 'err');
  if (kind) els.connPill.classList.add(kind);
  els.connLabel.textContent = label;
}

function toast(message, isError = false) {
  els.toast.textContent = message;
  els.toast.classList.toggle('error', isError);
  els.toast.classList.add('show');
  clearTimeout(toast._t);
  toast._t = setTimeout(() => els.toast.classList.remove('show'), 2800);
}

function selectedAgent() {
  return state.agents.find((a) => a.id === state.selectedId) || null;
}

function renderRail() {
  const agents = sortAgents(state.agents);
  els.agentCount.textContent = `${agents.length} agent${agents.length === 1 ? '' : 's'}`;

  if (!agents.length) {
    els.rail.innerHTML = `<div class="empty-rail">No cloud agents yet. Tap <strong>New agent</strong> to launch one.</div>`;
    return;
  }

  els.rail.innerHTML = agents
    .map((agent) => {
      const tone = statusTone(agent.status);
      const selected = agent.id === state.selectedId ? 'selected' : '';
      const attention = needsAttention(agent);
      return `
        <button class="agent-card ${selected}" type="button" data-id="${escapeAttr(agent.id)}">
          <div class="row">
            <span class="status ${tone}">${escapeHtml(agent.status)}</span>
            <span class="chip">${escapeHtml(relativeTime(agent.updatedAt || agent.createdAt) || '—')}</span>
          </div>
          <div>
            <h3>${escapeHtml(agent.name)}</h3>
            <p class="summary">${escapeHtml(agent.summary || 'No summary yet.')}</p>
          </div>
          <div class="chips">
            <span class="chip">${escapeHtml(agent.repoLabel)}</span>
            ${agent.model ? `<span class="chip">${escapeHtml(agent.model)}</span>` : ''}
            ${attention ? `<span class="chip attention">needs you</span>` : ''}
          </div>
        </button>
      `;
    })
    .join('');

  for (const card of els.rail.querySelectorAll('.agent-card')) {
    card.addEventListener('click', () => {
      state.selectedId = card.dataset.id;
      render();
    });
  }
}

function renderDetail() {
  const agent = selectedAgent();
  if (!agent) {
    els.selectedMeta.textContent = 'Tap a card';
    els.detail.innerHTML = `<div class="detail-empty">Select an agent to follow up, cancel, or open in Cursor.</div>`;
    return;
  }

  els.selectedMeta.textContent = agent.id;
  const tone = statusTone(agent.status);
  const canCancel = ['RUNNING', 'CREATING', 'WAITING_FOR_BACKGROUND_WORK', 'ACTIVE'].includes(
    String(agent.status).toUpperCase(),
  );

  els.detail.innerHTML = `
    <div class="row">
      <span class="status ${tone}">${escapeHtml(agent.status)}</span>
      <span class="chip">${escapeHtml(relativeTime(agent.updatedAt || agent.createdAt) || '')}</span>
    </div>
    <div>
      <h3>${escapeHtml(agent.name)}</h3>
      <p class="summary">${escapeHtml(agent.summary || 'No summary yet.')}</p>
    </div>
    <div class="chips">
      <span class="chip">${escapeHtml(agent.repoLabel)}</span>
      ${agent.branch ? `<span class="chip">${escapeHtml(agent.branch)}</span>` : ''}
      ${agent.model ? `<span class="chip">${escapeHtml(agent.model)}</span>` : ''}
    </div>
    <div class="stream" id="detailStream">${escapeHtml(agent.summary || 'Live stream attaches when a run is active.')}</div>
    <div class="action-grid">
      <button class="btn primary" type="button" data-action="open-desktop">Open in Cursor</button>
      <button class="btn" type="button" data-action="open-web">Open web</button>
      <button class="btn" type="button" data-action="followup">Follow-up</button>
      <button class="btn" type="button" data-action="pr" ${agent.prUrl ? '' : 'disabled'}>Open PR</button>
      <button class="btn danger" type="button" data-action="cancel" ${canCancel ? '' : 'disabled'}>Cancel run</button>
      <button class="btn ghost" type="button" data-action="archive">Archive</button>
    </div>
  `;

  for (const btn of els.detail.querySelectorAll('[data-action]')) {
    btn.addEventListener('click', () => handleAction(btn.dataset.action, agent));
  }
}

function render() {
  renderRail();
  renderDetail();
}

async function handleAction(action, agent) {
  try {
    if (action === 'open-desktop') {
      await openExternal(agent.desktopUrl || agent.url);
      return;
    }
    if (action === 'open-web') {
      await openExternal(agent.url);
      return;
    }
    if (action === 'pr') {
      if (agent.prUrl) await openExternal(agent.prUrl);
      return;
    }
    if (action === 'followup') {
      openModal('followup');
      return;
    }
    if (action === 'cancel') {
      await api(`/agents/${encodeURIComponent(agent.id)}/cancel`, { method: 'POST' });
      toast('Cancel requested');
      await refreshAgents();
      return;
    }
    if (action === 'archive') {
      await api(`/agents/${encodeURIComponent(agent.id)}/archive`, { method: 'POST' });
      toast('Archived');
      state.selectedId = null;
      await refreshAgents();
    }
  } catch (err) {
    toast(err.message || String(err), true);
  }
}

async function openExternal(url) {
  const b = bridge();
  if (b?.openExternal) {
    await b.openExternal(url);
    return;
  }
  window.open(url, '_blank', 'noopener,noreferrer');
}

function openModal(mode) {
  state.modalMode = mode;
  els.modalTitle.textContent = mode === 'followup' ? 'Follow-up' : 'New cloud agent';
  els.submitModalBtn.textContent = mode === 'followup' ? 'Send' : 'Launch';
  els.promptInput.value = '';
  els.repoInput.disabled = mode === 'followup';
  els.refInput.disabled = mode === 'followup';
  els.modelInput.disabled = mode === 'followup';
  els.modalBackdrop.classList.add('open');
  // Focus the prompt so a Mac keyboard can type immediately after the tap that opened the modal.
  requestAnimationFrame(() => {
    els.promptInput.focus({ preventScroll: true });
  });
}

function closeModal() {
  els.modalBackdrop.classList.remove('open');
}

async function refreshAgents() {
  const data = await api('/agents');
  state.agents = extractAgentsList(data).map((a) => normalizeAgent(a.raw || a) || a);
  if (state.selectedId && !state.agents.some((a) => a.id === state.selectedId)) {
    state.selectedId = null;
  }
  if (!state.selectedId && state.agents.length) {
    state.selectedId = sortAgents(state.agents)[0].id;
  }
  render();
}

async function bootstrap() {
  try {
    const health = await api('/health');
    state.mode = health.mode || 'live';
    state.version = health.version || state.version;
    els.versionLabel.textContent = `v${state.version}${state.mode === 'mock' ? ' · mock' : ''}`;

    if (health.configured === false && state.mode !== 'mock') {
      setConn('warn', 'Set API key');
    } else {
      setConn('ok', state.mode === 'mock' ? 'Mock mode' : 'Connected');
    }

    try {
      state.me = await api('/me');
      if (state.me?.userEmail) {
        setConn('ok', state.me.userEmail);
      }
    } catch {
      // optional
    }

    try {
      const models = await api('/models');
      state.models = models.models || [];
      els.modelInput.innerHTML =
        `<option value="">Default</option>` +
        state.models.map((m) => `<option value="${escapeAttr(m)}">${escapeHtml(m)}</option>`).join('');
    } catch {
      // optional
    }

    try {
      const repos = await api('/repositories');
      state.repos = repos.repositories || [];
      els.repoList.innerHTML = state.repos
        .map((r) => `<option value="${escapeAttr(r.repository || r.url || '')}"></option>`)
        .join('');
    } catch {
      // optional / rate-limited
    }

    await refreshAgents();
  } catch (err) {
    setConn('err', 'Offline');
    toast(err.message || String(err), true);
    render();
  }
}

function cycleNeedingAttention() {
  const needing = sortAgents(state.agents).filter(needsAttention);
  if (!needing.length) {
    toast('Nothing needs you right now');
    return;
  }
  const idx = needing.findIndex((a) => a.id === state.selectedId);
  const next = needing[(idx + 1) % needing.length];
  state.selectedId = next.id;
  render();
  const card = els.rail.querySelector(`[data-id="${CSS.escape(next.id)}"]`);
  card?.scrollIntoView({ behavior: 'smooth', inline: 'center', block: 'nearest' });
}

els.refreshBtn.addEventListener('click', async () => {
  try {
    await refreshAgents();
    toast('Refreshed');
  } catch (err) {
    toast(err.message || String(err), true);
  }
});

els.cycleBtn.addEventListener('click', cycleNeedingAttention);
els.newBtn.addEventListener('click', () => openModal('create'));
els.cancelModalBtn.addEventListener('click', closeModal);
els.modalBackdrop.addEventListener('click', (e) => {
  if (e.target === els.modalBackdrop) closeModal();
});

els.newForm.addEventListener('submit', async (e) => {
  e.preventDefault();
  try {
    if (state.modalMode === 'followup') {
      const agent = selectedAgent();
      if (!agent) throw new Error('No agent selected');
      await api(`/agents/${encodeURIComponent(agent.id)}/runs`, {
        method: 'POST',
        body: { prompt: { text: els.promptInput.value.trim() } },
      });
      toast('Follow-up sent');
    } else {
      const body = buildCreateBody({
        prompt: els.promptInput.value,
        repository: els.repoInput.value.trim() || undefined,
        ref: els.refInput.value.trim() || 'main',
        model: els.modelInput.value || undefined,
        autoCreatePR: true,
      });
      const created = await api('/agents', { method: 'POST', body });
      const agent = normalizeAgent(created.agent || created);
      if (agent) state.selectedId = agent.id;
      toast('Agent launched');
    }
    closeModal();
    await refreshAgents();
  } catch (err) {
    toast(err.message || String(err), true);
  }
});

document.addEventListener('keydown', (e) => {
  if (e.key === 'Escape') closeModal();
  if ((e.key === 'n' || e.key === 'N') && !e.metaKey && !e.ctrlKey && document.activeElement === document.body) {
    openModal('create');
  }
  if (e.key === ']' && !e.metaKey && !e.ctrlKey) cycleNeedingAttention();
});

function escapeHtml(value) {
  return String(value ?? '')
    .replaceAll('&', '&amp;')
    .replaceAll('<', '&lt;')
    .replaceAll('>', '&gt;')
    .replaceAll('"', '&quot;');
}

function escapeAttr(value) {
  return escapeHtml(value).replaceAll("'", '&#39;');
}

bootstrap();
state.pollTimer = setInterval(() => {
  refreshAgents().catch(() => {});
}, 15_000);

// Expose for native bridge / tests
window.__xeneon = { state, refreshAgents, render };
