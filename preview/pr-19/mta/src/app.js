/**
 * App shell: wires the DOM to the pure data modules.
 *
 * Data flow each refresh:
 *   pick feeds for the selected complex (+ the alerts feed)
 *     -> fetch (live) or synthesize (sample) -> decode GTFS-realtime
 *     -> buildArrivals / buildServiceStatus / buildTrains
 *     -> render.
 *
 * Live mode goes through a CORS proxy (MTA feeds have no CORS headers); if every
 * line feed fails and we have nothing on screen yet, we fall back to sample data
 * so the page is never empty. A visibility-aware poller drives auto-refresh.
 */

import { routeStyle } from './routes.js';
import { COMPLEXES, complexById, searchComplexes } from './stations.js';
import { feedsForRoutes, feedUrl, ALERTS_FEED } from './feeds.js';
import { decodeFeedMessage } from './gtfsRealtime.js';
import { buildArrivals } from './arrivals.js';
import { buildServiceStatus } from './status.js';
import { buildTrains } from './trains.js';
import { buildSampleLineFeed, buildSampleAlertsFeed } from './sampleFeed.js';
import { fetchFeed } from './client.js';
import { PROXY_PRESETS } from './proxy.js';
import { createPoller } from './poller.js';
import { freshness, pluralize } from './format.js';

const STORAGE = { mode: 'mta.mode', proxy: 'mta.proxy', complex: 'mta.complex' };
const DEFAULT_COMPLEX_ID = '611'; // Times Sq–42 St / Port Authority
const REFRESH_MS = 20000;

const el = {
  dataMode: document.getElementById('data-mode'),
  lastUpdated: document.getElementById('last-updated'),
  refresh: document.getElementById('refresh-btn'),
  error: document.getElementById('error'),
  search: document.getElementById('station-search'),
  results: document.getElementById('station-results'),
  chips: document.getElementById('station-chips'),
  settings: document.getElementById('settings'),
  proxyField: document.getElementById('proxy-field'),
  proxySelect: document.getElementById('proxy-select'),
  proxyCustomField: document.getElementById('proxy-custom-field'),
  proxyCustom: document.getElementById('proxy-custom'),
  stationName: document.getElementById('station-name'),
  stationMeta: document.getElementById('station-meta'),
  arrivals: document.getElementById('arrivals'),
  routeStatus: document.getElementById('route-status'),
  statusUpdated: document.getElementById('status-updated'),
  trains: document.getElementById('trains'),
  trainsSummary: document.getElementById('trains-summary'),
  alerts: document.getElementById('alerts'),
  alertsSummary: document.getElementById('alerts-summary'),
};

const state = {
  mode: 'sample',
  proxyTemplate: PROXY_PRESETS[0].template,
  complex: complexById(DEFAULT_COMPLEX_ID) || searchComplexes('')[0] || COMPLEXES[0],
  status: null,
  arrivals: null,
  trains: null,
  lastUpdated: null,
  source: 'sample',
  error: null,
  loading: false,
  alertFilter: null,
  requestId: 0,
};

let poller = null;

/* ---------------- settings persistence ---------------- */

function loadSettings() {
  try {
    const mode = localStorage.getItem(STORAGE.mode);
    if (mode === 'live' || mode === 'sample') state.mode = mode;
    const proxy = localStorage.getItem(STORAGE.proxy);
    if (proxy !== null) state.proxyTemplate = proxy;
    const complexId = localStorage.getItem(STORAGE.complex);
    const saved = complexId && complexById(complexId);
    if (saved) state.complex = saved;
  } catch {
    // localStorage may be unavailable (private mode / sandbox) — use defaults.
  }
}

function save(key, value) {
  try {
    localStorage.setItem(key, value);
  } catch {
    /* ignore */
  }
}

/* ---------------- small DOM helpers ---------------- */

function clear(node) {
  while (node.firstChild) node.removeChild(node.firstChild);
}

function makeBullet(routeOrStyle, sizeClass = '') {
  const style = typeof routeOrStyle === 'string' ? routeStyle(routeOrStyle) : routeOrStyle;
  const span = document.createElement('span');
  span.className = `bullet ${style.label.length > 1 ? 'wide' : ''} ${sizeClass}`.trim();
  span.textContent = style.label;
  span.style.background = style.color;
  span.style.color = style.text;
  span.title = style.trunk ? `${style.label} — ${style.trunk}` : style.label;
  return span;
}

function bulletRow(routes, sizeClass = 'sm') {
  const wrap = document.createElement('span');
  wrap.className = 'bullets';
  for (const route of routes) wrap.appendChild(makeBullet(route, sizeClass));
  return wrap;
}

/* ---------------- proxy settings UI ---------------- */

function populateProxySelect() {
  clear(el.proxySelect);
  for (const preset of PROXY_PRESETS) {
    const option = document.createElement('option');
    option.value = preset.id;
    option.textContent = preset.label;
    el.proxySelect.appendChild(option);
  }
  const custom = document.createElement('option');
  custom.value = 'custom';
  custom.textContent = 'Custom…';
  el.proxySelect.appendChild(custom);
}

function syncProxyUI() {
  const preset = PROXY_PRESETS.find((p) => p.template === state.proxyTemplate);
  if (preset) {
    el.proxySelect.value = preset.id;
    el.proxyCustomField.hidden = true;
  } else {
    el.proxySelect.value = 'custom';
    el.proxyCustomField.hidden = false;
    el.proxyCustom.value = state.proxyTemplate;
  }
  const liveDisabled = state.mode !== 'live';
  el.proxyField.style.opacity = liveDisabled ? 0.55 : 1;
}

/* ---------------- station picker ---------------- */

function renderChips() {
  clear(el.chips);
  for (const complex of searchComplexes('').slice(0, 6)) {
    const chip = document.createElement('button');
    chip.type = 'button';
    chip.className = 'chip';
    chip.textContent = complex.name;
    chip.addEventListener('click', () => selectComplex(complex));
    el.chips.appendChild(chip);
  }
}

let activeResultIndex = -1;
let currentResults = [];

function openResults(query) {
  currentResults = searchComplexes(query, 25);
  activeResultIndex = -1;
  clear(el.results);

  if (currentResults.length === 0) {
    const li = document.createElement('li');
    li.className = 'result';
    li.textContent = 'No matching stations';
    el.results.appendChild(li);
  }

  currentResults.forEach((complex, index) => {
    const li = document.createElement('li');
    li.className = 'result';
    li.setAttribute('role', 'option');
    li.dataset.index = String(index);

    const name = document.createElement('div');
    name.className = 'result-name';
    name.textContent = complex.name;
    const sub = document.createElement('small');
    sub.textContent = complex.borough;
    name.appendChild(sub);

    li.appendChild(name);
    li.appendChild(bulletRow(complex.routes));
    li.addEventListener('mousedown', (event) => {
      event.preventDefault();
      selectComplex(complex);
    });
    el.results.appendChild(li);
  });

  el.results.hidden = false;
  el.search.setAttribute('aria-expanded', 'true');
}

function closeResults() {
  el.results.hidden = true;
  el.search.setAttribute('aria-expanded', 'false');
  activeResultIndex = -1;
}

function highlightResult(delta) {
  const items = [...el.results.querySelectorAll('.result[data-index]')];
  if (!items.length) return;
  activeResultIndex = (activeResultIndex + delta + items.length) % items.length;
  items.forEach((item, i) => item.classList.toggle('active', i === activeResultIndex));
  items[activeResultIndex].scrollIntoView({ block: 'nearest' });
}

function selectComplex(complex) {
  if (!complex) return;
  state.complex = complex;
  state.alertFilter = null;
  save(STORAGE.complex, complex.id);
  el.search.value = '';
  closeResults();
  renderStationHeader();
  refresh();
}

/* ---------------- data loading ---------------- */

function loadSample(now) {
  return {
    line: decodeFeedMessage(buildSampleLineFeed({ now, complex: state.complex })),
    alerts: decodeFeedMessage(buildSampleAlertsFeed({ now })),
    source: 'sample',
  };
}

async function loadLive(now) {
  const feeds = feedsForRoutes(state.complex.routes);
  const lineResults = await Promise.allSettled(
    feeds.map((feed) => fetchFeed({ url: feedUrl(feed), proxyTemplate: state.proxyTemplate })),
  );

  const entities = [];
  let okCount = 0;
  let lastError = null;
  for (const result of lineResults) {
    if (result.status === 'fulfilled') {
      entities.push(...result.value.message.entities);
      okCount += 1;
    } else {
      lastError = result.reason;
    }
  }
  if (okCount === 0) {
    throw lastError || new Error('All feed requests failed');
  }

  let alerts = { header: {}, entities: [] };
  try {
    const result = await fetchFeed({ url: feedUrl(ALERTS_FEED), proxyTemplate: state.proxyTemplate });
    alerts = result.message;
  } catch {
    // Non-fatal: arrivals/trains still render without the alerts overlay.
  }

  return {
    line: { header: { timestamp: Math.floor(now / 1000) }, entities },
    alerts,
    source: 'live',
  };
}

async function refresh() {
  const requestId = (state.requestId += 1);
  setLoading(true);
  const now = Date.now();

  try {
    const data = state.mode === 'live' ? await loadLive(now) : loadSample(now);
    if (requestId !== state.requestId) return; // superseded by a newer refresh

    applyData(data, now);
    state.error = null;
  } catch (err) {
    if (requestId !== state.requestId) return;
    state.error = err && err.message ? err.message : String(err);

    if (!state.lastUpdated) {
      // Never rendered anything yet — show sample data so the page works.
      applyData(loadSample(Date.now()), Date.now());
      state.error += ' — showing sample data instead.';
    }
  } finally {
    if (requestId === state.requestId) setLoading(false);
    render();
  }
}

function applyData(data, now) {
  state.status = buildServiceStatus(data.alerts, { now });
  state.arrivals = buildArrivals(data.line, state.complex, { now });
  state.trains = buildTrains(data.line, { now, complex: state.complex, routes: state.complex.routes });
  state.lastUpdated = now;
  state.source = data.source;
}

function setLoading(loading) {
  state.loading = loading;
  el.refresh.classList.toggle('loading', loading);
  el.refresh.disabled = loading;
}

/* ---------------- rendering ---------------- */

function render() {
  renderTopbar();
  renderError();
  renderStationHeader();
  renderArrivals();
  renderStatus();
  renderTrains();
  renderAlerts();
}

function renderTopbar() {
  const mode = state.source === 'live' ? 'live' : 'sample';
  el.dataMode.dataset.mode = mode;
  el.dataMode.textContent = mode === 'live' ? 'Live' : 'Sample data';
  if (state.lastUpdated) {
    el.lastUpdated.textContent = `Updated ${freshness(Math.floor(state.lastUpdated / 1000))}`;
  }
}

function renderError() {
  if (!state.error) {
    el.error.hidden = true;
    clear(el.error);
    return;
  }
  clear(el.error);
  const strong = document.createElement('strong');
  strong.textContent = 'Live feed unavailable: ';
  el.error.appendChild(strong);
  el.error.appendChild(document.createTextNode(state.error));
  el.error.hidden = false;
}

function renderStationHeader() {
  const complex = state.complex;
  el.stationName.textContent = complex.name;
  clear(el.stationMeta);
  el.stationMeta.appendChild(bulletRow(complex.routes));
  const place = document.createElement('span');
  place.textContent = ` ${complex.borough}`;
  el.stationMeta.appendChild(place);
}

function renderArrivals() {
  clear(el.arrivals);
  const board = state.arrivals;
  if (!board) return;

  for (const lane of board.directions) {
    const col = document.createElement('div');
    col.className = 'lane';

    const head = document.createElement('div');
    head.className = 'lane-head';
    const arrow = document.createElement('span');
    arrow.className = 'arrow';
    arrow.textContent = lane.dir === 'N' ? '↑' : '↓';
    head.appendChild(arrow);
    head.appendChild(document.createTextNode(lane.label));
    col.appendChild(head);

    if (lane.trains.length === 0) {
      const empty = document.createElement('div');
      empty.className = 'empty';
      empty.textContent = 'No upcoming trains';
      col.appendChild(empty);
    } else {
      for (const train of lane.trains) col.appendChild(arrivalRow(train));
    }
    el.arrivals.appendChild(col);
  }
}

function arrivalRow(train) {
  const row = document.createElement('div');
  row.className = 'arrival-row';
  row.appendChild(makeBullet(train.route));

  const dest = document.createElement('div');
  dest.className = 'arrival-dest';
  dest.textContent = train.destination || 'Terminal';
  row.appendChild(dest);

  const eta = document.createElement('div');
  eta.className = 'eta';
  if (train.countdown === 'Now') {
    eta.classList.add('now');
    eta.textContent = 'Now';
  } else {
    const num = document.createElement('span');
    num.className = 'num';
    num.textContent = String(train.minutes);
    const unit = document.createElement('span');
    unit.className = 'unit';
    unit.textContent = 'min';
    eta.appendChild(num);
    eta.appendChild(unit);
  }
  row.appendChild(eta);
  return row;
}

function renderStatus() {
  clear(el.routeStatus);
  const status = state.status;
  if (!status) return;

  if (status.updated) {
    el.statusUpdated.textContent = `as of ${freshness(status.updated)}`;
  } else {
    el.statusUpdated.textContent = '';
  }

  for (const route of status.routes) {
    const pill = document.createElement('button');
    pill.type = 'button';
    pill.className = 'route-pill';
    if (state.alertFilter === route.label) pill.classList.add('is-active');
    pill.appendChild(makeBullet(route));

    const text = document.createElement('span');
    text.className = 'status-text';
    text.textContent = route.statusLabel;
    pill.appendChild(text);

    const dot = document.createElement('span');
    dot.className = `dot ${route.kind}`;
    pill.appendChild(dot);

    pill.title = `${route.label}: ${route.statusLabel}`;
    pill.addEventListener('click', () => {
      state.alertFilter = state.alertFilter === route.label ? null : route.label;
      renderStatus();
      renderAlerts();
    });
    el.routeStatus.appendChild(pill);
  }
}

function renderTrains() {
  clear(el.trains);
  const data = state.trains;
  if (!data) return;

  if (data.total === 0) {
    el.trainsSummary.textContent = 'No trains reporting';
  } else {
    el.trainsSummary.textContent = `${data.total} ${pluralize(data.total, 'train')} near ${state.complex.name}`;
  }

  if (data.trains.length === 0) {
    const empty = document.createElement('div');
    empty.className = 'empty';
    empty.textContent = 'No vehicle positions in the current feed.';
    el.trains.appendChild(empty);
    return;
  }

  for (const train of data.trains) {
    const row = document.createElement('div');
    row.className = `train-row ${train.statusKind} ${train.atSelected ? 'at-selected' : ''}`.trim();
    row.appendChild(makeBullet(train));

    const info = document.createElement('div');
    info.className = 'train-info';
    const status = document.createElement('div');
    status.className = 'train-status';
    status.textContent = train.statusText;
    info.appendChild(status);

    const sub = document.createElement('div');
    sub.className = 'train-sub';
    const bits = [];
    if (train.destination) bits.push(`to ${train.destination}`);
    if (train.directionLabel) bits.push(train.directionLabel);
    if (train.updatedText) bits.push(train.updatedText);
    sub.textContent = bits.join(' · ');
    info.appendChild(sub);
    row.appendChild(info);

    el.trains.appendChild(row);
  }
}

function renderAlerts() {
  clear(el.alerts);
  const status = state.status;
  if (!status) return;

  let list = status.alerts;
  if (state.alertFilter) list = list.filter((alert) => alert.routes.includes(state.alertFilter));

  const filterNote = state.alertFilter ? ` for ${state.alertFilter}` : '';
  if (list.length === 0) {
    el.alertsSummary.textContent = '';
    const empty = document.createElement('div');
    empty.className = 'empty';
    empty.textContent = state.alertFilter
      ? `Good service on the ${state.alertFilter} — no active alerts.`
      : 'Good service across the system — no active alerts.';
    el.alerts.appendChild(empty);
    return;
  }

  el.alertsSummary.textContent =
    `${status.activeCount} active · ${status.plannedCount} planned${filterNote}`;

  for (const alert of list) {
    el.alerts.appendChild(alertCard(alert));
  }
}

function alertCard(alert) {
  const card = document.createElement('div');
  card.className = `alert ${alert.kind}`;

  const head = document.createElement('div');
  head.className = 'alert-head';
  const kind = document.createElement('span');
  kind.className = 'alert-kind';
  kind.textContent = alert.planned ? 'Planned' : alert.statusLabel;
  head.appendChild(kind);
  if (alert.routes.length) head.appendChild(bulletRow(alert.routes));
  card.appendChild(head);

  if (alert.header) {
    const title = document.createElement('p');
    title.className = 'alert-title';
    title.textContent = alert.header;
    card.appendChild(title);
  }

  if (alert.description && alert.description !== alert.header) {
    if (alert.description.length > 140) {
      const details = document.createElement('details');
      const summary = document.createElement('summary');
      summary.textContent = 'Details';
      const desc = document.createElement('p');
      desc.className = 'alert-desc';
      desc.textContent = alert.description;
      details.appendChild(summary);
      details.appendChild(desc);
      card.appendChild(details);
    } else {
      const desc = document.createElement('p');
      desc.className = 'alert-desc';
      desc.textContent = alert.description;
      card.appendChild(desc);
    }
  }
  return card;
}

/* ---------------- events + boot ---------------- */

function setMode(mode) {
  state.mode = mode;
  save(STORAGE.mode, mode);
  for (const input of document.querySelectorAll('input[name="mode"]')) {
    input.checked = input.value === mode;
  }
  syncProxyUI();
  refresh();
}

function bindEvents() {
  el.refresh.addEventListener('click', () => refresh());

  el.search.addEventListener('focus', () => openResults(el.search.value));
  el.search.addEventListener('input', () => openResults(el.search.value));
  el.search.addEventListener('blur', () => setTimeout(closeResults, 120));
  el.search.addEventListener('keydown', (event) => {
    if (event.key === 'ArrowDown') {
      event.preventDefault();
      highlightResult(1);
    } else if (event.key === 'ArrowUp') {
      event.preventDefault();
      highlightResult(-1);
    } else if (event.key === 'Enter') {
      if (activeResultIndex >= 0 && currentResults[activeResultIndex]) {
        selectComplex(currentResults[activeResultIndex]);
      } else if (currentResults[0]) {
        selectComplex(currentResults[0]);
      }
    } else if (event.key === 'Escape') {
      closeResults();
    }
  });

  for (const input of document.querySelectorAll('input[name="mode"]')) {
    input.addEventListener('change', (event) => setMode(event.target.value));
  }

  el.proxySelect.addEventListener('change', () => {
    const value = el.proxySelect.value;
    if (value === 'custom') {
      el.proxyCustomField.hidden = false;
      state.proxyTemplate = el.proxyCustom.value;
    } else {
      const preset = PROXY_PRESETS.find((p) => p.id === value);
      state.proxyTemplate = preset ? preset.template : '';
      el.proxyCustomField.hidden = true;
    }
    save(STORAGE.proxy, state.proxyTemplate);
    if (state.mode === 'live') refresh();
  });

  el.proxyCustom.addEventListener('input', () => {
    state.proxyTemplate = el.proxyCustom.value;
    save(STORAGE.proxy, state.proxyTemplate);
  });
  el.proxyCustom.addEventListener('change', () => {
    if (state.mode === 'live') refresh();
  });
}

function init() {
  loadSettings();
  populateProxySelect();
  for (const input of document.querySelectorAll('input[name="mode"]')) {
    input.checked = input.value === state.mode;
  }
  syncProxyUI();
  renderChips();
  renderStationHeader();
  bindEvents();

  poller = createPoller({ onPoll: () => refresh(), intervalMs: REFRESH_MS });
  poller.start();

  refresh();
}

init();
