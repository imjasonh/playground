/**
 * Roll the system-wide alerts feed up into a per-route service status (the
 * "Good Service / Delays / ..." board) plus a flat, worst-first list of the
 * alerts themselves.
 *
 * GTFS-realtime gives us an `effect` enum and free-text header/description. The
 * MTA layers its own "Planned Work / Delays / Service Change" taxonomy on top
 * via a non-standard extension we don't decode, so {@link classifyAlert} leans
 * on `effect` first and falls back to keyword heuristics on the text.
 */

import { ROUTE_ORDER, normalizeRouteId, routeStyle, sortRoutes } from './routes.js';

/** GTFS-realtime Alert.Effect enum (the values we special-case). */
const EFFECT = {
  NO_SERVICE: 1,
  REDUCED_SERVICE: 2,
  SIGNIFICANT_DELAYS: 3,
  DETOUR: 4,
  MODIFIED_SERVICE: 6,
};

/** Severity ladder. Higher rank wins when a route has several active alerts. */
export const LEVELS = {
  GOOD: { rank: 0, label: 'Good Service', kind: 'good' },
  INFO: { rank: 1, label: 'Service Notice', kind: 'info' },
  PLANNED: { rank: 1, label: 'Planned Work', kind: 'planned' },
  DELAYS: { rank: 2, label: 'Delays', kind: 'warn' },
  DISRUPTION: { rank: 3, label: 'Service Change', kind: 'bad' },
};

function level(name, label) {
  return { level: name, label: label || LEVELS[name].label };
}

/**
 * Classify one alert into a {@link LEVELS} bucket and a short label.
 * @param {{effect?: number, headerText?: string, descriptionText?: string}} alert
 */
export function classifyAlert(alert) {
  const effect = alert.effect;
  const text = `${alert.headerText || ''} ${alert.descriptionText || ''}`.toLowerCase();

  if (effect === EFFECT.NO_SERVICE || /suspend|no\s+\w+\s+service|not running|trains? are not/.test(text)) {
    return level('DISRUPTION', 'No Service');
  }
  if (effect === EFFECT.REDUCED_SERVICE) return level('DISRUPTION', 'Reduced Service');
  if (effect === EFFECT.SIGNIFICANT_DELAYS || /\bdelay/.test(text)) return level('DELAYS');
  if (effect === EFFECT.DETOUR || /reroute|rerouted|detour/.test(text)) return level('DELAYS', 'Reroute');
  if (/planned work|scheduled|weekend|overnight|nights/.test(text) && !/\bdelay/.test(text)) {
    return level('PLANNED');
  }
  if (effect === EFFECT.MODIFIED_SERVICE || /service change|skip|express|local|bypass/.test(text)) {
    return level('INFO', 'Service Change');
  }
  return level('INFO');
}

function periodActive(periods, nowSec) {
  if (!periods || periods.length === 0) return true; // no window = always in effect
  return periods.some((p) => {
    const start = Number.isFinite(p.start) ? p.start : -Infinity;
    const end = Number.isFinite(p.end) ? p.end : Infinity;
    return start <= nowSec && nowSec <= end;
  });
}

function periodFuture(periods, nowSec) {
  if (!periods || periods.length === 0) return false;
  return periods.some((p) => Number.isFinite(p.start) && p.start > nowSec);
}

/**
 * @param {{header?: {timestamp?: number}, entities?: object[]}} alertsFeed
 * @param {{now?: number, routes?: string[]}} [options]
 */
export function buildServiceStatus(alertsFeed, { now = Date.now(), routes = ROUTE_ORDER } = {}) {
  const nowSec = now / 1000;
  const routeState = new Map(routes.map((r) => [r, { level: 'GOOD', alerts: [] }]));
  const alerts = [];

  for (const entity of (alertsFeed && alertsFeed.entities) || []) {
    const alert = entity.alert;
    if (!alert) continue;

    const active = periodActive(alert.activePeriods, nowSec);
    const planned = !active && periodFuture(alert.activePeriods, nowSec);
    if (!active && !planned) continue; // expired

    const cls = classifyAlert(alert);
    const routeLabels = sortRoutes(
      new Set(
        (alert.informedEntities || [])
          .map((sel) => sel.routeId)
          .filter(Boolean)
          .map(normalizeRouteId),
      ),
    );

    const record = {
      id: entity.id || '',
      level: cls.level,
      statusLabel: cls.label,
      kind: LEVELS[cls.level].kind,
      rank: LEVELS[cls.level].rank,
      header: alert.headerText || '',
      description: alert.descriptionText || '',
      url: alert.url || '',
      routes: routeLabels,
      active,
      planned,
    };
    alerts.push(record);

    for (const routeLabel of routeLabels) {
      const state = routeState.get(routeLabel);
      if (!state) continue; // alert for a route we don't track (e.g. a bus)
      state.alerts.push(record);
      if (active && LEVELS[cls.level].rank > LEVELS[state.level].rank) {
        state.level = cls.level;
        state.statusLabel = cls.label;
      }
    }
  }

  const routeList = routes.map((routeLabel) => {
    const state = routeState.get(routeLabel);
    const meta = LEVELS[state.level];
    return {
      ...routeStyle(routeLabel),
      level: state.level,
      statusLabel: state.level === 'GOOD' ? 'Good Service' : state.statusLabel || meta.label,
      kind: meta.kind,
      alerts: state.alerts,
    };
  });

  alerts.sort((a, b) => b.rank - a.rank || (a.active === b.active ? 0 : a.active ? -1 : 1));

  return {
    updated: alertsFeed && alertsFeed.header ? alertsFeed.header.timestamp : undefined,
    routes: routeList,
    alerts,
    activeCount: alerts.filter((a) => a.active).length,
    plannedCount: alerts.filter((a) => a.planned).length,
  };
}
