// Browser entry point. Stats and scrape planning stay in DOM-free modules.

import { normalizeDoc } from "./scrape-lib.js";
import {
  WEEKDAYS,
  bucketLabelLong,
  chartLayout,
  exclusionLabel,
  formatDate,
  formatPercent,
  formatSolveTime,
  formatUpdated,
  maxSecondsFromMinutes,
  medianByWeekday,
  partialPuzzles,
  puzzleUrl,
  selectSolves,
  solvedYears,
  trendByWeekday,
  visibleExcluded,
  weekdayName,
} from "./stats.js";

const PREFS_KEY = "nyt-crossword-prefs";
const SVG_NS = "http://www.w3.org/2000/svg";
const SLUG = {
  Monday: "mon",
  Tuesday: "tue",
  Wednesday: "wed",
  Thursday: "thu",
  Friday: "fri",
  Saturday: "sat",
  Sunday: "sun",
};

const el = {
  generated: document.getElementById("generated"),
  badge: document.getElementById("source-badge"),
  reload: document.getElementById("reload"),
  fromYear: document.getElementById("from-year"),
  throughYear: document.getElementById("through-year"),
  bucket: document.getElementById("bucket"),
  hideOutliers: document.getElementById("hide-outliers"),
  maxMinutes: document.getElementById("max-minutes"),
  solveCount: document.getElementById("solve-count"),
  summary: document.getElementById("weekday-summary"),
  legend: document.getElementById("legend"),
  chart: document.getElementById("chart"),
  chartEmpty: document.getElementById("chart-empty"),
  ignoreForm: document.getElementById("ignore-form"),
  ignoreDate: document.getElementById("ignore-date"),
  notice: document.getElementById("notice"),
  excludedBody: document.getElementById("excluded-rows"),
  excludedTable: document.getElementById("excluded-table"),
  excludedEmpty: document.getElementById("excluded-empty"),
  excludedMore: document.getElementById("excluded-more"),
  partialSort: document.getElementById("partial-sort"),
  partialBody: document.getElementById("partial-rows"),
  partialTable: document.getElementById("partial-table"),
  partialEmpty: document.getElementById("partial-empty"),
};

const state = {
  doc: null,
  source: "sample",
  ignored: new Set(),
  hiddenWeekdays: new Set(),
};

function loadPrefs() {
  const raw = localStorage.getItem(PREFS_KEY);
  if (!raw) return;
  try {
    const prefs = JSON.parse(raw);
    if (!prefs || typeof prefs !== "object") return;
    if (typeof prefs.hideOutliers === "boolean") el.hideOutliers.checked = prefs.hideOutliers;
    if (typeof prefs.maxMinutes === "string") el.maxMinutes.value = prefs.maxMinutes;
    if (prefs.bucket === "month" || prefs.bucket === "quarter" || prefs.bucket === "year") {
      el.bucket.value = prefs.bucket;
    }
    if (
      prefs.partialSort === "date" ||
      prefs.partialSort === "percent" ||
      prefs.partialSort === "weekday"
    ) {
      el.partialSort.value = prefs.partialSort;
    }
    if (Array.isArray(prefs.ignored)) {
      state.ignored = new Set(prefs.ignored.filter((date) => typeof date === "string"));
    }
    if (Array.isArray(prefs.hiddenWeekdays)) {
      state.hiddenWeekdays = new Set(
        prefs.hiddenWeekdays.filter((day) => WEEKDAYS.includes(day)),
      );
    }
  } catch {
    return;
  }
}

function savePrefs() {
  const payload = {
    hideOutliers: el.hideOutliers.checked,
    maxMinutes: el.maxMinutes.value,
    bucket: el.bucket.value,
    partialSort: el.partialSort.value,
    ignored: [...state.ignored],
    hiddenWeekdays: [...state.hiddenWeekdays],
  };
  try {
    localStorage.setItem(PREFS_KEY, JSON.stringify(payload));
  } catch {
    el.notice.textContent = "This browser did not store the filters.";
  }
}

async function fetchJson(path) {
  const response = await fetch(path, { cache: "no-store" });
  if (!response.ok) throw new Error(`HTTP ${response.status} for ${path}`);
  return response.json();
}

async function loadDoc() {
  try {
    const live = normalizeDoc(await fetchJson("data/stats.json"));
    if (live.puzzles.length > 0) return { doc: live, source: "live" };
  } catch {
    // Live stats are published on gh-pages. Sample covers local preview.
  }
  const sample = normalizeDoc(await fetchJson("sample/stats.json"));
  return { doc: sample, source: "sample" };
}

function option(year) {
  const node = document.createElement("option");
  node.value = String(year);
  node.textContent = String(year);
  return node;
}

function fillYears() {
  const years = solvedYears(state.doc.puzzles);
  const previousFrom = el.fromYear.value;
  const previousThrough = el.throughYear.value;
  el.fromYear.replaceChildren(...years.map(option));
  el.throughYear.replaceChildren(...years.map(option));
  if (years.length === 0) return;
  el.fromYear.value = years.includes(Number(previousFrom)) ? previousFrom : String(years[0]);
  const last = String(years[years.length - 1]);
  el.throughYear.value = years.includes(Number(previousThrough)) ? previousThrough : last;
}

function yearRange() {
  const from = Number(el.fromYear.value);
  const through = Number(el.throughYear.value);
  if (!Number.isFinite(from) || !Number.isFinite(through)) {
    return { fromYear: NaN, throughYear: NaN };
  }
  return { fromYear: Math.min(from, through), throughYear: Math.max(from, through) };
}

function swatch(weekday) {
  const mark = document.createElement("span");
  mark.className = `swatch ${SLUG[weekday]}`;
  mark.setAttribute("aria-hidden", "true");
  return mark;
}

function renderSummary(rows) {
  el.summary.replaceChildren();
  for (const row of rows) {
    const item = document.createElement("li");
    const name = document.createElement("span");
    name.className = "day";
    name.append(swatch(row.weekday), document.createTextNode(row.weekday));
    const time = document.createElement("strong");
    time.textContent = row.median == null ? "No solves" : formatSolveTime(row.median);
    const count = document.createElement("span");
    count.className = "count";
    count.textContent =
      row.count === 1 ? "1 solve" : `${row.count.toLocaleString("en-US")} solves`;
    item.append(name, time, count);
    el.summary.append(item);
  }
}

function renderLegend() {
  el.legend.replaceChildren();
  for (const weekday of WEEKDAYS) {
    const button = document.createElement("button");
    button.type = "button";
    button.className = `legend-button ${SLUG[weekday]}`;
    button.dataset.weekday = weekday;
    button.append(swatch(weekday), document.createTextNode(weekday));
    const shown = !state.hiddenWeekdays.has(weekday);
    button.setAttribute("aria-pressed", shown ? "true" : "false");
    button.addEventListener("click", () => {
      if (state.hiddenWeekdays.has(weekday)) state.hiddenWeekdays.delete(weekday);
      else state.hiddenWeekdays.add(weekday);
      savePrefs();
      render();
      const next = el.legend.querySelector(`[data-weekday="${weekday}"]`);
      if (next) next.focus();
    });
    el.legend.append(button);
  }
}

function svgEl(name, attrs) {
  const node = document.createElementNS(SVG_NS, name);
  for (const [key, value] of Object.entries(attrs)) node.setAttribute(key, String(value));
  return node;
}

function renderChart(series) {
  const visible = series.filter(
    (row) => !state.hiddenWeekdays.has(row.weekday) && row.points.length > 0,
  );
  el.chart.replaceChildren();
  if (visible.length === 0) {
    el.chart.hidden = true;
    el.chartEmpty.hidden = false;
    el.chartEmpty.textContent =
      series.every((row) => row.points.length === 0)
        ? "No solved puzzles in this range."
        : "All weekdays are hidden.";
    return;
  }
  el.chart.hidden = false;
  el.chartEmpty.hidden = true;
  const layout = chartLayout(visible);
  el.chart.setAttribute("viewBox", `0 0 ${layout.width} ${layout.height}`);
  const plot = svgEl("rect", {
    class: "plot",
    x: layout.pad.left,
    y: layout.pad.top,
    width: layout.width - layout.pad.left - layout.pad.right,
    height: layout.height - layout.pad.top - layout.pad.bottom,
  });
  el.chart.append(plot);
  for (const tick of layout.yTicks) {
    el.chart.append(
      svgEl("line", {
        class: "grid",
        x1: layout.pad.left,
        x2: layout.width - layout.pad.right,
        y1: tick.y,
        y2: tick.y,
      }),
    );
    const label = svgEl("text", {
      class: "axis",
      x: layout.pad.left - 8,
      y: tick.y + 5,
      "text-anchor": "end",
    });
    label.textContent = tick.label;
    el.chart.append(label);
  }
  for (const tick of layout.xTicks) {
    const label = svgEl("text", {
      class: "axis",
      x: tick.x,
      y: layout.height - 10,
      "text-anchor": "middle",
    });
    label.textContent = tick.label;
    el.chart.append(label);
  }
  for (const line of layout.lines) {
    const slug = SLUG[line.weekday];
    if (line.points.length > 1) {
      el.chart.append(
        svgEl("polyline", {
          class: `series ${slug}`,
          points: line.points.map((point) => `${point.x},${point.y}`).join(" "),
        }),
      );
    }
    for (const point of line.points) {
      const dot = svgEl("circle", {
        class: `dot ${slug}`,
        cx: point.x,
        cy: point.y,
        r: 4,
      });
      const title = document.createElementNS(SVG_NS, "title");
      title.textContent = `${line.weekday}, ${bucketLabelLong(point.bucket)}: ${formatSolveTime(point.median)} median, ${point.count} solves`;
      dot.append(title);
      el.chart.append(dot);
    }
  }
}

function renderExcluded(excluded) {
  const visible = visibleExcluded(excluded);
  el.excludedBody.replaceChildren();
  el.excludedEmpty.hidden = excluded.length > 0;
  el.excludedTable.hidden = excluded.length === 0;
  el.excludedMore.hidden = visible.hidden === 0;
  if (visible.hidden > 0) {
    el.excludedMore.textContent = `Showing the 100 longest, plus every ignored date. ${visible.hidden.toLocaleString("en-US")} more are excluded.`;
  }
  for (const row of visible.rows) {
    const tr = document.createElement("tr");
    const date = document.createElement("td");
    const label = document.createElement("span");
    label.className = "date-label";
    label.append(
      swatch(weekdayName(row.puzzle.date)),
      document.createTextNode(formatDate(row.puzzle.date)),
    );
    date.append(label);
    const time = document.createElement("td");
    time.className = "num";
    time.textContent = formatSolveTime(row.puzzle.seconds);
    const reason = document.createElement("td");
    reason.textContent = exclusionLabel(row.reason);
    const action = document.createElement("td");
    const button = document.createElement("button");
    button.type = "button";
    button.dataset.date = row.puzzle.date;
    if (row.reason === "ignored") {
      button.dataset.action = "restore";
      button.textContent = "Restore";
    } else {
      button.dataset.action = "ignore";
      button.textContent = "Ignore";
    }
    action.append(button);
    tr.append(date, time, reason, action);
    el.excludedBody.append(tr);
  }
}

function renderPartials(puzzles) {
  const rows = partialPuzzles(puzzles, el.partialSort.value);
  el.partialBody.replaceChildren();
  el.partialEmpty.hidden = rows.length > 0;
  el.partialTable.hidden = rows.length === 0;
  for (const puzzle of rows) {
    const tr = document.createElement("tr");
    const date = document.createElement("td");
    const link = document.createElement("a");
    link.href = puzzleUrl(puzzle.date);
    link.target = "_blank";
    link.rel = "noopener noreferrer";
    link.textContent = formatDate(puzzle.date);
    date.append(link);
    const filled = document.createElement("td");
    filled.className = "num";
    filled.textContent = formatPercent(puzzle.percentFilled);
    tr.append(date, filled);
    el.partialBody.append(tr);
  }
}

function render() {
  if (!state.doc) return;
  const range = yearRange();
  const { kept, excluded } = selectSolves(state.doc.puzzles, {
    ...range,
    hideOutliers: el.hideOutliers.checked,
    maxSeconds: maxSecondsFromMinutes(el.maxMinutes.value),
    ignoredDates: state.ignored,
  });
  const excludedCount = excluded.length.toLocaleString("en-US");
  const keptCount = kept.length.toLocaleString("en-US");
  el.solveCount.textContent =
    excluded.length > 0
      ? `${keptCount} solves in range. ${excludedCount} excluded.`
      : `${keptCount} solves in range.`;
  renderSummary(medianByWeekday(kept));
  renderLegend();
  renderChart(trendByWeekday(kept, el.bucket.value));
  renderExcluded(excluded);
  renderPartials(state.doc.puzzles);
}

function setBadge() {
  el.badge.hidden = false;
  if (state.source === "live") {
    el.badge.textContent = "Live stats";
    el.badge.className = "badge live";
    return;
  }
  el.badge.textContent = "Sample data";
  el.badge.className = "badge sample";
}

async function boot() {
  const loaded = await loadDoc();
  state.doc = loaded.doc;
  state.source = loaded.source;
  const when = formatUpdated(state.doc.generatedAt);
  el.generated.textContent = when ? `Updated ${when}` : "";
  setBadge();
  fillYears();
  render();
}

el.reload.addEventListener("click", () => {
  boot().catch(() => {
    el.notice.textContent = "Could not reload the stats file.";
  });
});

for (const node of [el.fromYear, el.throughYear, el.bucket, el.hideOutliers, el.partialSort]) {
  node.addEventListener("change", () => {
    savePrefs();
    render();
  });
}
el.maxMinutes.addEventListener("input", () => {
  savePrefs();
  render();
});

el.ignoreForm.addEventListener("submit", (event) => {
  event.preventDefault();
  if (!state.doc) return;
  const date = el.ignoreDate.value;
  if (!date) {
    el.notice.textContent = "Choose a date.";
    return;
  }
  const puzzle = state.doc.puzzles.find(
    (row) => row.date === date && row.solved === true && row.seconds > 0,
  );
  if (!puzzle) {
    el.notice.textContent = "No solved puzzle on that date.";
    return;
  }
  state.ignored.add(date);
  el.notice.textContent = "";
  savePrefs();
  render();
});

el.excludedBody.addEventListener("click", (event) => {
  const button = event.target.closest("button[data-date]");
  if (!button) return;
  const date = button.dataset.date;
  if (button.dataset.action === "restore") state.ignored.delete(date);
  else state.ignored.add(date);
  el.notice.textContent = "";
  savePrefs();
  render();
  const next = el.excludedBody.querySelector(`button[data-date="${date}"]`);
  if (next) next.focus();
});

loadPrefs();
boot().catch(() => {
  el.notice.textContent = "Could not load crossword stats.";
});
