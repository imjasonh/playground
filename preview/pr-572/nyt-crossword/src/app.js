// Browser entry point. Stats stay in the DOM-free module.

import { publishedDataUrl } from "./published-data.js";
import { normalizeDoc } from "./scrape-lib.js";
import {
  WEEKDAYS,
  bucketLabelLong,
  chartLayout,
  excludedDates,
  formatDate,
  formatPercent,
  formatSolveTime,
  formatUpdated,
  medianByWeekday,
  partialPuzzles,
  puzzleUrl,
  selectSolves,
  solvedYears,
  trendByWeekday,
} from "./stats.js";

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
  solveCount: document.getElementById("solve-count"),
  notice: document.getElementById("notice"),
  summary: document.getElementById("weekday-summary"),
  legend: document.getElementById("legend"),
  chart: document.getElementById("chart"),
  chartEmpty: document.getElementById("chart-empty"),
  partialSort: document.getElementById("partial-sort"),
  partialBody: document.getElementById("partial-rows"),
  partialTable: document.getElementById("partial-table"),
  partialEmpty: document.getElementById("partial-empty"),
};

const state = {
  doc: null,
  source: "sample",
  excluded: new Set(),
  hiddenWeekdays: new Set(),
};

async function fetchJson(path) {
  const response = await fetch(path, { cache: "no-store" });
  if (!response.ok) throw new Error(`HTTP ${response.status} for ${path}`);
  return response.json();
}

async function loadDoc() {
  const urls = ["data/stats.json"];
  const published = publishedDataUrl(window.location.pathname, "data/stats.json");
  if (published) urls.push(published);
  for (const url of urls) {
    try {
      const live = normalizeDoc(await fetchJson(url));
      if (live.puzzles.length > 0) return { doc: live, source: "live" };
    } catch {
      // Missing here. A preview then tries the published gh-pages file.
    }
  }
  const sample = normalizeDoc(await fetchJson("sample/stats.json"));
  return { doc: sample, source: "sample" };
}

async function loadExcluded() {
  try {
    return excludedDates(await fetchJson("excluded.json"));
  } catch {
    return new Set();
  }
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

function renderSummary(rows) {
  el.summary.replaceChildren();
  for (const row of rows) {
    const tr = document.createElement("tr");
    const day = document.createElement("th");
    day.scope = "row";
    day.textContent = row.weekday;
    const time = document.createElement("td");
    time.className = "num";
    time.textContent = row.median == null ? "None" : formatSolveTime(row.median);
    const count = document.createElement("td");
    count.className = "num";
    count.textContent = row.count.toLocaleString("en-US");
    tr.append(day, time, count);
    el.summary.append(tr);
  }
}

function renderLegend() {
  el.legend.replaceChildren();
  for (const weekday of WEEKDAYS) {
    const button = document.createElement("button");
    button.type = "button";
    button.className = "legend-button";
    button.dataset.weekday = weekday;
    const key = document.createElement("span");
    key.className = `key ${SLUG[weekday]}`;
    key.setAttribute("aria-hidden", "true");
    button.append(key, document.createTextNode(weekday));
    const shown = !state.hiddenWeekdays.has(weekday);
    button.setAttribute("aria-pressed", shown ? "true" : "false");
    button.addEventListener("click", () => {
      if (state.hiddenWeekdays.has(weekday)) state.hiddenWeekdays.delete(weekday);
      else state.hiddenWeekdays.add(weekday);
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
    el.chartEmpty.textContent = series.every((row) => row.points.length === 0)
      ? "No solved puzzles in this range."
      : "All weekdays are hidden.";
    return;
  }
  el.chart.hidden = false;
  el.chartEmpty.hidden = true;
  const layout = chartLayout(visible, { width: 720, height: 380 });
  el.chart.setAttribute("viewBox", `0 0 ${layout.width} ${layout.height}`);
  el.chart.append(
    svgEl("rect", {
      class: "plot",
      x: layout.pad.left,
      y: layout.pad.top,
      width: layout.width - layout.pad.left - layout.pad.right,
      height: layout.height - layout.pad.top - layout.pad.bottom,
    }),
  );
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
      y: layout.height - 8,
      "text-anchor": tick.anchor,
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
        r: 3.5,
      });
      const title = document.createElementNS(SVG_NS, "title");
      title.textContent = `${line.weekday}, ${bucketLabelLong(point.bucket)}: ${formatSolveTime(point.median)} median, ${point.count} solves`;
      dot.append(title);
      el.chart.append(dot);
    }
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
  const { kept } = selectSolves(state.doc.puzzles, {
    ...range,
    hideOutliers: el.hideOutliers.checked,
    excludedDates: state.excluded,
  });
  const keptCount = kept.length.toLocaleString("en-US");
  el.solveCount.textContent =
    keptCount === "1" ? "1 solve in range." : `${keptCount} solves in range.`;
  renderSummary(medianByWeekday(kept));
  renderLegend();
  renderChart(trendByWeekday(kept, el.bucket.value));
  renderPartials(state.doc.puzzles);
}

function setBadge() {
  el.badge.hidden = false;
  el.badge.textContent = state.source === "live" ? "Live" : "Sample";
}

async function boot() {
  el.notice.textContent = "";
  const [loaded, excluded] = await Promise.all([loadDoc(), loadExcluded()]);
  state.doc = loaded.doc;
  state.source = loaded.source;
  state.excluded = excluded;
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
  node.addEventListener("change", render);
}

boot().catch(() => {
  el.notice.textContent = "Could not load crossword stats.";
});
