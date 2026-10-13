// Browser entry point. Stats stay in the DOM-free module.

import { publishedDataUrl } from "./published-data.js";
import { normalizeDoc } from "./scrape-lib.js";
import {
  WEEKDAYS,
  bucketSpan,
  chartLayout,
  excludedDates,
  formatDate,
  formatPercent,
  formatSolveTime,
  formatUnsolvedCount,
  formatUpdated,
  medianByWeekday,
  nearestChartPoint,
  overallByBucket,
  partialPuzzles,
  placeView,
  puzzleUrl,
  selectSolves,
  solvedYears,
  trendByWeekday,
  trendLine,
  weekdayName,
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
  unsolvedCount: document.getElementById("unsolved-count"),
  fromYear: document.getElementById("from-year"),
  throughYear: document.getElementById("through-year"),
  bucket: document.getElementById("bucket"),
  hideOutliers: document.getElementById("hide-outliers"),
  trendDays: document.getElementById("trend-days"),
  trendOverall: document.getElementById("trend-overall"),
  solveCount: document.getElementById("solve-count"),
  notice: document.getElementById("notice"),
  summary: document.getElementById("weekday-summary"),
  legend: document.getElementById("legend"),
  chart: document.getElementById("chart"),
  chartEmpty: document.getElementById("chart-empty"),
  chartScroll: document.getElementById("chart-scroll"),
  chartPan: document.getElementById("chart-pan"),
  chartPanInner: document.getElementById("chart-pan-inner"),
  chartFrame: document.querySelector(".chart-frame"),
  chartTip: document.getElementById("chart-tip"),
  zoomIn: document.getElementById("zoom-in"),
  zoomOut: document.getElementById("zoom-out"),
  zoomReset: document.getElementById("zoom-reset"),
  partialSort: document.getElementById("partial-sort"),
  partialBody: document.getElementById("partial-rows"),
  partialTable: document.getElementById("partial-table"),
  partialEmpty: document.getElementById("partial-empty"),
};

const CHART_HEIGHT = 380;

const state = {
  doc: null,
  excluded: new Set(),
  hiddenWeekdays: new Set(),
  viewStart: 0,
  viewEnd: 1,
  bucketCount: 0,
  chartPoints: [],
  syncingPan: false,
};

async function fetchJson(path) {
  const response = await fetch(path, { cache: "no-store" });
  if (!response.ok) throw new Error(`HTTP ${response.status} for ${path}`);
  return response.json();
}

async function loadDoc() {
  const published = publishedDataUrl(window.location.pathname, "data/stats.json");
  return normalizeDoc(await fetchJson(published ?? "data/stats.json"));
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
    const label = document.createElement("label");
    label.className = "legend-check";
    const input = document.createElement("input");
    input.type = "checkbox";
    input.checked = !state.hiddenWeekdays.has(weekday);
    input.addEventListener("change", () => {
      if (input.checked) state.hiddenWeekdays.delete(weekday);
      else state.hiddenWeekdays.add(weekday);
      render();
    });
    const key = document.createElement("span");
    key.className = `key ${SLUG[weekday]}`;
    key.setAttribute("aria-hidden", "true");
    label.append(input, key, document.createTextNode(weekday));
    el.legend.append(label);
  }
  if (el.trendOverall.checked) {
    const label = document.createElement("span");
    label.className = "legend-check";
    const key = document.createElement("span");
    key.className = "key overall";
    key.setAttribute("aria-hidden", "true");
    label.append(key, document.createTextNode("Overall"));
    el.legend.append(label);
  }
}

function svgEl(name, attrs) {
  const node = document.createElementNS(SVG_NS, name);
  for (const [key, value] of Object.entries(attrs)) node.setAttribute(key, String(value));
  return node;
}

function chartPixelWidth() {
  return Math.max(1, Math.round(el.chartScroll.clientWidth || 720));
}

function minViewSpan() {
  if (state.bucketCount <= 2) return 1;
  return 1 / (state.bucketCount - 1);
}

function setView(start, end) {
  const span = Math.min(1, Math.max(minViewSpan(), end - start));
  const [nextStart, nextEnd] = placeView(start, span);
  state.viewStart = nextStart;
  state.viewEnd = nextEnd;
}

function hideTip() {
  el.chartTip.hidden = true;
  el.chartTip.replaceChildren();
  for (const dot of el.chart.querySelectorAll(".is-hot")) {
    dot.classList.remove("is-hot");
    dot.setAttribute("r", "3.5");
  }
}

function syncZoomButtons(enabled) {
  const span = state.viewEnd - state.viewStart;
  el.zoomIn.disabled = !enabled || span <= minViewSpan() + 1e-4;
  el.zoomOut.disabled = !enabled || span >= 0.999;
  el.zoomReset.disabled = !enabled || span >= 0.999;
  el.chart.classList.toggle("is-zoomed", enabled && span < 0.999);
  el.chart.style.touchAction = enabled && span < 0.999 ? "none" : "pan-y";
}

function syncPanBar() {
  const span = state.viewEnd - state.viewStart;
  const zoomed = span < 0.999 && state.bucketCount > 2;
  el.chartPan.hidden = !zoomed;
  if (!zoomed) return;
  const viewport = el.chartPan.clientWidth || el.chartScroll.clientWidth || 1;
  const inner = Math.max(viewport + 1, viewport / span);
  el.chartPanInner.style.width = `${inner}px`;
  const maxScroll = inner - viewport;
  const left = (state.viewStart / (1 - span)) * maxScroll;
  state.syncingPan = true;
  el.chartPan.scrollLeft = left;
  state.syncingPan = false;
}

function drawTrend(line, slug) {
  const trend = trendLine(line.points);
  if (!trend) return;
  el.chart.append(
    svgEl("line", {
      class: `trend ${slug}`,
      "clip-path": "url(#plot-clip)",
      x1: trend.x1,
      y1: trend.y1,
      x2: trend.x2,
      y2: trend.y2,
    }),
  );
}

function renderChart(series, overall) {
  hideTip();
  const visible = series.filter(
    (row) => !state.hiddenWeekdays.has(row.weekday) && row.points.length > 0,
  );
  const plotted = el.trendOverall.checked && overall ? [...visible, overall] : visible;
  el.chart.replaceChildren();
  state.chartPoints = [];
  if (plotted.length === 0 || visible.length === 0) {
    el.chart.hidden = true;
    el.chartEmpty.hidden = false;
    el.chartEmpty.textContent = series.every((row) => row.points.length === 0)
      ? "No solved puzzles in this range."
      : "All weekdays are hidden.";
    syncZoomButtons(false);
    return;
  }
  el.chart.hidden = false;
  el.chartEmpty.hidden = true;
  const layout = chartLayout(plotted, {
    width: chartPixelWidth(),
    height: CHART_HEIGHT,
    viewStart: state.viewStart,
    viewEnd: state.viewEnd,
  });
  state.bucketCount = layout.bucketCount;
  el.chart.setAttribute("width", String(layout.width));
  el.chart.setAttribute("height", String(layout.height));
  el.chart.setAttribute("viewBox", `0 0 ${layout.width} ${layout.height}`);
  syncZoomButtons(true);
  syncPanBar();
  const plotWidth = layout.width - layout.pad.left - layout.pad.right;
  const plotHeight = layout.height - layout.pad.top - layout.pad.bottom;
  const defs = svgEl("defs", {});
  const clip = svgEl("clipPath", { id: "plot-clip" });
  clip.append(
    svgEl("rect", {
      x: layout.pad.left,
      y: layout.pad.top,
      width: plotWidth,
      height: plotHeight,
    }),
  );
  defs.append(clip);
  el.chart.append(defs);
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
    if (line.weekday === "Overall") {
      drawTrend(line, "overall");
      continue;
    }
    const slug = SLUG[line.weekday];
    if (line.points.length > 1) {
      el.chart.append(
        svgEl("polyline", {
          class: `series ${slug}`,
          "clip-path": "url(#plot-clip)",
          points: line.points.map((point) => `${point.x},${point.y}`).join(" "),
        }),
      );
    }
    for (const point of line.points) {
      const dot = svgEl("circle", {
        class: `dot ${slug}`,
        "clip-path": "url(#plot-clip)",
        cx: point.x,
        cy: point.y,
        r: 3.5,
      });
      const title = document.createElementNS(SVG_NS, "title");
      const when = bucketSpan(point.bucket);
      const time = formatSolveTime(point.median);
      title.textContent = `${line.weekday}, ${when}, ${time}`;
      dot.append(title);
      dot.dataset.bucket = point.bucket;
      dot.dataset.weekday = line.weekday;
      el.chart.append(dot);
      if (point.x < layout.pad.left - 1 || point.x > layout.width - layout.pad.right + 1) continue;
      state.chartPoints.push({
        x: point.x,
        y: point.y,
        weekday: line.weekday,
        bucket: point.bucket,
        median: point.median,
        count: point.count,
      });
    }
    if (el.trendDays.checked) drawTrend(line, slug);
  }
}

function pointerOnChart(event) {
  const rect = el.chart.getBoundingClientRect();
  if (rect.width === 0 || rect.height === 0) return null;
  const width = Number(el.chart.getAttribute("width")) || rect.width;
  const height = Number(el.chart.getAttribute("height")) || rect.height;
  return {
    x: ((event.clientX - rect.left) / rect.width) * width,
    y: ((event.clientY - rect.top) / rect.height) * height,
  };
}

function showTip(event) {
  const at = pointerOnChart(event);
  const hit = at ? nearestChartPoint(state.chartPoints, at.x, at.y) : null;
  for (const dot of el.chart.querySelectorAll(".is-hot")) {
    dot.classList.remove("is-hot");
    dot.setAttribute("r", "3.5");
  }
  if (!hit) {
    el.chartTip.hidden = true;
    return;
  }
  const hot = el.chart.querySelector(
    `.dot[data-weekday="${hit.weekday}"][data-bucket="${hit.bucket}"]`,
  );
  if (hot) {
    hot.classList.add("is-hot");
    hot.setAttribute("r", "6");
  }
  el.chartTip.replaceChildren();
  const day = document.createElement("p");
  day.textContent = hit.weekday;
  const when = document.createElement("p");
  when.textContent = bucketSpan(hit.bucket);
  const time = document.createElement("p");
  time.className = "tip-time";
  time.textContent = formatSolveTime(hit.median);
  const meta = document.createElement("p");
  meta.className = "tip-meta";
  meta.textContent = hit.count === 1 ? "1 solve" : `Median of ${hit.count} solves`;
  el.chartTip.append(day, when, time, meta);
  el.chartTip.hidden = false;
  const frame = el.chartFrame.getBoundingClientRect();
  const tipWidth = el.chartTip.offsetWidth;
  const tipHeight = el.chartTip.offsetHeight;
  let left = event.clientX - frame.left + 14;
  let top = event.clientY - frame.top - tipHeight - 12;
  if (left + tipWidth > frame.width - 8) left = event.clientX - frame.left - tipWidth - 14;
  if (left < 8) left = 8;
  if (top < 8) top = event.clientY - frame.top + 16;
  el.chartTip.style.left = `${left}px`;
  el.chartTip.style.top = `${top}px`;
}

function zoomAt(factor, clientX) {
  const rect = el.chart.getBoundingClientRect();
  const fraction =
    rect.width > 0 && clientX != null
      ? Math.min(1, Math.max(0, (clientX - rect.left) / rect.width))
      : 0.5;
  const span = state.viewEnd - state.viewStart;
  let nextSpan = span / factor;
  nextSpan = Math.min(1, Math.max(minViewSpan(), nextSpan));
  if (Math.abs(nextSpan - span) < 1e-4) return;
  const anchor = state.viewStart + fraction * span;
  setView(anchor - fraction * nextSpan, anchor + (1 - fraction) * nextSpan);
  render();
}

function renderPartials(puzzles) {
  const rows = partialPuzzles(puzzles, el.partialSort.value);
  el.unsolvedCount.textContent = formatUnsolvedCount(rows.length);
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
  const visibleKept = kept.filter(
    (puzzle) => !state.hiddenWeekdays.has(weekdayName(puzzle.date)),
  );
  renderChart(
    trendByWeekday(kept, el.bucket.value),
    overallByBucket(visibleKept, el.bucket.value),
  );
  renderPartials(state.doc.puzzles);
}

async function boot() {
  el.notice.textContent = "";
  const [doc, excluded] = await Promise.all([loadDoc(), loadExcluded()]);
  state.doc = doc;
  state.excluded = excluded;
  const when = formatUpdated(state.doc.generatedAt);
  el.generated.textContent = when ? `Updated ${when}` : "";
  fillYears();
  render();
}

for (const node of [
  el.fromYear,
  el.throughYear,
  el.bucket,
  el.hideOutliers,
  el.trendDays,
  el.trendOverall,
  el.partialSort,
]) {
  node.addEventListener("change", render);
}

let pan = null;

el.zoomIn.addEventListener("click", () => zoomAt(1.5, null));
el.zoomOut.addEventListener("click", () => zoomAt(1 / 1.5, null));
el.zoomReset.addEventListener("click", () => {
  state.viewStart = 0;
  state.viewEnd = 1;
  render();
});

el.chart.addEventListener("pointerdown", (event) => {
  if (event.button !== 0) return;
  if (state.viewEnd - state.viewStart >= 0.999) return;
  pan = {
    id: event.pointerId,
    x: event.clientX,
    start: state.viewStart,
    end: state.viewEnd,
    moved: false,
  };
  el.chart.setPointerCapture(event.pointerId);
});

el.chart.addEventListener("pointermove", (event) => {
  if (pan && pan.id === event.pointerId) {
    const dx = event.clientX - pan.x;
    if (Math.abs(dx) > 2) {
      pan.moved = true;
      el.chart.classList.add("is-panning");
      hideTip();
    }
    if (!pan.moved) return;
    const rect = el.chart.getBoundingClientRect();
    const span = pan.end - pan.start;
    const delta = rect.width > 0 ? (-dx / rect.width) * span : 0;
    setView(pan.start + delta, pan.end + delta);
    render();
    return;
  }
  if (!el.chart.hidden) showTip(event);
});

function endPan(event) {
  if (!pan || pan.id !== event.pointerId) return;
  pan = null;
  el.chart.classList.remove("is-panning");
}

el.chart.addEventListener("pointerup", endPan);
el.chart.addEventListener("pointercancel", endPan);
el.chart.addEventListener("pointerleave", () => {
  if (!pan) hideTip();
});

el.chart.addEventListener("dblclick", () => {
  if (state.viewEnd - state.viewStart >= 0.999) return;
  state.viewStart = 0;
  state.viewEnd = 1;
  render();
});

el.chartFrame.addEventListener(
  "wheel",
  (event) => {
    if (el.chart.hidden) return;
    if (Math.abs(event.deltaX) > Math.abs(event.deltaY)) {
      if (state.viewEnd - state.viewStart >= 0.999) return;
      event.preventDefault();
      const span = state.viewEnd - state.viewStart;
      const rect = el.chart.getBoundingClientRect();
      const delta = rect.width > 0 ? (event.deltaX / rect.width) * span : 0;
      setView(state.viewStart + delta, state.viewEnd + delta);
      render();
      return;
    }
    event.preventDefault();
    zoomAt(event.deltaY > 0 ? 1 / 1.2 : 1.2, event.clientX);
  },
  { passive: false },
);

el.chartPan.addEventListener("scroll", () => {
  if (state.syncingPan || pan) return;
  const span = state.viewEnd - state.viewStart;
  const maxScroll = el.chartPan.scrollWidth - el.chartPan.clientWidth;
  if (maxScroll <= 0) return;
  const start = (el.chartPan.scrollLeft / maxScroll) * (1 - span);
  if (Math.abs(start - state.viewStart) < 0.001) return;
  state.viewStart = start;
  state.viewEnd = start + span;
  render();
});

boot().catch(() => {
  el.notice.textContent = "Could not load crossword stats.";
});
