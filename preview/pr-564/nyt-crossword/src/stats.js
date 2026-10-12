// Pure stats for the crossword page. No DOM, no network.

export const WEEKDAYS = [
  "Monday",
  "Tuesday",
  "Wednesday",
  "Thursday",
  "Friday",
  "Saturday",
  "Sunday",
];

const MONTHS = [
  "January",
  "February",
  "March",
  "April",
  "May",
  "June",
  "July",
  "August",
  "September",
  "October",
  "November",
  "December",
];

const MONTHS_SHORT = [
  "Jan",
  "Feb",
  "Mar",
  "Apr",
  "May",
  "Jun",
  "Jul",
  "Aug",
  "Sep",
  "Oct",
  "Nov",
  "Dec",
];

export function weekdayName(isoDate) {
  const [year, month, day] = isoDate.split("-").map(Number);
  const index = new Date(Date.UTC(year, month - 1, day)).getUTCDay();
  return WEEKDAYS[(index + 6) % 7];
}

export function weekdayIndex(isoDate) {
  return WEEKDAYS.indexOf(weekdayName(isoDate));
}

export function puzzleUrl(isoDate) {
  const [year, month, day] = isoDate.split("-");
  return `https://www.nytimes.com/crosswords/game/daily/${year}/${month}/${day}`;
}

export function isPartial(puzzle) {
  return puzzle.solved !== true && puzzle.percentFilled > 0;
}

export function formatSolveTime(seconds) {
  if (!(seconds > 0) || !Number.isFinite(seconds)) return "";
  const total = Math.round(seconds);
  const hours = Math.floor(total / 3600);
  const minutes = Math.floor((total % 3600) / 60);
  const secs = total % 60;
  const pad = (n) => String(n).padStart(2, "0");
  if (hours > 0) return `${hours}:${pad(minutes)}:${pad(secs)}`;
  return `${minutes}:${pad(secs)}`;
}

export function formatPercent(value) {
  if (!Number.isFinite(value)) return "0%";
  return `${Math.round(value)}%`;
}

export function formatDate(isoDate) {
  const [year, month, day] = isoDate.split("-").map(Number);
  return new Intl.DateTimeFormat("en-US", {
    timeZone: "UTC",
    weekday: "long",
    month: "long",
    day: "numeric",
    year: "numeric",
  }).format(new Date(Date.UTC(year, month - 1, day)));
}

export function formatUpdated(iso) {
  const date = new Date(iso);
  if (Number.isNaN(date.getTime())) return "";
  return new Intl.DateTimeFormat("en-US", {
    timeZone: "UTC",
    month: "long",
    day: "numeric",
    year: "numeric",
    hour: "numeric",
    minute: "2-digit",
    timeZoneName: "short",
  }).format(date);
}

export function median(values) {
  if (values.length === 0) return null;
  const sorted = values.slice().sort((a, b) => a - b);
  const mid = Math.floor(sorted.length / 2);
  if (sorted.length % 2 === 1) return sorted[mid];
  return (sorted[mid - 1] + sorted[mid]) / 2;
}

function quantile(sorted, p) {
  if (sorted.length === 0) return null;
  const idx = (sorted.length - 1) * p;
  const lo = Math.floor(idx);
  const hi = Math.ceil(idx);
  if (lo === hi) return sorted[lo];
  const frac = idx - lo;
  return sorted[lo] * (1 - frac) + sorted[hi] * frac;
}

const DATE_RE = /^\d{4}-\d{2}-\d{2}$/;

// Dates listed in excluded.json. Short and long solves go in the same file.
export function excludedDates(raw) {
  const rows = raw && Array.isArray(raw.dates) ? raw.dates : [];
  const dates = new Set();
  for (const row of rows) {
    if (typeof row === "string" && DATE_RE.test(row)) dates.add(row);
  }
  return dates;
}

// Tukey fences per weekday. Needs four solves. A time far above or below
// the middle of that weekday lands outside the fence.
export function fencesByWeekday(puzzles) {
  const groups = new Map(WEEKDAYS.map((day) => [day, []]));
  for (const puzzle of puzzles) {
    const day = weekdayName(puzzle.date);
    const group = groups.get(day);
    if (group) group.push(puzzle.seconds);
  }
  const fences = new Map();
  for (const [day, values] of groups) {
    if (values.length >= 4) {
      const sorted = values.slice().sort((a, b) => a - b);
      const q1 = quantile(sorted, 0.25);
      const q3 = quantile(sorted, 0.75);
      const iqr = q3 - q1;
      fences.set(day, { lower: q1 - 1.5 * iqr, upper: q3 + 1.5 * iqr });
    }
  }
  return fences;
}

export function maxSecondsFromMinutes(raw) {
  const trimmed = String(raw ?? "").trim();
  if (trimmed === "") return null;
  const minutes = Number(trimmed);
  if (!Number.isFinite(minutes) || minutes < 0) return null;
  return minutes * 60;
}

function yearOf(isoDate) {
  return Number(isoDate.slice(0, 4));
}

function inYearRange(isoDate, fromYear, throughYear) {
  const year = yearOf(isoDate);
  return year >= fromYear && year <= throughYear;
}

// Listed dates come off before the fence is computed, so one excluded time
// does not widen the range for that weekday.
export function selectSolves(puzzles, options = {}) {
  const fromYear = options.fromYear ?? -Infinity;
  const throughYear = options.throughYear ?? Infinity;
  const listed = options.excludedDates ?? new Set();
  const maxSeconds = options.maxSeconds ?? null;
  const hideOutliers = options.hideOutliers === true;

  const excluded = [];
  const pool = [];
  for (const puzzle of puzzles) {
    if (puzzle.solved !== true || !(puzzle.seconds > 0)) continue;
    if (!inYearRange(puzzle.date, fromYear, throughYear)) continue;
    if (listed.has(puzzle.date)) {
      excluded.push({ puzzle, reason: "listed" });
    } else if (maxSeconds != null && puzzle.seconds > maxSeconds) {
      excluded.push({ puzzle, reason: "over-limit" });
    } else {
      pool.push(puzzle);
    }
  }

  const fences = hideOutliers ? fencesByWeekday(pool) : new Map();
  const kept = [];
  for (const puzzle of pool) {
    const fence = fences.get(weekdayName(puzzle.date));
    const outside =
      fence != null && (puzzle.seconds > fence.upper || puzzle.seconds < fence.lower);
    if (hideOutliers && outside) {
      excluded.push({ puzzle, reason: "outlier" });
    } else {
      kept.push(puzzle);
    }
  }
  excluded.sort((a, b) => compareIso(b.puzzle.date, a.puzzle.date));
  return { kept, excluded, fences };
}

export function medianByWeekday(puzzles) {
  const groups = new Map(WEEKDAYS.map((day) => [day, []]));
  for (const puzzle of puzzles) {
    const group = groups.get(weekdayName(puzzle.date));
    if (group) group.push(puzzle.seconds);
  }
  return WEEKDAYS.map((weekday) => {
    const values = groups.get(weekday);
    return {
      weekday,
      count: values.length,
      median: values.length ? median(values) : null,
    };
  });
}

export function bucketKey(isoDate, bucket) {
  const year = isoDate.slice(0, 4);
  const month = Number(isoDate.slice(5, 7));
  if (bucket === "year") return year;
  if (bucket === "quarter") return `${year}-Q${Math.floor((month - 1) / 3) + 1}`;
  return `${year}-${isoDate.slice(5, 7)}`;
}

export function bucketLabel(bucket) {
  const quarter = /^(\d{4})-Q([1-4])$/.exec(bucket);
  if (quarter) return `${quarter[1]} Q${quarter[2]}`;
  const month = /^(\d{4})-(\d{2})$/.exec(bucket);
  if (month) {
    const name = MONTHS_SHORT[Number(month[2]) - 1];
    return `${name} ${month[1]}`;
  }
  return bucket;
}

export function bucketLabelLong(bucket) {
  const quarter = /^(\d{4})-Q([1-4])$/.exec(bucket);
  if (quarter) return `${quarter[1]} Q${quarter[2]}`;
  const month = /^(\d{4})-(\d{2})$/.exec(bucket);
  if (month) {
    const name = MONTHS[Number(month[2]) - 1];
    return `${name} ${month[1]}`;
  }
  return bucket;
}

export function trendByWeekday(puzzles, bucket) {
  const groups = new Map(WEEKDAYS.map((day) => [day, new Map()]));
  for (const puzzle of puzzles) {
    const day = weekdayName(puzzle.date);
    const byBucket = groups.get(day);
    if (!byBucket) continue;
    const key = bucketKey(puzzle.date, bucket);
    const list = byBucket.get(key);
    if (list) list.push(puzzle.seconds);
    else byBucket.set(key, [puzzle.seconds]);
  }
  return WEEKDAYS.map((weekday) => {
    const byBucket = groups.get(weekday);
    const points = [...byBucket.keys()].sort().map((key) => {
      const values = byBucket.get(key);
      return { bucket: key, median: median(values), count: values.length };
    });
    return { weekday, points };
  });
}

export function solvedYears(puzzles) {
  const years = new Set();
  for (const puzzle of puzzles) {
    if (puzzle.solved === true && puzzle.seconds > 0) years.add(yearOf(puzzle.date));
  }
  return [...years].sort((a, b) => a - b);
}

export function partialPuzzles(puzzles, sort) {
  const rows = puzzles.filter((puzzle) => isPartial(puzzle));
  rows.sort((a, b) => comparePartial(a, b, sort));
  return rows;
}

function compareIso(a, b) {
  if (a === b) return 0;
  if (a < b) return -1;
  return 1;
}

function comparePartial(a, b, sort) {
  if (sort === "percent") {
    if (a.percentFilled !== b.percentFilled) return b.percentFilled - a.percentFilled;
    return compareIso(b.date, a.date);
  }
  if (sort === "weekday") {
    const byDay = weekdayIndex(a.date) - weekdayIndex(b.date);
    if (byDay !== 0) return byDay;
    return compareIso(a.date, b.date);
  }
  return compareIso(b.date, a.date);
}

export function niceMinuteStep(maxMinutes) {
  const steps = [1, 2, 5, 10, 15, 20, 30, 60, 120, 180, 240];
  const target = Math.max(maxMinutes, 1) / 4;
  for (const step of steps) {
    if (step >= target) return step;
  }
  return 360;
}

export function formatAxisMinutes(minutes) {
  if (minutes >= 60 && minutes % 60 === 0) return `${minutes / 60}h`;
  return `${minutes}m`;
}

function round1(n) {
  return Math.round(n * 10) / 10;
}

function pickTicks(buckets, maxTicks) {
  if (buckets.length <= maxTicks) return buckets.slice();
  const ticks = [];
  for (let i = 0; i < maxTicks; i += 1) {
    const idx = Math.round((i * (buckets.length - 1)) / (maxTicks - 1));
    const bucket = buckets[idx];
    if (ticks[ticks.length - 1] !== bucket) ticks.push(bucket);
  }
  return ticks;
}

export function chartLayout(series, { width = 960, height = 420 } = {}) {
  const pad = { top: 16, right: 16, bottom: 36, left: 56 };
  const innerW = width - pad.left - pad.right;
  const innerH = height - pad.top - pad.bottom;
  const seen = new Set();
  const buckets = [];
  let maxSeconds = 60;
  for (const seriesRow of series) {
    for (const point of seriesRow.points) {
      if (!seen.has(point.bucket)) {
        seen.add(point.bucket);
        buckets.push(point.bucket);
      }
      if (point.median > maxSeconds) maxSeconds = point.median;
    }
  }
  buckets.sort();
  const maxMinutes = maxSeconds / 60;
  const step = niceMinuteStep(maxMinutes);
  const yMaxMinutes = Math.max(step, Math.ceil(maxMinutes / step) * step);
  const yMax = yMaxMinutes * 60;
  const xOf = (bucket) => {
    if (buckets.length <= 1) return pad.left + innerW / 2;
    const index = buckets.indexOf(bucket);
    return pad.left + (index / (buckets.length - 1)) * innerW;
  };
  const yOf = (seconds) => pad.top + (1 - seconds / yMax) * innerH;
  const lines = series.map((seriesRow) => ({
    weekday: seriesRow.weekday,
    points: seriesRow.points.map((point) => ({
      bucket: point.bucket,
      median: point.median,
      count: point.count,
      x: round1(xOf(point.bucket)),
      y: round1(yOf(point.median)),
    })),
  }));
  const yTicks = [];
  for (let minutes = 0; minutes <= yMaxMinutes; minutes += step) {
    yTicks.push({
      minutes,
      y: round1(yOf(minutes * 60)),
      label: formatAxisMinutes(minutes),
    });
  }
  const picked = pickTicks(buckets, 6);
  const xTicks = picked.map((bucket, index) => {
    let anchor = "middle";
    if (picked.length > 1 && index === 0) anchor = "start";
    if (picked.length > 1 && index === picked.length - 1) anchor = "end";
    return {
      bucket,
      x: round1(xOf(bucket)),
      label: bucketLabel(bucket),
      anchor,
    };
  });
  return { width, height, pad, lines, yTicks, xTicks };
}
