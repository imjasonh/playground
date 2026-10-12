// Pure planning for the NYT crossword scrape. The list endpoint returns
// solved and percent filled, not solve time, and it rejects ranges longer
// than 100 days. Game records fill in secondsSpentSolving.

export const API_ORIGIN = "https://www.nytimes.com";
export const DEFAULT_START = "2005-01-01";
export const CHUNK_DAYS = 100;

const DATE_RE = /^\d{4}-\d{2}-\d{2}$/;

export function isIsoDate(value) {
  if (typeof value !== "string" || !DATE_RE.test(value)) return false;
  const [year, month, day] = value.split("-").map(Number);
  const date = new Date(Date.UTC(year, month - 1, day));
  return (
    date.getUTCFullYear() === year &&
    date.getUTCMonth() === month - 1 &&
    date.getUTCDate() === day
  );
}

export function addDays(isoDate, days) {
  const [year, month, day] = isoDate.split("-").map(Number);
  const date = new Date(Date.UTC(year, month - 1, day));
  date.setUTCDate(date.getUTCDate() + days);
  return date.toISOString().slice(0, 10);
}

export function todayInNewYork(now = new Date()) {
  return new Intl.DateTimeFormat("en-CA", {
    timeZone: "America/New_York",
    year: "numeric",
    month: "2-digit",
    day: "2-digit",
  }).format(now);
}

export function dateChunks(start, end, span = CHUNK_DAYS) {
  if (!isIsoDate(start) || !isIsoDate(end) || start > end) {
    throw new Error(`Bad date range ${start}..${end}`);
  }
  const chunks = [];
  let cursor = start;
  while (cursor <= end) {
    const chunkEnd = addDays(cursor, span - 1);
    const endDate = chunkEnd < end ? chunkEnd : end;
    chunks.push([cursor, endDate]);
    cursor = addDays(endDate, 1);
  }
  return chunks;
}

export function listUrl(start, end) {
  const url = new URL("/svc/crosswords/v3/puzzles.json", API_ORIGIN);
  url.searchParams.set("publish_type", "daily");
  url.searchParams.set("sort_order", "asc");
  url.searchParams.set("sort_by", "print_date");
  url.searchParams.set("date_start", start);
  url.searchParams.set("date_end", end);
  return url;
}

export function gameUrl(id) {
  return new URL(`/svc/crosswords/v6/game/${id}.json`, API_ORIGIN);
}

export function cookieValue(raw) {
  const trimmed = String(raw ?? "").trim();
  const prefix = "NYT-S=";
  if (trimmed.startsWith(prefix)) return trimmed.slice(prefix.length).trim();
  return trimmed;
}

export function cookieHeader(raw) {
  return `NYT-S=${cookieValue(raw)}`;
}

export function listItemToPuzzle(item) {
  if (!item || typeof item !== "object") return null;
  const publish = item.publish_type;
  if (typeof publish === "string" && publish.toLowerCase() !== "daily") return null;
  if (!isIsoDate(item.print_date)) return null;
  const id = Number(item.puzzle_id);
  if (!Number.isInteger(id)) return null;
  const percent = Number(item.percent_filled);
  return {
    date: item.print_date,
    id,
    solved: item.solved === true,
    percentFilled: Number.isFinite(percent) ? percent : 0,
    seconds: null,
  };
}

// A stored solve time means the game is finished. It cannot become unsolved,
// so later runs leave that record alone.
export function isFinished(puzzle) {
  return Boolean(puzzle && puzzle.solved === true && puzzle.seconds > 0);
}

export function needsGameFetch(prev, listed) {
  if (isFinished(prev)) return false;
  const progressed = listed.solved === true || listed.percentFilled > 0;
  if (!prev) return progressed;
  if (prev.solved !== listed.solved || prev.percentFilled !== listed.percentFilled) return true;
  if (listed.solved === true && !(prev.seconds > 0)) return true;
  // The list row lags the game record, so unfinished puzzles are rechecked.
  if (listed.solved !== true && listed.percentFilled > 0) return true;
  return false;
}

export function mergeListed(prevPuzzles, listedItems, range) {
  const prevByDate = new Map((prevPuzzles ?? []).map((puzzle) => [puzzle.date, puzzle]));
  const merged = new Map();
  for (const puzzle of prevPuzzles ?? []) {
    if (puzzle.date < range.start || puzzle.date > range.end) {
      merged.set(puzzle.date, { puzzle, fetch: false });
    }
  }
  for (const item of listedItems ?? []) {
    const listed = listItemToPuzzle(item);
    if (!listed) continue;
    const prev = prevByDate.get(listed.date) ?? null;
    if (isFinished(prev)) {
      merged.set(prev.date, { puzzle: prev, fetch: false });
      continue;
    }
    const puzzle = {
      date: listed.date,
      id: listed.id,
      solved: listed.solved,
      percentFilled: listed.percentFilled,
      seconds: prev && prev.seconds > 0 ? prev.seconds : null,
    };
    merged.set(puzzle.date, { puzzle, fetch: needsGameFetch(prev, puzzle) });
  }
  const entries = [...merged.values()].sort((a, b) => (a.puzzle.date < b.puzzle.date ? -1 : 1));
  return {
    puzzles: entries.map((entry) => entry.puzzle),
    fetchList: entries.filter((entry) => entry.fetch).map((entry) => entry.puzzle),
  };
}

export function applyGame(puzzle, body) {
  const calcs =
    body && typeof body === "object" && body.calcs && typeof body.calcs === "object"
      ? body.calcs
      : {};
  if (isFinished(puzzle)) return { ...puzzle };
  const solved = typeof calcs.solved === "boolean" ? calcs.solved : puzzle.solved === true;
  const percent = Number(calcs.percentFilled);
  const spent = Number(calcs.secondsSpentSolving);
  let seconds = null;
  if (solved) {
    if (Number.isFinite(spent) && spent > 0) seconds = spent;
    else if (puzzle.seconds > 0) seconds = puzzle.seconds;
  }
  return {
    date: puzzle.date,
    id: puzzle.id,
    solved,
    percentFilled: Number.isFinite(percent) ? percent : puzzle.percentFilled,
    seconds,
  };
}

export function puzzlesEqual(a, b) {
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i += 1) {
    const left = a[i];
    const right = b[i];
    if (left.date !== right.date) return false;
    if (left.id !== right.id) return false;
    if (left.solved !== right.solved) return false;
    if (left.percentFilled !== right.percentFilled) return false;
    if (left.seconds !== right.seconds) return false;
  }
  return true;
}

export function serializeStats(doc) {
  const puzzles = doc.puzzles.map((puzzle) => ({
    date: puzzle.date,
    id: puzzle.id,
    solved: puzzle.solved === true,
    percentFilled: puzzle.percentFilled,
    seconds: puzzle.seconds > 0 ? puzzle.seconds : null,
  }));
  return `${JSON.stringify({ generatedAt: doc.generatedAt ?? null, puzzles }, null, 2)}\n`;
}

export function normalizeDoc(raw) {
  const puzzles = [];
  const rows = raw && Array.isArray(raw.puzzles) ? raw.puzzles : [];
  for (const row of rows) {
    if (!row || !isIsoDate(row.date)) continue;
    const id = Number(row.id);
    const percent = Number(row.percentFilled);
    const seconds = Number(row.seconds);
    puzzles.push({
      date: row.date,
      id: Number.isInteger(id) ? id : 0,
      solved: row.solved === true,
      percentFilled: Number.isFinite(percent) ? percent : 0,
      seconds: Number.isFinite(seconds) && seconds > 0 ? seconds : null,
    });
  }
  puzzles.sort((a, b) => (a.date < b.date ? -1 : 1));
  const generatedAt = raw && typeof raw.generatedAt === "string" ? raw.generatedAt : null;
  return { generatedAt, puzzles };
}
