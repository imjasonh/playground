import type {
  AgentTurn,
  ClueLeak,
  GameRecord,
  Move,
  OutcomeKind,
  TraceMessage,
} from "./types.js";
import {
  assistantSpeech,
  coalesceTraceMessages,
  stripMoveFences,
} from "./trace.js";

/** Render a game record as a self-contained HTML chat transcript. */
export function formatGameHtml(record: GameRecord): string {
  const title = escapeHtml(`It's Not Jaws — ${record.id.slice(0, 8)}`);
  const turnsHtml = record.turns.map((turn, i) => renderTurn(turn, i)).join("\n");
  const helpful = (record.clueLeaks ?? []).filter((l) => l.helpful && !l.isTitleLeak);

  return `<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8" />
<meta name="viewport" content="width=device-width, initial-scale=1" />
<title>${title}</title>
<style>
  :root {
    --bg: #f3efe6;
    --bg-accent: #e7e0d2;
    --ink: #1c1a17;
    --muted: #6f675c;
    --thinking: #8a8174;
    --line: #d5cdbf;
    --knower: #1f4b5a;
    --knower-bg: #d9e8ec;
    --guesser: #5c3d1e;
    --guesser-bg: #f0e2cf;
    --setup-bg: #ece7dc;
    --tool-bg: #f7f4ee;
    --badge: #2d2a26;
    --ok: #1f6b4a;
    --bad: #8b2e2e;
    --warn: #8a5a12;
  }
  * { box-sizing: border-box; }
  body {
    margin: 0;
    min-height: 100vh;
    font-family: "Iowan Old Style", "Palatino Linotype", Palatino, "Book Antiqua", Georgia, serif;
    color: var(--ink);
    background:
      radial-gradient(1200px 500px at 10% -10%, #fff9ef 0%, transparent 55%),
      radial-gradient(900px 400px at 100% 0%, #e5eef1 0%, transparent 50%),
      var(--bg);
  }
  .page {
    max-width: 760px;
    margin: 0 auto;
    padding: 2rem 1.25rem 4rem;
  }
  header.summary {
    margin-bottom: 1.75rem;
    padding-bottom: 1.25rem;
    border-bottom: 1px solid var(--line);
  }
  header.summary h1 {
    font-family: "Avenir Next", "Segoe UI", sans-serif;
    font-weight: 700;
    font-size: 1.55rem;
    letter-spacing: -0.02em;
    margin: 0 0 0.35rem;
  }
  header.summary .tagline {
    color: var(--muted);
    margin: 0 0 1rem;
    font-size: 0.98rem;
  }
  .meta {
    display: grid;
    grid-template-columns: repeat(auto-fit, minmax(140px, 1fr));
    gap: 0.65rem 1rem;
    font-family: "Avenir Next", "Segoe UI", sans-serif;
    font-size: 0.86rem;
  }
  .meta dt {
    color: var(--muted);
    font-size: 0.72rem;
    text-transform: uppercase;
    letter-spacing: 0.06em;
    margin: 0 0 0.15rem;
  }
  .meta dd {
    margin: 0;
    font-weight: 600;
    word-break: break-word;
  }
  .outcome {
    display: inline-block;
    margin-top: 1rem;
    padding: 0.35rem 0.7rem;
    border-radius: 999px;
    font-family: "Avenir Next", "Segoe UI", sans-serif;
    font-size: 0.82rem;
    font-weight: 700;
    letter-spacing: 0.02em;
  }
  .outcome.good { background: #d8f0e4; color: var(--ok); }
  .outcome.bad { background: #f5d6d6; color: var(--bad); }
  .outcome.warn { background: #f7e4c8; color: var(--warn); }
  .outcome.neutral { background: var(--bg-accent); color: var(--ink); }
  .outcome-reason {
    margin: 0.55rem 0 0;
    color: var(--muted);
    font-size: 0.92rem;
  }
  .clue-leaks {
    margin-top: 1rem;
    padding: 0.75rem 0.9rem;
    background: #f7e4c8;
    border: 1px solid #e2c48a;
    border-radius: 0.7rem;
    font-family: "Avenir Next", "Segoe UI", sans-serif;
    font-size: 0.86rem;
  }
  .clue-leaks h2 {
    margin: 0 0 0.45rem;
    font-size: 0.78rem;
    text-transform: uppercase;
    letter-spacing: 0.06em;
    color: var(--warn);
  }
  .clue-leaks ul {
    margin: 0;
    padding-left: 1.1rem;
  }
  .clue-leaks li { margin: 0.25rem 0; }
  .clue-leaks .evidence {
    display: block;
    color: var(--muted);
    font-size: 0.78rem;
    margin-top: 0.1rem;
  }
  .chat {
    display: flex;
    flex-direction: column;
    gap: 1rem;
  }
  .turn {
    display: flex;
    flex-direction: column;
    max-width: min(92%, 560px);
  }
  .turn.knower { align-self: flex-start; }
  .turn.guesser { align-self: flex-end; }
  .turn.setup { align-self: stretch; max-width: 100%; }
  .who {
    font-family: "Avenir Next", "Segoe UI", sans-serif;
    font-size: 0.75rem;
    font-weight: 700;
    letter-spacing: 0.04em;
    text-transform: uppercase;
    margin: 0 0 0.35rem 0.15rem;
  }
  .turn.knower .who { color: var(--knower); }
  .turn.guesser .who { color: var(--guesser); text-align: right; margin-right: 0.15rem; }
  .turn.setup .who { color: var(--muted); }
  .bubble {
    border-radius: 1.05rem;
    padding: 0.85rem 1rem;
    border: 1px solid transparent;
    box-shadow: 0 1px 0 rgba(28, 26, 23, 0.04);
  }
  .turn.knower .bubble {
    background: var(--knower-bg);
    border-color: #c5d8de;
    border-bottom-left-radius: 0.35rem;
  }
  .turn.guesser .bubble {
    background: var(--guesser-bg);
    border-color: #e2d0b4;
    border-bottom-right-radius: 0.35rem;
  }
  .turn.setup .bubble {
    background: var(--setup-bg);
    border: 1px dashed var(--line);
    border-radius: 0.85rem;
  }
  .move-badge {
    display: inline-block;
    margin: 0 0 0.65rem;
    padding: 0.2rem 0.55rem;
    border-radius: 999px;
    background: var(--badge);
    color: #f7f2ea;
    font-family: "Avenir Next", "Segoe UI", sans-serif;
    font-size: 0.72rem;
    font-weight: 700;
    letter-spacing: 0.03em;
  }
  .thinking {
    color: var(--thinking);
    font-style: italic;
    font-size: 0.92rem;
    line-height: 1.45;
    margin: 0 0 0.75rem;
    white-space: pre-wrap;
  }
  .thinking::before {
    content: "thinking";
    display: block;
    font-style: normal;
    font-family: "Avenir Next", "Segoe UI", sans-serif;
    font-size: 0.68rem;
    font-weight: 700;
    letter-spacing: 0.08em;
    text-transform: uppercase;
    color: #a39889;
    margin-bottom: 0.25rem;
  }
  .assistant {
    margin: 0;
    line-height: 1.5;
    white-space: pre-wrap;
    font-size: 1.02rem;
  }
  .assistant + .assistant { margin-top: 0.65rem; }
  .speech-empty {
    margin: 0 0 0.35rem;
    font-family: "Avenir Next", "Segoe UI", sans-serif;
    font-size: 0.8rem;
    color: var(--muted);
    font-style: italic;
  }
  .tool {
    margin: 0.65rem 0;
    padding: 0.55rem 0.7rem;
    background: var(--tool-bg);
    border: 1px solid var(--line);
    border-radius: 0.55rem;
    font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace;
    font-size: 0.78rem;
    line-height: 1.4;
    overflow-x: auto;
  }
  .tool .label {
    font-family: "Avenir Next", "Segoe UI", sans-serif;
    font-size: 0.68rem;
    font-weight: 700;
    letter-spacing: 0.06em;
    text-transform: uppercase;
    color: var(--muted);
    margin-bottom: 0.3rem;
  }
  .foot {
    margin-top: 0.45rem;
    font-family: "Avenir Next", "Segoe UI", sans-serif;
    font-size: 0.72rem;
    color: var(--muted);
  }
  .turn.guesser .foot { text-align: right; }
  .private-note {
    margin: 0 0 0.65rem;
    font-family: "Avenir Next", "Segoe UI", sans-serif;
    font-size: 0.78rem;
    color: var(--muted);
  }
</style>
</head>
<body>
  <div class="page">
    <header class="summary">
      <h1>It's Not Jaws</h1>
      <p class="tagline">Knower vs guesser — full published traces</p>
      <dl class="meta">
        <div><dt>Outcome</dt><dd>${escapeHtml(record.outcome.kind)}</dd></div>
        <div><dt>Secret</dt><dd>${escapeHtml(record.secret ?? "(none)")}</dd></div>
        <div><dt>Game length</dt><dd>${record.gameLength} guess${record.gameLength === 1 ? "" : "es"}</dd></div>
        <div><dt>Helpful clue leaks</dt><dd>${helpful.length}</dd></div>
        <div><dt>Knower</dt><dd>${escapeHtml(record.knowerModel ?? "—")}</dd></div>
        <div><dt>Guesser</dt><dd>${escapeHtml(record.guesserModel ?? "—")}</dd></div>
        <div><dt>Tokens</dt><dd>${record.usage.totalTokens.toLocaleString()}</dd></div>
        ${
          record.usage.totalRawCostCents != null
            ? `<div><dt>Cost</dt><dd>$${(record.usage.totalRawCostCents / 100).toFixed(4)}</dd></div>`
            : ""
        }
        <div><dt>Backend</dt><dd>${escapeHtml(record.backend)}</dd></div>
        <div><dt>Id</dt><dd>${escapeHtml(record.id)}</dd></div>
      </dl>
      <div class="outcome ${outcomeClass(record.outcome.kind)}">${escapeHtml(record.outcome.kind)}</div>
      <p class="outcome-reason">${escapeHtml(record.outcome.reason)}${
        record.outcome.detail
          ? ` — ${escapeHtml(record.outcome.detail)}`
          : ""
      }</p>
      ${renderClueLeakSummary(record.clueLeaks ?? [])}
    </header>
    <main class="chat">
${turnsHtml}
    </main>
  </div>
</body>
</html>
`;
}

function renderClueLeakSummary(leaks: ClueLeak[]): string {
  const helpful = leaks.filter((l) => l.helpful && !l.isTitleLeak);
  if (helpful.length === 0) return "";
  const items = helpful
    .map(
      (l) =>
        `<li><strong>turn ${l.turnIndex}</strong> (${escapeHtml(l.channel)}): ${escapeHtml(l.excerpt)}${
          l.evidence
            ? `<span class="evidence">${escapeHtml(l.evidence)}</span>`
            : ""
        }</li>`,
    )
    .join("\n");
  return `<div class="clue-leaks"><h2>Helpful non-title clue leaks</h2><ul>${items}</ul></div>`;
}

function renderTurn(turn: AgentTurn, index: number): string {
  const roleClass = turn.phase === "setup" ? "setup" : turn.role;
  const who =
    turn.phase === "setup"
      ? "Knower · private setup"
      : turn.role === "knower"
        ? "Knower"
        : "Guesser";
  const body = renderTurnBody(turn);
  const badge = turn.move ? renderMoveBadge(turn.move) : "";
  const privateNote =
    turn.phase === "setup"
      ? `<p class="private-note">Not shown to the guesser — harness ground truth only.</p>`
      : "";

  return `      <article class="turn ${roleClass}" data-turn="${index}" data-phase="${turn.phase}">
        <div class="who">${escapeHtml(who)}</div>
        <div class="bubble">
          ${privateNote}
          ${badge}
          ${body}
        </div>
        <div class="foot">turn ${turn.turnIndex} · ${turn.durationMs}ms${
          turn.usage ? ` · ${turn.usage.totalTokens} tokens` : ""
        }</div>
      </article>`;
}

function renderTurnBody(turn: AgentTurn): string {
  const messages = coalesceTraceMessages(turn.public.messages);
  const parts: string[] = [];
  let sawSpeech = false;

  for (const message of messages) {
    if (message.type === "thinking") {
      const text = message.text.trim();
      if (!text) continue;
      parts.push(`<div class="thinking">${escapeHtml(text)}</div>`);
      continue;
    }
    if (message.type === "assistant") {
      const text = stripMoveFences(message.text);
      if (!text) continue;
      sawSpeech = true;
      parts.push(`<p class="assistant">${escapeHtml(text)}</p>`);
      continue;
    }
    parts.push(renderTool(message));
  }

  if (!sawSpeech && turn.move) {
    parts.push(
      `<p class="speech-empty">${escapeHtml(speechPlaceholder(turn.move))}</p>`,
    );
  }

  if (parts.length === 0) {
    return `<p class="assistant">(no messages)</p>`;
  }
  return parts.join("\n");
}

function speechPlaceholder(move: Move): string {
  switch (move.type) {
    case "commit":
      return "(committed secret via structured move)";
    case "shared_fact":
      return "(issued shared fact via structured move)";
    case "guess":
      return "(submitted guess via structured move)";
    case "give_up":
      return "(gave up via structured move)";
    case "meta":
      return "(submitted meta move)";
  }
}

function renderTool(
  message: Extract<TraceMessage, { type: "tool_call" }>,
): string {
  const args =
    message.args !== undefined ? `\nargs: ${safeJson(message.args)}` : "";
  const result =
    message.result !== undefined
      ? `\nresult: ${safeJson(message.result)}`
      : "";
  return `<div class="tool"><div class="label">tool · ${escapeHtml(message.name)} · ${escapeHtml(message.status)}</div><pre>${escapeHtml(`${args}${result}`.trim() || "(no payload)")}</pre></div>`;
}

function renderMoveBadge(move: Move): string {
  let label: string;
  switch (move.type) {
    case "commit":
      label = `commit · ${move.secret}`;
      break;
    case "shared_fact":
      label = `shared fact · ${move.text}`;
      break;
    case "guess":
      label = `guess · ${move.value}`;
      break;
    case "give_up":
      label = move.reason ? `give up · ${move.reason}` : "give up";
      break;
    case "meta":
      label = `meta · ${move.text}`;
      break;
  }
  return `<div class="move-badge">${escapeHtml(label)}</div>`;
}

function outcomeClass(kind: OutcomeKind): string {
  switch (kind) {
    case "guesser_correct":
    case "knower_wins":
      return "good";
    case "secret_leaked":
    case "unguessable":
    case "protocol_error":
      return "bad";
    case "max_turns":
      return "warn";
    default:
      return "neutral";
  }
}

/** @deprecated Prefer stripMoveFences — kept for older imports/tests. */
export function stripTrailingMoveFence(text: string): string {
  return stripMoveFences(text);
}

export { assistantSpeech, stripMoveFences };

export function escapeHtml(value: string): string {
  return value
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;")
    .replaceAll("'", "&#39;");
}

function safeJson(value: unknown): string {
  try {
    return JSON.stringify(value, null, 2);
  } catch {
    return String(value);
  }
}
