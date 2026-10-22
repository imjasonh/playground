import type { SidebarView } from "./types.js";

/** Wrap text to a column width, keeping the author's own line breaks. */
export function wrapText(text: string, width: number): string[] {
  const cols = Math.max(1, width);
  const out: string[] = [];
  for (const rawLine of text.replace(/\r/g, "").split("\n")) {
    if (rawLine === "") {
      out.push("");
      continue;
    }
    let line = "";
    for (const word of rawLine.split(/\s+/u)) {
      if (word === "") continue;
      if (line === "") {
        line = word;
      } else if (line.length + 1 + word.length <= cols) {
        line += ` ${word}`;
      } else {
        out.push(line);
        line = word;
      }
      // A single word longer than the pane is hard-split so it never overflows.
      while (line.length > cols) {
        out.push(line.slice(0, cols));
        line = line.slice(cols);
      }
    }
    out.push(line);
  }
  return out;
}

const STATUS_LABEL: Record<SidebarView["status"], string> = {
  watching: "watching",
  thinking: "thinking…",
  paused: "paused",
  over: "game over",
};

/** Build the sidebar as an array of text lines, each already fit to `width`. */
export function layoutSidebar(view: SidebarView, width: number): string[] {
  const cols = Math.max(12, width);
  const rule = "─".repeat(cols);
  const lines: string[] = [];
  lines.push(fit("NetHack Coach", cols));
  lines.push(rule);

  const body = view.status === "over" && !view.advice ? "The game has ended." : view.advice;
  const bodyLines = body ? wrapText(body, cols) : wrapText(idleHint(view), cols);
  lines.push(...bodyLines);

  if (view.note) {
    lines.push("");
    lines.push(...wrapText(view.note, cols));
  }

  lines.push("");
  lines.push(rule);
  lines.push(fit(`${STATUS_LABEL[view.status]}  auto ${view.auto ? "on" : "off"}`, cols));
  lines.push(fit(costLine(view), cols));
  lines.push(fit("F9 ask  F10 auto  F8 quit", cols));
  return lines;
}

/** Repaint the whole pane: clear, home, then the laid-out lines. */
export function paintSidebar(view: SidebarView, width: number, write: (s: string) => void): void {
  const lines = layoutSidebar(view, width);
  write(`\x1b[2J\x1b[H${lines.join("\r\n")}`);
}

function idleHint(view: SidebarView): string {
  if (!view.auto) return "Automatic advice is off. Press F9 for advice on this screen.";
  return "Watching the game. Advice appears when the screen settles, or press F9.";
}

function costLine(view: SidebarView): string {
  const tokens = view.tokens.toLocaleString("en-US");
  if (view.costCents === undefined) return `${tokens} tokens`;
  return `${tokens} tokens  ${formatDollars(view.costCents)}`;
}

function fit(text: string, width: number): string {
  return text.length <= width ? text : text.slice(0, width);
}

function formatDollars(cents: number): string {
  if (!Number.isFinite(cents)) return "$0.00";
  return `$${(cents / 100).toFixed(2)}`;
}
