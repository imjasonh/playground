import path from "node:path";
import { RC_BEGIN, RC_END } from "./prompts.js";

export type RcSource = {
  /** `file`: read from `path`. `inline`: options came from NETHACKOPTIONS. `none`: nothing yet. */
  kind: "file" | "inline" | "none";
  /** The file to read and, with --write, to update. Present for `file`. */
  path?: string;
  /** The inline options string. Present for `inline`. */
  contents?: string;
};

/**
 * Work out where the player's NetHack configuration lives.
 *
 * An explicit `--file` wins. Otherwise NETHACKOPTIONS decides: `@path` or a value
 * that names an existing file is a file; any other non-empty value is inline
 * options. With nothing set, fall back to `~/.nethackrc`.
 */
export function resolveRcSource(input: {
  fileArg?: string;
  nethackoptions?: string;
  home: string;
  exists: (candidate: string) => boolean;
}): RcSource {
  if (input.fileArg) return { kind: "file", path: input.fileArg };

  const opt = input.nethackoptions?.trim();
  if (opt) {
    if (opt.startsWith("@")) return { kind: "file", path: expandHome(opt.slice(1), input.home) };
    const asPath = expandHome(opt, input.home);
    if (input.exists(asPath)) return { kind: "file", path: asPath };
    return { kind: "inline", contents: opt };
  }

  return { kind: "file", path: path.join(input.home, ".nethackrc") };
}

function expandHome(candidate: string, home: string): string {
  if (candidate === "~") return home;
  if (candidate.startsWith("~/")) return path.join(home, candidate.slice(2));
  return candidate;
}

export type SettingsReply = {
  /** The plain-text review before the config block. */
  review: string;
  /** The suggested .nethackrc, when the model returned a block. */
  config?: string;
};

/** Split the model's reply into the review text and the suggested config block. */
export function parseSettingsReply(text: string): SettingsReply {
  const begin = text.indexOf(RC_BEGIN);
  const end = text.indexOf(RC_END);
  if (begin < 0 || end < 0 || end < begin) {
    return { review: text.trim() };
  }
  const review = text.slice(0, begin).trim();
  const config = text.slice(begin + RC_BEGIN.length, end).replace(/^\n/, "").replace(/\n$/, "");
  return { review, config };
}

/** A timestamped backup path so --write never clobbers an existing config. */
export function backupPath(target: string, now: Date): string {
  const stamp = now.toISOString().replace(/[:.]/g, "-");
  return `${target}.bak.${stamp}`;
}
