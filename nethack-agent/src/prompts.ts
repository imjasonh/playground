import type { Memory } from "./types.js";
import { renderMemory } from "./memory.js";

/**
 * Interface contract only. Do not name the game, list commands, or describe a win.
 * The weights may already know the game. This text does not add a second teacher.
 */
export function systemPrompt(): string {
  return [
    "A process is attached. It shows a screen and waits for keys.",
    "",
    "Reply with one JSON object and no other text:",
    '{"keys":"<characters to send>"}',
    "",
    "Optional fields, same object:",
    '"note" string you want kept',
    '"retract" note id to drop',
    '"save" object {"name":"<short name>","keys":"<characters>"} to keep a key sequence you wrote',
    '"run" name of a sequence you already saved',
    '"quit" true to close this process without sending keys',
    "",
    "Keys are sent exactly. The next message is the new screen.",
    "When the process ends, this conversation ends. Notes, saved sequences, and the final screen are what a later attempt can see.",
    "A note is one claim that is still true if this screen is gone.",
    "Do not file where you are, the keys you just sent, or what to try next.",
    "The notebook is small. To add a note when it is full, retract one that is narrower or wrong.",
    "A saved sequence is a short series of keys that does the same thing on a later screen, not a path through this one.",
    "Anything you already believe is untested until a screen agrees with it.",
  ].join("\n");
}

export function playPrompt(input: {
  life: number;
  turn: number;
  screen: string;
  diff?: string;
  memory?: Memory;
  includeMemory: boolean;
  acks?: string[];
}): string {
  const parts = [`Life ${input.life}, turn ${input.turn}.`];
  if (input.acks && input.acks.length > 0) {
    parts.push("", input.acks.join("\n"));
  }
  if (input.includeMemory && input.memory) {
    const memory = renderMemory(input.memory);
    if (memory) {
      parts.push("", memory);
    }
  }
  parts.push("", "Current screen:", input.screen);
  if (input.diff) {
    parts.push("", "Screen difference:", input.diff);
  }
  return parts.join("\n");
}

export function debriefPrompt(input: { screen: string; acks?: string[] }): string {
  const parts = [
    "The process is no longer accepting keys.",
    "File a claim a later attempt can use on a different screen.",
    "Do not recap this path, where you were, or the keys you sent.",
    "You may reply with a JSON object that only contains note, save, or retract.",
    "The next attempt will not have this conversation.",
  ];
  if (input.acks && input.acks.length > 0) {
    parts.push("", input.acks.join("\n"));
  }
  parts.push("", "Final screen:", input.screen);
  return parts.join("\n");
}

export function retryPrompt(): string {
  return [
    "That reply did not contain a usable JSON object.",
    "Reply with one JSON object.",
    '{"keys":"<characters to send>"}',
    "Optional fields: note, retract, save, run, quit.",
  ].join("\n");
}

/** Words the harness must not introduce. Game output is not checked here. */
export const HARNESS_SPOILER_WORDS = [
  "nethack",
  "dungeon",
  "potion",
  "monster",
  "stair",
  "amulet",
  "yendor",
  "roguelike",
  "hjkl",
  "prayer",
  "valkyrie",
] as const;
