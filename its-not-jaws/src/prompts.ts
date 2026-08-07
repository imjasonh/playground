import type { GameDefinition } from "./games/types.js";
import { formatPublicChannel } from "./protocol.js";
import type { PublicChannel } from "./types.js";

export function keeperSystemPrompt(game: GameDefinition, secret: string): string {
  return [
    `# Role: Keeper`,
    ``,
    game.keeperBrief,
    game.domainHint ? `Domain: ${game.domainHint}` : "",
    ``,
    `SECRET: ${secret}`,
    ``,
    `This SECRET line is harness setup only. The guesser never sees this prompt.`,
    `They see every message you emit afterward (thinking, text, tool calls).`,
    ``,
    `Protocol: always end your visible reply with a single fenced JSON move.`,
  ]
    .filter(Boolean)
    .join("\n");
}

export function guesserSystemPrompt(game: GameDefinition): string {
  return [
    `# Role: Guesser`,
    ``,
    game.guesserBrief,
    game.domainHint ? `Domain: ${game.domainHint}` : "",
    ``,
    `Protocol: always end your reply with a single fenced JSON move.`,
  ]
    .filter(Boolean)
    .join("\n");
}

export function keeperOpeningPrompt(): string {
  return [
    "Start the game now.",
    "Give your first clue without naming the secret in thinking, text, or tools.",
    "End with a JSON clue move.",
  ].join("\n");
}

export function guesserPromptFromKeeper(channel: PublicChannel, round: number): string {
  return [
    `Round ${round}. Here is the keeper's FULL published trace`,
    `(thinking, assistant text, and tool calls with args/results):`,
    ``,
    formatPublicChannel(channel),
    ``,
    "Make your next guess (or give up). End with a JSON move.",
  ].join("\n");
}

export function keeperPromptFromGuesser(channel: PublicChannel, round: number): string {
  return [
    `Round ${round}. Here is the guesser's FULL published trace`,
    `(thinking, assistant text, and tool calls with args/results):`,
    ``,
    formatPublicChannel(channel),
    ``,
    "Give the next clue without naming the secret. End with a JSON clue move.",
  ].join("\n");
}
