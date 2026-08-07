import type { GameDefinition } from "./games/types.js";
import { formatPublicChannel } from "./protocol.js";
import type { PublicChannel } from "./types.js";

export function keeperSystemPrompt(game: GameDefinition): string {
  return [
    `# Role: Keeper`,
    ``,
    game.keeperBrief,
    game.domainHint ? `Domain: ${game.domainHint}` : "",
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
    "1) Call commit_secret with your chosen secret.",
    "2) Give your first clue without naming the secret in thinking or text.",
    "3) End with a JSON clue move.",
  ].join("\n");
}

export function guesserPromptFromKeeper(channel: PublicChannel, round: number): string {
  return [
    `Round ${round}. Here is the keeper's published channel (thinking + text):`,
    ``,
    formatPublicChannel(channel),
    ``,
    "Make your next guess (or give up). End with a JSON move.",
  ].join("\n");
}

export function keeperPromptFromGuesser(channel: PublicChannel, round: number): string {
  return [
    `Round ${round}. Here is the guesser's published channel (thinking + text):`,
    ``,
    formatPublicChannel(channel),
    ``,
    "Give the next clue without naming the secret. End with a JSON clue move.",
  ].join("\n");
}
