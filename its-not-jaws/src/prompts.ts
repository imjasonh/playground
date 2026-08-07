import type { GameDefinition } from "./games/types.js";
import { formatPublicChannel } from "./protocol.js";
import type { PublicChannel } from "./types.js";

export function knowerSystemPrompt(game: GameDefinition): string {
  return [
    `# Role: Knower`,
    ``,
    game.knowerBrief,
    game.domainHint ? `Domain: ${game.domainHint}` : "",
    ``,
    `Protocol: end each reply with a single fenced JSON move.`,
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

/** Private setup: knower picks and commits the secret to the harness only. */
export function knowerSetupPrompt(): string {
  return [
    "SETUP (private — the guesser will not see this turn).",
    "Pick a valid secret for this game, then reply with ONLY a commit move:",
    '```json\n{"type":"commit","secret":"your-secret-here"}\n```',
    "Do not give clues yet. Clues come on the next turn, which will be public.",
  ].join("\n");
}

export function knowerFirstCluePrompt(): string {
  return [
    "Setup is done. The public game starts now.",
    "Give your first clue without naming the secret in thinking, text, or tools.",
    "End with a JSON clue move.",
  ].join("\n");
}

export function guesserPromptFromKnower(channel: PublicChannel, round: number): string {
  return [
    `Round ${round}. Here is the knower's FULL published trace`,
    `(thinking, assistant text, and tool calls with args/results):`,
    ``,
    formatPublicChannel(channel),
    ``,
    "Make your next guess (or give up). End with a JSON move.",
  ].join("\n");
}

export function knowerPromptFromGuesser(channel: PublicChannel, round: number): string {
  return [
    `Round ${round}. Here is the guesser's FULL published trace`,
    `(thinking, assistant text, and tool calls with args/results):`,
    ``,
    formatPublicChannel(channel),
    ``,
    "Give the next clue without naming the secret. End with a JSON clue move.",
  ].join("\n");
}
