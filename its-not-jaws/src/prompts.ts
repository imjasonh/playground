import type { GameDefinition } from "./games/types.js";
import { formatPublicChannel } from "./protocol.js";
import type { PublicChannel } from "./types.js";

export function knowerSystemPrompt(game: GameDefinition): string {
  return [
    `# Role: Knower (Agent A)`,
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
    `# Role: Guesser (Agent B)`,
    ``,
    game.guesserBrief,
    game.domainHint ? `Domain: ${game.domainHint}` : "",
    ``,
    `Protocol: always end your reply with a single fenced JSON move.`,
  ]
    .filter(Boolean)
    .join("\n");
}

/** Private setup: knower picks and commits the movie to the harness only. */
export function knowerSetupPrompt(): string {
  return [
    "SETUP (private — the guesser will not see this turn).",
    "Pick a real, fairly well-known movie title, then reply with ONLY a commit move:",
    '```json\n{"type":"commit","secret":"Movie Title"}\n```',
    "Do not give shared facts yet. The guesser moves first after setup.",
  ].join("\n");
}

export function guesserOpeningPrompt(): string {
  return [
    "The knower has secretly picked a real, fairly well-known movie.",
    "Make your first guess. You have no shared facts yet.",
    "End with a JSON guess move.",
  ].join("\n");
}

export function guesserPromptFromKnower(
  channel: PublicChannel,
  round: number,
  sharedFacts: string[],
): string {
  const factsBlock =
    sharedFacts.length === 0
      ? "(none yet)"
      : sharedFacts.map((f, i) => `${i + 1}. ${f}`).join("\n");
  return [
    `Round ${round}.`,
    ``,
    `Shared facts so far (true of both your previous guesses and the secret movie):`,
    factsBlock,
    ``,
    `Here is the knower's FULL published trace for their latest reply`,
    `(thinking, assistant text, and tool calls with args/results):`,
    ``,
    formatPublicChannel(channel),
    ``,
    "Make your next guess (or give up). End with a JSON move.",
  ].join("\n");
}

export function knowerPromptFromGuesser(
  channel: PublicChannel,
  guess: string,
  round: number,
): string {
  return [
    `Round ${round}. The guesser guessed: ${JSON.stringify(guess)}`,
    ``,
    `Here is the guesser's FULL published trace`,
    `(thinking, assistant text, and tool calls with args/results):`,
    ``,
    formatPublicChannel(channel),
    ``,
    "If that guess is NOT your movie, name ONE fact that their guess and your movie share.",
    "CRITICAL: your thinking is public. Do NOT write the secret title in thinking or text",
    "(not even as \"the committed movie is …\" or while comparing). A leak scores secret_leaked",
    "and you lose the round immediately.",
    "End with a JSON shared_fact move.",
    "If they somehow already have it right, you may acknowledge; the harness scores matches.",
  ].join("\n");
}
