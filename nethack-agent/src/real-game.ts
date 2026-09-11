import { existsSync } from "node:fs";

/** The fake screen is a test double. Learning runs only the installed binary. */
export function assertLearningGame(game: string): void {
  if (game !== "tty") {
    throw new Error(
      "The learning notebook is only written from the nethack process. The fake screen is for tests.",
    );
  }
}

export function defaultNethackCommand(): string {
  if (existsSync("/usr/games/nethack")) return "/usr/games/nethack";
  return "nethack";
}
