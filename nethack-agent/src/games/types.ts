import type { Observation } from "../types.js";

export type Game = {
  observe(): Promise<Observation>;
  sendKeys(keys: string): Promise<Observation>;
  close(): Promise<void>;
};

export type GameStart = {
  lifeDir: string;
  seed: number;
};

export type GameBackend = {
  id: "fake" | "tty";
  start(ctx: GameStart): Promise<Game>;
};
