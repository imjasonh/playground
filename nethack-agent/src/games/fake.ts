import type { Observation } from "../types.js";
import type { Game, GameBackend } from "./types.js";

/**
 * A small terminal stand-in for tests.
 * The agent prompt does not describe this map or these bytes.
 */
const WIDTH = 11;
const HEIGHT = 5;

type Tile = "." | "#" | "a" | "^" | ">";

type Vec = { x: number; y: number };

const DELTAS: Record<string, Vec> = {
  h: { x: -1, y: 0 },
  l: { x: 1, y: 0 },
  k: { x: 0, y: -1 },
  j: { x: 0, y: 1 },
  y: { x: -1, y: -1 },
  u: { x: 1, y: -1 },
  b: { x: -1, y: 1 },
  n: { x: 1, y: 1 },
};

export function createFakeBackend(): GameBackend {
  return {
    id: "fake",
    async start(ctx) {
      return new FakeGame(ctx.seed);
    },
  };
}

class FakeGame implements Game {
  private readonly tiles: Tile[][];
  private actor: Vec;
  private message = "";
  private turns = 0;
  private holding = "";
  private ended = false;

  constructor(seed: number) {
    const layout = layoutForSeed(seed);
    this.tiles = layout.tiles;
    this.actor = { ...layout.actor };
  }

  async observe(): Promise<Observation> {
    return { screen: this.render(), ended: this.ended };
  }

  async sendKeys(keys: string): Promise<Observation> {
    if (this.ended) return this.observe();
    for (const key of keys) {
      if (this.ended) break;
      this.apply(key);
    }
    return this.observe();
  }

  async close(): Promise<void> {
    this.ended = true;
  }

  private apply(key: string): void {
    this.turns += 1;
    if (key === ">" && this.underfoot() === ">") {
      this.message = "You ascend.";
      this.ended = true;
      return;
    }
    const delta = DELTAS[key];
    if (!delta) {
      this.message = "";
      return;
    }
    const next = { x: this.actor.x + delta.x, y: this.actor.y + delta.y };
    if (this.tileAt(next) === "#") {
      this.message = "";
      return;
    }
    this.actor = next;
    const landed = this.underfoot();
    if (landed === "a") {
      this.tiles[next.y][next.x] = ".";
      this.holding = "a";
      this.message = "";
      return;
    }
    if (landed === "^") {
      this.message = "You die.";
      this.ended = true;
      return;
    }
    this.message = "";
  }

  private underfoot(): Tile {
    return this.tileAt(this.actor);
  }

  private tileAt(pos: Vec): Tile {
    return this.tiles[pos.y]?.[pos.x] ?? "#";
  }

  private render(): string {
    const rows: string[] = [];
    rows.push(this.message.padEnd(WIDTH, " ").slice(0, Math.max(WIDTH, this.message.length)));
    for (let y = 0; y < HEIGHT; y++) {
      let line = "";
      for (let x = 0; x < WIDTH; x++) {
        if (this.actor.x === x && this.actor.y === y && !this.ended) {
          line += "@";
        } else if (this.actor.x === x && this.actor.y === y && this.ended) {
          line += this.tiles[y][x] === "^" || this.tiles[y][x] === ">" ? this.tiles[y][x] : "@";
        } else {
          line += this.tiles[y][x];
        }
      }
      rows.push(line);
    }
    const status = this.holding ? `t:${this.turns} ${this.holding}` : `t:${this.turns}`;
    rows.push(status);
    return rows.join("\n");
  }
}

function layoutForSeed(seed: number): { tiles: Tile[][]; actor: Vec } {
  const tiles = blankMap();
  const actor = { x: 1, y: 1 };
  if (seed === 1) {
    tiles[2][5] = "a";
    tiles[3][5] = "^";
    tiles[3][9] = ">";
    return { tiles, actor };
  }
  const spots = interiorSpots().filter((spot) => spot.x !== actor.x || spot.y !== actor.y);
  const rng = mulberry32(seed);
  const item = take(spots, rng);
  const trap = take(spots, rng);
  const goal = take(spots, rng);
  tiles[item.y][item.x] = "a";
  tiles[trap.y][trap.x] = "^";
  tiles[goal.y][goal.x] = ">";
  return { tiles, actor };
}

function blankMap(): Tile[][] {
  const tiles: Tile[][] = [];
  for (let y = 0; y < HEIGHT; y++) {
    const row: Tile[] = [];
    for (let x = 0; x < WIDTH; x++) {
      const edge = y === 0 || x === 0 || y === HEIGHT - 1 || x === WIDTH - 1;
      row.push(edge ? "#" : ".");
    }
    tiles.push(row);
  }
  return tiles;
}

function interiorSpots(): Vec[] {
  const spots: Vec[] = [];
  for (let y = 1; y < HEIGHT - 1; y++) {
    for (let x = 1; x < WIDTH - 1; x++) {
      spots.push({ x, y });
    }
  }
  return spots;
}

function take(spots: Vec[], rng: () => number): Vec {
  const index = Math.floor(rng() * spots.length);
  const [spot] = spots.splice(index, 1);
  return spot ?? { x: 1, y: 1 };
}

function mulberry32(seed: number): () => number {
  let state = seed >>> 0;
  return () => {
    state += 0x6d2b79f5;
    let t = state;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
