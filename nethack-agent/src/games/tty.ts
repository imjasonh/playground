import { spawn, type ChildProcessWithoutNullStreams } from "node:child_process";
import { mkdir } from "node:fs/promises";
import { createInterface } from "node:readline";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { LIMITS } from "../limits.js";
import type { Observation } from "../types.js";
import type { Game, GameBackend } from "./types.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const bridgePath = path.resolve(here, "../../pty_bridge.py");

export type TtyOptions = {
  command: string;
  args?: string[];
  cols?: number;
  rows?: number;
  idleMs?: number;
  startTimeoutMs?: number;
  python?: string;
};

export function createTtyBackend(options: TtyOptions): GameBackend {
  return {
    id: "tty",
    async start(ctx) {
      return TtyGame.start(options, ctx.lifeDir);
    },
  };
}

type BridgeMsg = { type: string; b64?: string; code?: number };

class TtyGame implements Game {
  private readonly term: import("@xterm/headless").Terminal;
  private readonly child: ChildProcessWithoutNullStreams;
  private readonly idleMs: number;
  private ended = false;
  private closed = false;
  private readonly inbox: BridgeMsg[] = [];
  private readonly waiters: Array<(msg: BridgeMsg | null) => void> = [];
  private readonly chunks: string[] = [];

  private constructor(
    term: import("@xterm/headless").Terminal,
    child: ChildProcessWithoutNullStreams,
    idleMs: number,
  ) {
    this.term = term;
    this.child = child;
    this.idleMs = idleMs;
  }

  static async start(options: TtyOptions, lifeDir: string): Promise<TtyGame> {
    const cols = options.cols ?? 80;
    const rows = options.rows ?? 24;
    const idleMs = options.idleMs ?? LIMITS.DEFAULT_TTY_IDLE_MS;
    const startTimeoutMs = options.startTimeoutMs ?? LIMITS.DEFAULT_TTY_START_MS;
    await mkdir(lifeDir, { recursive: true });
    const { Terminal } = await import("@xterm/headless");
    const term = new Terminal({ cols, rows, allowProposedApi: true });
    const env: NodeJS.ProcessEnv = {
      ...process.env,
      HOME: lifeDir,
      TERM: "xterm-256color",
      LANG: process.env.LANG || "C.UTF-8",
      PTY_COLS: String(cols),
      PTY_ROWS: String(rows),
    };
    // A parent options value would be a spoiled config. Drop it.
    // Leave the binary's own prompts on the screen.
    delete env.NETHACKOPTIONS;
    const child = spawn(
      options.python ?? "python3",
      [bridgePath, options.command, ...(options.args ?? [])],
      {
        cwd: lifeDir,
        env,
        stdio: ["pipe", "pipe", "pipe"],
      },
    ) as ChildProcessWithoutNullStreams;

    const game = new TtyGame(term, child, idleMs);
    game.attach();
    const first = await game.settle(startTimeoutMs);
    if (!first && !game.ended) {
      await game.close();
      throw new Error(`no screen from ${options.command} within ${startTimeoutMs}ms`);
    }
    return game;
  }

  async observe(): Promise<Observation> {
    await this.flush();
    return { screen: this.snapshot(), ended: this.ended };
  }

  async sendKeys(keys: string): Promise<Observation> {
    if (this.ended || this.closed) return this.observe();
    if (keys) {
      this.write({ type: "write", b64: Buffer.from(keys, "utf8").toString("base64") });
      await this.settle(Math.max(this.idleMs * 10, 1000));
    }
    return this.observe();
  }

  async close(): Promise<void> {
    if (this.closed) return;
    this.closed = true;
    this.ended = true;
    this.write({ type: "close" });
    await new Promise<void>((resolve) => {
      const timer = setTimeout(() => {
        this.child.kill("SIGKILL");
        resolve();
      }, 1000);
      this.child.once("exit", () => {
        clearTimeout(timer);
        resolve();
      });
    });
  }

  private attach(): void {
    const lines = createInterface({ input: this.child.stdout });
    lines.on("line", (line) => {
      let msg: BridgeMsg;
      try {
        msg = JSON.parse(line) as BridgeMsg;
      } catch {
        return;
      }
      if (msg.type === "bytes" && msg.b64) {
        this.chunks.push(Buffer.from(msg.b64, "base64").toString("utf8"));
      } else if (msg.type === "exit") {
        this.ended = true;
      }
      this.push(msg);
    });
    this.child.on("exit", () => {
      this.ended = true;
      this.push({ type: "exit" });
    });
  }

  private push(msg: BridgeMsg): void {
    const waiter = this.waiters.shift();
    if (waiter) waiter(msg);
    else this.inbox.push(msg);
  }

  private write(msg: { type: string; b64?: string }): void {
    if (!this.child.stdin || this.child.stdin.destroyed) return;
    this.child.stdin.write(`${JSON.stringify(msg)}\n`);
  }

  private async settle(timeoutMs: number): Promise<boolean> {
    const started = Date.now();
    let sawBytes = false;
    let lastBytesAt = 0;
    while (Date.now() - started < timeoutMs) {
      const remaining = timeoutMs - (Date.now() - started);
      const msg = await this.nextMessage(Math.min(this.idleMs, remaining));
      if (!msg) {
        if (sawBytes && Date.now() - lastBytesAt >= this.idleMs) {
          await this.flush();
          return true;
        }
        if (this.ended) {
          await this.flush();
          return sawBytes;
        }
        continue;
      }
      if (msg.type === "bytes") {
        sawBytes = true;
        lastBytesAt = Date.now();
      }
      if (msg.type === "exit") {
        await this.flush();
        return sawBytes;
      }
    }
    await this.flush();
    return sawBytes;
  }

  private nextMessage(timeoutMs: number): Promise<BridgeMsg | null> {
    const queued = this.inbox.shift();
    if (queued) return Promise.resolve(queued);
    return new Promise((resolve) => {
      const timer = setTimeout(() => {
        const index = this.waiters.indexOf(onMsg);
        if (index >= 0) this.waiters.splice(index, 1);
        resolve(null);
      }, Math.max(1, timeoutMs));
      const onMsg = (msg: BridgeMsg | null): void => {
        clearTimeout(timer);
        resolve(msg);
      };
      this.waiters.push(onMsg);
    });
  }

  private async flush(): Promise<void> {
    while (this.chunks.length > 0) {
      const chunk = this.chunks.shift() ?? "";
      await new Promise<void>((resolve) => {
        this.term.write(chunk, () => resolve());
      });
    }
  }

  private snapshot(): string {
    const buf = this.term.buffer.active;
    const lines: string[] = [];
    for (let y = 0; y < this.term.rows; y++) {
      const line = buf.getLine(y);
      lines.push(line ? line.translateToString(true) : "");
    }
    while (lines.length > 1 && lines[lines.length - 1].trim() === "") {
      lines.pop();
    }
    return lines.join("\n");
  }
}
