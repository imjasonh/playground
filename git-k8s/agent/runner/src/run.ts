import { createHash, randomBytes } from "node:crypto";
import { open, readFile, rename, rm, writeFile } from "node:fs/promises";
import { dirname, join } from "node:path";
import { cursorBackend } from "./backends/cursor.js";
import { fakeBackend } from "./backends/fake.js";
import type { Backend } from "./backends/types.js";
import { changedFiles, checkPaths } from "./changes.js";
import { buildPrompt, firstLines, MAX_DIFF, MAX_LOG } from "./prompt.js";
import type { ChangedFile, Result } from "./result.js";
import { parseTask, type BackendName, type Task } from "./task.js";
import { MAX_PATHS_BYTES, parseNameStatus } from "./touched.js";
import { errorMessage, redact, truncate } from "./text.js";
import { parseVerdict } from "./verdict.js";

/** Kubernetes keeps at most 4096 bytes of a termination message. */
const MAX_MESSAGE = 3500;

/** How long after the task's timeout the runner gives up on a run that doesn't stop. */
const GRACE_MS = 120_000;

export interface RunOptions {
  backends?: Partial<Record<BackendName, Backend>>;
  log?: (line: string) => void;
}

const defaultBackends: Record<BackendName, Backend> = { cursor: cursorBackend, fake: fakeBackend };

/**
 * Runs the task in AGENT_TASK, writes the result file, and writes the
 * result's SHA-256 digest as the container's termination message, which the
 * operator reads from the API server to check the result that it fetches.
 * On failure, the termination message is the error. Returns the exit code.
 */
export async function runFromEnv(env: NodeJS.ProcessEnv, options: RunOptions = {}): Promise<number> {
  const log = options.log ?? ((line: string) => console.log(line));
  let task: Task | undefined;
  let key = "";
  let watchdog: NodeJS.Timeout | undefined;
  try {
    task = parseTask(env.AGENT_TASK ?? "");
    key = await takeKey(task.keyFile);
    const deadline = task.timeoutSeconds * 1000 + GRACE_MS;
    const timedOut = new Promise<never>((_, reject) => {
      watchdog = setTimeout(() => reject(new Error(`the run didn't stop within ${Math.round(deadline / 1000)}s`)), deadline);
    });
    const result = await Promise.race([run(task, key, { ...defaultBackends, ...options.backends }, log), timedOut]);
    const body = Buffer.from(JSON.stringify(result));
    await writeAtomic(task.resultFile, body);
    await writeFile(task.terminationLog, `sha256:${createHash("sha256").update(body).digest("hex")}`);
    log(`verdict ${result.verdict}: ${result.summary}`);
    return 0;
  } catch (err) {
    const message = truncate(redact(errorMessage(err), key), MAX_MESSAGE);
    console.error(message);
    if (task) {
      await writeFile(task.terminationLog, message).catch(() => undefined);
    }
    return 1;
  } finally {
    clearTimeout(watchdog);
  }
}

/** Runs the agent on the task and builds its result. */
export async function run(task: Task, key: string, backends: Record<BackendName, Backend>, log: (line: string) => void): Promise<Result> {
  if (task.backend === "cursor" && !key) {
    throw new Error(`${task.keyFile} holds no Cursor API key; check the Secret that the Pod reads it from`);
  }
  const diff = await readStart(task.diffFile, MAX_DIFF + 1);
  const commits = await readStart(task.logFile, MAX_LOG + 1);
  const paths = task.changesFile ? parseNameStatus(await readStart(task.changesFile, MAX_PATHS_BYTES + 1)) : undefined;
  const index = task.edit ? await readFile(task.filesFile) : undefined;
  if (index) {
    checkPaths(index);
  }
  const started = Date.now();
  const response = await backends[task.backend]({
    prompt: buildPrompt(task, diff, commits, paths),
    diff: firstLines(diff, MAX_DIFF).text,
    cwd: task.workTree,
    edit: task.edit,
    model: task.model,
    apiKey: key,
    timeoutMs: task.timeoutSeconds * 1000,
    log,
  });
  const verdict = parseVerdict(response.text);
  const files: ChangedFile[] = [];
  if (index) {
    for (const change of await changedFiles(task.workTree, index)) {
      if (change.deleted) {
        files.push({ path: change.path, deleted: true });
        continue;
      }
      if (key && change.content.includes(key)) {
        throw new Error(`the agent wrote the Cursor API key to ${change.path}`);
      }
      files.push({ path: change.path, mode: change.mode, content: change.content.toString("base64") });
    }
  }
  const result: Result = {
    verdict: verdict.verdict,
    summary: redact(verdict.summary, key),
    reasoning: redact(verdict.reasoning, key),
    model: response.model,
    usage: response.usage,
    durationMs: Date.now() - started,
    files,
  };
  if (response.costCents !== undefined) {
    result.costCents = response.costCents;
  }
  return result;
}

/** Reads at most limit bytes from the start of a file. */
async function readStart(path: string, limit: number): Promise<Buffer> {
  const file = await open(path);
  try {
    const buf = Buffer.alloc(limit);
    let n = 0;
    while (n < limit) {
      const { bytesRead } = await file.read(buf, n, limit - n, n);
      if (bytesRead === 0) {
        break;
      }
      n += bytesRead;
    }
    return buf.subarray(0, n);
  } finally {
    await file.close();
  }
}

/**
 * Reads the API key and deletes its file, so the agent, which runs as the
 * same user, can't read it. The key stays out of the environment for the
 * same reason.
 */
async function takeKey(path: string): Promise<string> {
  if (!path) {
    return "";
  }
  let key: string;
  try {
    key = (await readFile(path, "utf8")).trim();
  } catch (err) {
    if ((err as NodeJS.ErrnoException).code === "ENOENT") {
      return "";
    }
    throw err;
  }
  await rm(path, { force: true });
  return key;
}

/**
 * Writes a file through a new file and a rename, so that a link that the
 * agent left at the path is replaced instead of followed.
 */
async function writeAtomic(path: string, data: Buffer): Promise<void> {
  const tmp = join(dirname(path), `.result-${randomBytes(8).toString("hex")}`);
  await writeFile(tmp, data, { flag: "wx", mode: 0o644 });
  await rename(tmp, path);
}
