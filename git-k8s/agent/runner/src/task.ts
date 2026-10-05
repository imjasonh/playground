import { checkTools } from "./tools.js";

/** The backends that can run a task. */
export const BACKENDS = ["cursor", "fake"] as const;

export type BackendName = (typeof BACKENDS)[number];

/**
 * One agent task, as the operator writes it to the AGENT_TASK environment
 * variable of the Pod's agent container.
 */
export interface Task {
  backend: BackendName;
  model: string;
  instructions: string;
  /** Lets the agent edit files; the runner reports the files it changed. */
  edit: boolean;
  /** The agent's tools, if not all that edit allows. */
  tools?: string[];
  timeoutSeconds: number;
  branch: string;
  parent: string;
  head: string;
  /** The merge base of the branch and its parent, or "" if they have none. */
  base: string;
  /** The head commit's files. It isn't a git repository. */
  workTree: string;
  /** The change from base to head, from git diff. */
  diffFile: string;
  /** The branch's commits since base, one per line. */
  logFile: string;
  /** The head commit's index, from git ls-files -s -z. */
  filesFile: string;
  /** The paths that the change touches, from git diff --name-status -z. */
  changesFile?: string;
  /** Holds the Cursor API key. The runner deletes it before the agent starts. */
  keyFile: string;
  resultFile: string;
  terminationLog: string;
}

const STRING_FIELDS = [
  "model",
  "instructions",
  "branch",
  "parent",
  "head",
  "base",
  "workTree",
  "diffFile",
  "logFile",
  "filesFile",
  "keyFile",
  "resultFile",
  "terminationLog",
] as const;

const OPTIONAL_STRING_FIELDS = ["changesFile"] as const;

/** Parses and checks a task from its JSON. */
export function parseTask(json: string): Task {
  let value: unknown;
  try {
    value = JSON.parse(json);
  } catch (err) {
    throw new Error("AGENT_TASK isn't valid JSON", { cause: err });
  }
  if (typeof value !== "object" || value === null || Array.isArray(value)) {
    throw new Error("AGENT_TASK isn't a JSON object");
  }
  const raw = value as Record<string, unknown>;
  for (const field of STRING_FIELDS) {
    if (typeof raw[field] !== "string") {
      throw new Error(`AGENT_TASK.${field} must be a string`);
    }
  }
  for (const field of OPTIONAL_STRING_FIELDS) {
    if (raw[field] !== undefined && typeof raw[field] !== "string") {
      throw new Error(`AGENT_TASK.${field} must be a string`);
    }
  }
  const backend = raw.backend;
  if (typeof backend !== "string" || !(BACKENDS as readonly string[]).includes(backend)) {
    throw new Error(`AGENT_TASK.backend must be one of ${BACKENDS.join(", ")}`);
  }
  if (typeof raw.edit !== "boolean") {
    throw new Error("AGENT_TASK.edit must be a boolean");
  }
  if (raw.tools !== undefined) {
    checkTools(raw.tools, raw.edit);
  }
  const timeout = raw.timeoutSeconds;
  if (typeof timeout !== "number" || !Number.isInteger(timeout) || timeout <= 0) {
    throw new Error("AGENT_TASK.timeoutSeconds must be a positive integer");
  }
  const task = raw as unknown as Task;
  for (const field of ["model", "instructions", "branch", "head", "workTree", "resultFile"] as const) {
    if (!task[field]) {
      throw new Error(`AGENT_TASK.${field} can't be empty`);
    }
  }
  return task;
}
