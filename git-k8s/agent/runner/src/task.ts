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
  /**
   * The merge base of the branch and its parent, or of head and mergeHead,
   * or "" if they have none.
   */
  base: string;
  /** How the prompt names the ref whose commit mergeHead merges into head, such as main. */
  mergeName?: string;
  /** A commit to merge into head. Then workTree holds the merge's files, with conflict markers. */
  mergeHead?: string;
  /** The head commit's files, or the merge's. It isn't a git repository. */
  workTree: string;
  /** The change from base to head, from git diff. */
  diffFile: string;
  /** The branch's commits since base, one per line. */
  logFile: string;
  /** The index of workTree's files, from git ls-files -s -z. */
  filesFile: string;
  /** The paths that the change touches, from git diff --name-status -z. */
  changesFile?: string;
  /** The merge's tree and the paths that conflict, from git merge-tree --name-only -z. */
  conflictsFile?: string;
  /** The merged branch's commits since base, one per line. */
  mergeLogFile?: string;
  /** The change from base to mergeHead, from git diff. */
  mergeDiffFile?: string;
  /** The paths that the change from base to mergeHead touches, from git diff --name-status -z. */
  mergeChangesFile?: string;
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

const OPTIONAL_STRING_FIELDS = ["changesFile", "mergeName", "mergeHead", "conflictsFile", "mergeLogFile", "mergeDiffFile", "mergeChangesFile"] as const;

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
  if (task.mergeHead !== undefined) {
    for (const field of ["mergeName", "mergeHead", "base", "conflictsFile", "mergeLogFile", "mergeDiffFile", "mergeChangesFile"] as const) {
      if (!task[field]) {
        throw new Error(`AGENT_TASK.${field} can't be empty in a merge`);
      }
    }
  }
  return task;
}
