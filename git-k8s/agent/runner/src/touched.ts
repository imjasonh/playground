/** The most paths that a change can touch for an agent to check it. */
export const MAX_PATHS = 1000;

/** The most bytes that the list of a change's paths can take. */
export const MAX_PATHS_BYTES = 128 << 10;

/** A path that the change touches, from git diff --name-status. */
export interface TouchedPath {
  /** A, C, D, M, R, or T. */
  status: string;
  path: string;
  /** The path that a rename or a copy started from. */
  from?: string;
}

/** The paths that a change touches, or the first of them. */
export interface TouchedPaths {
  paths: TouchedPath[];
  /** Whether the change touches more paths than paths holds. */
  more: boolean;
}

/**
 * Parses git diff --name-status -z output: each status is followed by its
 * path, or for a rename or a copy, by the old path and the new one. It
 * refuses output that takes more than MAX_PATHS_BYTES or that holds more
 * than MAX_PATHS paths.
 */
export function parseNameStatus(data: Buffer): TouchedPath[] {
  if (data.length > MAX_PATHS_BYTES) {
    throw new Error(`the change's paths take more than ${MAX_PATHS_BYTES >> 10} KiB, more than an agent can check`);
  }
  const { paths, more } = firstNameStatus(data);
  if (more) {
    throw new Error(`the change touches more than ${MAX_PATHS} paths, more than an agent can check`);
  }
  return paths;
}

/**
 * Parses the paths at the start of git diff --name-status -z output, as
 * many as its first MAX_PATHS_BYTES hold, and at most MAX_PATHS of them.
 */
export function firstNameStatus(data: Buffer): TouchedPaths {
  const cut = data.length > MAX_PATHS_BYTES;
  const fields = data.subarray(0, MAX_PATHS_BYTES).toString("utf8").split("\0");
  const paths: TouchedPath[] = [];
  for (let i = 0; i < fields.length - 1; ) {
    const status = fields[i].charAt(0);
    const two = status === "R" || status === "C";
    const end = i + (two ? 3 : 2);
    if (cut && end > fields.length - 1) {
      break;
    }
    const path = fields[end - 1];
    if (!/^[ACDMRT]$/.test(status) || !path || (two && !fields[i + 1])) {
      throw new Error("the change's list of paths isn't git diff --name-status -z output");
    }
    if (paths.length === MAX_PATHS) {
      return { paths, more: true };
    }
    paths.push(two ? { status, path, from: fields[i + 1] } : { status, path });
    i = end;
  }
  return { paths, more: cut };
}

/** A merge that git merge-tree wrote. */
export interface Conflicts {
  /** The merge's tree, whose files that conflict hold conflict markers. */
  tree: string;
  /** The paths that conflict. */
  paths: string[];
}

/**
 * Parses git merge-tree --write-tree --name-only -z output: the merge's
 * tree, and then each path that conflicts.
 */
export function parseConflicts(data: Buffer): Conflicts {
  if (data.length > MAX_PATHS_BYTES) {
    throw new Error(`the merge's conflicting paths take more than ${MAX_PATHS_BYTES >> 10} KiB, more than an agent can resolve`);
  }
  const fields = data.toString("utf8").split("\0");
  const [tree, ...paths] = fields.slice(0, -1);
  if (fields.at(-1) !== "" || !/^[0-9a-f]{40}([0-9a-f]{24})?$/.test(tree ?? "") || paths.includes("")) {
    throw new Error("the merge's list of conflicts isn't git merge-tree --name-only -z output");
  }
  if (paths.length > MAX_PATHS) {
    throw new Error(`more than ${MAX_PATHS} paths conflict, more than an agent can resolve`);
  }
  return { tree, paths };
}
