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

/**
 * Parses git diff --name-status -z output: each status is followed by its
 * path, or for a rename or a copy, by the old path and the new one.
 */
export function parseNameStatus(data: Buffer): TouchedPath[] {
  if (data.length > MAX_PATHS_BYTES) {
    throw new Error(`the change's paths take more than ${MAX_PATHS_BYTES >> 10} KiB, more than an agent can check`);
  }
  const fields = data.toString("utf8").split("\0");
  const paths: TouchedPath[] = [];
  for (let i = 0; i < fields.length - 1; ) {
    const status = fields[i].charAt(0);
    const two = status === "R" || status === "C";
    const path = fields[i + (two ? 2 : 1)];
    if (!/^[ACDMRT]$/.test(status) || !path || (two && !fields[i + 1])) {
      throw new Error("the change's list of paths isn't git diff --name-status -z output");
    }
    paths.push(two ? { status, path, from: fields[i + 1] } : { status, path });
    if (paths.length > MAX_PATHS) {
      throw new Error(`the change touches more than ${MAX_PATHS} paths, more than an agent can check`);
    }
    i += two ? 3 : 2;
  }
  return paths;
}

/**
 * Parses git merge-tree --write-tree --name-only -z output: the merge's
 * tree, and then each path that conflicts.
 */
export function parseConflicts(data: Buffer): string[] {
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
  return paths;
}
