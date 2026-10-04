import { createHash } from "node:crypto";
import { lstat, readdir, readFile, readlink } from "node:fs/promises";
import { join } from "node:path";

export const MAX_FILES = 1000;
export const MAX_BYTES = 8 << 20;

const GITLINK = "160000";

/** A file that the agent changed, before encoding. */
export type Change =
  | { path: string; mode: "100644" | "100755" | "120000"; content: Buffer; deleted?: undefined }
  | { path: string; deleted: true; mode?: undefined; content?: undefined };

interface IndexEntry {
  mode: string;
  sha: string;
}

/** Parses git ls-files -s -z output: "MODE SHA STAGE\tPATH" records. */
export function parseIndex(data: Buffer): Map<string, IndexEntry> {
  const entries = new Map<string, IndexEntry>();
  for (const record of data.toString("utf8").split("\0")) {
    const tab = record.indexOf("\t");
    const [mode, sha] = record.slice(0, Math.max(tab, 0)).split(" ");
    if (tab > 0 && mode && sha) {
      entries.set(record.slice(tab + 1), { mode, sha });
    }
  }
  return entries;
}

/** Returns the SHA of a blob with this content, as git hash-object does. */
export function blobSha(algorithm: "sha1" | "sha256", content: Buffer): string {
  return createHash(algorithm).update(`blob ${content.length}\0`).update(content).digest("hex");
}

/**
 * Compares a work tree with the index that the Pod checked it out from, and
 * returns what changed, sorted by path. The work tree has no .git
 * directory, so this needs no git, and nothing that the agent writes can
 * configure one.
 */
export async function changedFiles(workTree: string, index: Buffer): Promise<Change[]> {
  const entries = parseIndex(index);
  const algorithm = [...entries.values()].some((e) => e.sha.length === 64) ? "sha256" : "sha1";
  const gitlinks = new Set([...entries].filter(([, e]) => e.mode === GITLINK).map(([path]) => path));
  const changes: Change[] = [];
  const seen = new Set<string>();
  let bytes = 0;

  const visit = async (dir: string): Promise<void> => {
    const dirents = await readdir(join(workTree, dir), { withFileTypes: true });
    for (const d of dirents) {
      const path = dir ? `${dir}/${d.name}` : d.name;
      const full = join(workTree, path);
      if (d.isDirectory()) {
        if (!gitlinks.has(path)) {
          await visit(path);
        }
        continue;
      }
      let mode: "100644" | "100755" | "120000";
      let content: Buffer;
      if (d.isSymbolicLink()) {
        mode = "120000";
        content = await readlink(full, { encoding: "buffer" });
      } else if (d.isFile()) {
        mode = ((await lstat(full)).mode & 0o111) !== 0 ? "100755" : "100644";
        content = await readFile(full);
      } else {
        throw new Error(`${path} isn't a file, a directory, or a symbolic link`);
      }
      seen.add(path);
      const old = entries.get(path);
      if (old && old.mode === mode && old.sha === blobSha(algorithm, content)) {
        continue;
      }
      bytes += content.length;
      changes.push({ path, mode, content });
      check(changes.length, bytes);
    }
  };
  await visit("");

  for (const [path, entry] of entries) {
    if (entry.mode !== GITLINK && !seen.has(path)) {
      changes.push({ path, deleted: true });
      check(changes.length, bytes);
    }
  }
  return changes.sort((a, b) => (a.path < b.path ? -1 : a.path > b.path ? 1 : 0));
}

function check(files: number, bytes: number): void {
  if (files > MAX_FILES) {
    throw new Error(`the agent changed more than ${MAX_FILES} files`);
  }
  if (bytes > MAX_BYTES) {
    throw new Error(`the files that the agent changed hold more than ${MAX_BYTES >> 20} MiB`);
  }
}
