import { createHash } from "node:crypto";
import { createReadStream } from "node:fs";
import { lstat, readdir, readFile, readlink } from "node:fs/promises";
import { join } from "node:path";

export const MAX_FILES = 1000;
export const MAX_BYTES = 8 << 20;

const GITLINK = "160000";

/**
 * Cursor reads these files to hide other files from the agent. The Pod
 * leaves them out of the work tree, so a fix leaves them as they are.
 */
const IGNORE_FILE = ".cursorignore";

function isIgnoreFile(path: string): boolean {
  return path === IGNORE_FILE || path.endsWith(`/${IGNORE_FILE}`);
}

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
 * configure one. It reads only the changed files into memory, and throws
 * before it reads more than MAX_FILES files or MAX_BYTES bytes.
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
      if (isIgnoreFile(path)) {
        continue;
      }
      seen.add(path);
      const old = entries.get(path);
      if (d.isSymbolicLink()) {
        const target = await readlink(full, { encoding: "buffer" });
        if (old?.mode === "120000" && old.sha === blobSha(algorithm, target)) {
          continue;
        }
        check(changes.length + 1, bytes + target.length);
        bytes += target.length;
        changes.push({ path, mode: "120000", content: target });
      } else if (d.isFile()) {
        const stat = await lstat(full);
        const mode = (stat.mode & 0o111) !== 0 ? "100755" : "100644";
        if (old?.mode === mode && old.sha === (await fileSha(algorithm, full, path, stat.size))) {
          continue;
        }
        check(changes.length + 1, bytes + stat.size);
        const content = await readFile(full);
        if (content.length !== stat.size) {
          throw new Error(`${path} changed while the runner read it`);
        }
        bytes += content.length;
        changes.push({ path, mode, content });
      } else {
        throw new Error(`${path} isn't a file, a directory, or a symbolic link`);
      }
    }
  };
  await visit("");

  for (const [path, entry] of entries) {
    if (entry.mode !== GITLINK && !seen.has(path) && !isIgnoreFile(path)) {
      changes.push({ path, deleted: true });
      check(changes.length, bytes);
    }
  }
  return changes.sort((a, b) => (a.path < b.path ? -1 : a.path > b.path ? 1 : 0));
}

/**
 * Returns the SHA of the blob for a file of the given size, reading the
 * file a piece at a time, so a large file that the agent left alone takes
 * no memory.
 */
async function fileSha(algorithm: "sha1" | "sha256", full: string, path: string, size: number): Promise<string> {
  const hash = createHash(algorithm).update(`blob ${size}\0`);
  let read = 0;
  for await (const chunk of createReadStream(full) as AsyncIterable<Buffer>) {
    read += chunk.length;
    hash.update(chunk);
  }
  if (read !== size) {
    throw new Error(`${path} changed while the runner read it`);
  }
  return hash.digest("hex");
}

/**
 * Throws unless every path in the index is valid UTF-8. The runner finds
 * the files that the agent changed by their paths, which it reads as
 * UTF-8.
 */
export function checkPaths(index: Buffer): void {
  const strict = new TextDecoder("utf-8", { fatal: true });
  for (let start = 0; start < index.length; ) {
    const nul = index.indexOf(0, start);
    const end = nul < 0 ? index.length : nul;
    const record = index.subarray(start, end);
    try {
      strict.decode(record);
    } catch {
      const path = record.subarray(record.indexOf(0x09) + 1).toString();
      throw new Error(`the agent can't edit files because the path ${JSON.stringify(path)} isn't valid UTF-8`);
    }
    start = end + 1;
  }
}

function check(files: number, bytes: number): void {
  if (files > MAX_FILES) {
    throw new Error(`the agent changed more than ${MAX_FILES} files`);
  }
  if (bytes > MAX_BYTES) {
    throw new Error(`the files that the agent changed hold more than ${MAX_BYTES >> 20} MiB`);
  }
}
