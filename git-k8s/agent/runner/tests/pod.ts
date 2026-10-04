import { execFileSync, spawnSync } from "node:child_process";
import { mkdirSync, mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import type { Task } from "../src/task.js";

const gitEnv = {
  ...process.env,
  GIT_CONFIG_GLOBAL: "/dev/null",
  GIT_CONFIG_NOSYSTEM: "1",
  GIT_AUTHOR_NAME: "test",
  GIT_AUTHOR_EMAIL: "test@example.com",
  GIT_COMMITTER_NAME: "test",
  GIT_COMMITTER_EMAIL: "test@example.com",
};

export function git(dir: string, ...args: string[]): string {
  return execFileSync("git", args, { cwd: dir, env: gitEnv, encoding: "utf8" });
}

export function gitBuffer(dir: string, ...args: string[]): Buffer {
  return execFileSync("git", args, { cwd: dir, env: gitEnv });
}

/** Files to write, by path. null deletes a file. */
export type Files = Record<string, string | null>;

function write(root: string, files: Files): void {
  for (const [path, content] of Object.entries(files)) {
    const full = join(root, path);
    if (content === null) {
      execFileSync("rm", ["-f", full]);
      continue;
    }
    mkdirSync(join(full, ".."), { recursive: true });
    writeFileSync(full, content);
  }
}

/**
 * Lays out what the agent container sees, the way the Pod's prepare
 * container does: the head's files in a directory that isn't a repository,
 * the diff, the paths that it touches, the commit log, the head's index,
 * and the key file.
 */
export function preparePod(base: Files, change: Files, task: Partial<Task> = {}): Task {
  const { root, repo, baseSha } = newRepo(base);
  const head = commit(repo, change, "Change");
  return layOut(root, repo, baseSha, head, head, task);
}

/**
 * Lays out what the agent container sees for a task that merges theirs
 * into ours, the way the prepare container does: the merge's files, with
 * conflict markers, the paths that conflict, and the merged commits' log.
 */
export function prepareMerge(base: Files, ours: Files, theirs: Files, task: Partial<Task> = {}): Task {
  const { root, repo, baseSha } = newRepo(base);
  const head = commit(repo, ours, "Ours");
  git(repo, "checkout", "-q", "-b", "theirs", baseSha);
  const mergeHead = commit(repo, theirs, "Theirs");
  const args = ["-c", "merge.conflictStyle=diff3", "merge-tree", "--write-tree", "--no-messages", "--name-only", "-z"];
  const merged = spawnSync("git", [...args, `--merge-base=${baseSha}`, head, mergeHead], { cwd: repo, env: gitEnv });
  if (merged.status !== 0 && merged.status !== 1) {
    throw new Error(`git merge-tree failed: ${merged.stderr.toString()}`);
  }
  const conflictsFile = join(root, "input", "conflicts");
  const mergeLogFile = join(root, "input", "merge-log.txt");
  const tree = merged.stdout.subarray(0, merged.stdout.indexOf(0)).toString();
  const laidOut = layOut(root, repo, baseSha, head, tree, { mergeName: "theirs", mergeHead, conflictsFile, mergeLogFile, ...task });
  writeFileSync(conflictsFile, merged.stdout);
  writeFileSync(mergeLogFile, git(repo, "log", "--format=%h %s", `${baseSha}..${mergeHead}`));
  return laidOut;
}

function newRepo(base: Files): { root: string; repo: string; baseSha: string } {
  const root = mkdtempSync(join(tmpdir(), "agent-runner-"));
  const repo = join(root, "git");
  mkdirSync(repo);
  git(repo, "init", "-q", "-b", "main");
  return { root, repo, baseSha: commit(repo, base, "Base") };
}

function commit(repo: string, files: Files, message: string): string {
  write(repo, files);
  git(repo, "add", "-A");
  git(repo, "commit", "-q", "--allow-empty", "-m", message);
  return git(repo, "rev-parse", "HEAD").trim();
}

/** Checks out tree, and writes the change from baseSha to head, as preparePod describes. */
function layOut(root: string, repo: string, baseSha: string, head: string, tree: string, task: Partial<Task>): Task {
  for (const dir of ["src", "input", "key", "result"]) {
    mkdirSync(join(root, dir));
  }
  git(repo, "read-tree", tree);
  git(repo, "rm", "-q", "--cached", "--ignore-unmatch", "--", ":(glob)**/.cursorignore");
  git(repo, "checkout-index", "-a", "-f", `--prefix=${join(root, "src")}/`);
  writeFileSync(join(root, "input", "files"), gitBuffer(repo, "ls-files", "-s", "-z"));
  writeFileSync(join(root, "input", "change.diff"), gitBuffer(repo, "diff", "--no-color", baseSha, head));
  writeFileSync(join(root, "input", "changes"), gitBuffer(repo, "diff", "--name-status", "-z", baseSha, head));
  writeFileSync(join(root, "input", "log.txt"), git(repo, "log", "--format=%h %s", `${baseSha}..${head}`));
  writeFileSync(join(root, "key", "api-key"), "test-key-123\n");
  return {
    backend: "fake",
    model: "composer-2.5",
    instructions: "Review the change.",
    edit: false,
    timeoutSeconds: 60,
    branch: "c/x",
    parent: "main",
    head,
    base: baseSha,
    workTree: join(root, "src"),
    diffFile: join(root, "input", "change.diff"),
    logFile: join(root, "input", "log.txt"),
    filesFile: join(root, "input", "files"),
    changesFile: join(root, "input", "changes"),
    keyFile: join(root, "key", "api-key"),
    resultFile: join(root, "result", "result.json"),
    terminationLog: join(root, "termination-log"),
    ...task,
  };
}
