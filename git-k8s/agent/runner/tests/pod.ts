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
  const root = mkdtempSync(join(tmpdir(), "agent-runner-"));
  const repo = join(root, "git");
  mkdirSync(repo);
  git(repo, "init", "-q", "-b", "main");
  write(repo, base);
  git(repo, "add", "-A");
  git(repo, "commit", "-q", "--allow-empty", "-m", "Base");
  const baseSha = git(repo, "rev-parse", "HEAD").trim();
  write(repo, change);
  git(repo, "add", "-A");
  git(repo, "commit", "-q", "--allow-empty", "-m", "Change");
  const head = git(repo, "rev-parse", "HEAD").trim();

  for (const dir of ["src", "input", "key", "result"]) {
    mkdirSync(join(root, dir));
  }
  git(repo, "read-tree", head);
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

/**
 * Lays out what the agent container sees for a task that merges, the way
 * the Pod's prepare container does: the files of merging theirs into ours
 * from base, with conflict markers, the merge's index, the paths that
 * conflict, both sides' diffs and logs, and the key file.
 */
export function prepareMergePod(base: Files, ours: Files, theirs: Files, task: Partial<Task> = {}): Task {
  const root = mkdtempSync(join(tmpdir(), "agent-runner-"));
  const repo = join(root, "git");
  mkdirSync(repo);
  git(repo, "init", "-q", "-b", "main");
  const commit = (files: Files, message: string): string => {
    write(repo, files);
    git(repo, "add", "-A");
    git(repo, "commit", "-q", "--allow-empty", "-m", message);
    return git(repo, "rev-parse", "HEAD").trim();
  };
  const baseSha = commit(base, "Base");
  const merged = commit(theirs, "Theirs");
  git(repo, "checkout", "-q", "-b", "c/x", baseSha);
  const head = commit(ours, "Ours");
  const args = ["-c", "merge.conflictStyle=diff3", "merge-tree", "--write-tree", "--name-only", "-z", "--no-messages", `--merge-base=${baseSha}`, head, merged];
  const conflicts = spawnSync("git", args, { cwd: repo, env: gitEnv }).stdout;

  for (const dir of ["src", "input", "key", "result"]) {
    mkdirSync(join(root, dir));
  }
  git(repo, "read-tree", conflicts.toString().split("\0")[0]);
  git(repo, "rm", "-q", "--cached", "--ignore-unmatch", "--", ":(glob)**/.cursorignore");
  git(repo, "checkout-index", "-a", "-f", `--prefix=${join(root, "src")}/`);
  writeFileSync(join(root, "input", "files"), gitBuffer(repo, "ls-files", "-s", "-z"));
  writeFileSync(join(root, "input", "conflicts"), conflicts);
  writeFileSync(join(root, "input", "change.diff"), gitBuffer(repo, "diff", "--no-color", baseSha, head));
  writeFileSync(join(root, "input", "changes"), gitBuffer(repo, "diff", "--name-status", "-z", baseSha, head));
  writeFileSync(join(root, "input", "log.txt"), git(repo, "log", "--format=%h %s", `${baseSha}..${head}`));
  writeFileSync(join(root, "input", "merge.diff"), gitBuffer(repo, "diff", "--no-color", baseSha, merged));
  writeFileSync(join(root, "input", "merge-log.txt"), git(repo, "log", "--format=%h %s", `${baseSha}..${merged}`));
  writeFileSync(join(root, "key", "api-key"), "test-key-123\n");
  return {
    backend: "fake",
    model: "composer-2.5",
    instructions: "Resolve the conflicts.",
    edit: true,
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
    merge: {
      commit: merged,
      name: "main",
      conflictsFile: join(root, "input", "conflicts"),
      diffFile: join(root, "input", "merge.diff"),
      logFile: join(root, "input", "merge-log.txt"),
    },
    ...task,
  };
}
