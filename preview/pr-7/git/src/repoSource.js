/**
 * RepoSource is the contract the UI talks to. It is implemented by:
 *   - InMemoryRepoSource (below) for demo mode and unit/e2e tests, and
 *   - GitRepoSource (gitClient.js) backed by isomorphic-git + lightning-fs.
 *
 * Keeping the UI behind this interface means the entire code browser
 * (file tree, viewer, fuzzy finder, branch switching, history) — and the
 * read-write editing flow (edit, create, delete, stage, commit) — can be
 * exercised without any network access.
 *
 * @typedef {Object} Commit
 * @property {string} oid
 * @property {string} message
 * @property {{name: string, email: string}} author
 * @property {number} timestamp  seconds since epoch
 *
 * @typedef {Object} BranchInfo
 * @property {string} name
 * @property {boolean} current
 *
 * @typedef {Object} UpdateResult
 * @property {boolean} updated  whether a fetch ran (false for static sources)
 * @property {boolean} changed  whether the current branch tip actually moved
 *
 * @typedef {Object} ChangeEntry
 * @property {string} path
 * @property {'new'|'modified'|'deleted'} status
 *
 * @typedef {Object} CommitResult
 * @property {string} oid  the new commit id
 *
 * @typedef {Object} RepoSource
 * @property {string} fullName
 * @property {string|null} url
 * @property {boolean} readOnly  when true the UI hides every editing affordance
 * @property {boolean} canPush   whether changes can be pushed to a remote
 * @property {() => string} getCurrentBranch
 * @property {() => Promise<BranchInfo[]>} listBranches
 * @property {(name: string) => Promise<void>} setBranch
 * @property {(ref?: string) => Promise<string[]>} listFiles
 * @property {(path: string, ref?: string) => Promise<Uint8Array>} readFile
 * @property {(ref?: string) => Promise<Commit|null>} headCommit
 * @property {(limit?: number, ref?: string) => Promise<Commit[]>} log
 * @property {(onProgress?: Function) => Promise<UpdateResult>} update
 *
 * Write surface (present only when readOnly === false):
 * @property {(path: string, content: string|Uint8Array) => Promise<void>} writeFile
 * @property {(path: string) => Promise<void>} deleteFile
 * @property {() => Promise<ChangeEntry[]>} status
 * @property {(opts: {message: string, author: {name: string, email: string}}) => Promise<CommitResult>} commit
 * @property {(opts?: object) => Promise<{ok: boolean}>} push
 */

const textEncoder = new TextEncoder();

export function toBytes(content) {
  if (content == null) return new Uint8Array(0);
  if (content instanceof Uint8Array) return content;
  if (ArrayBuffer.isView(content)) return new Uint8Array(content.buffer);
  return textEncoder.encode(String(content));
}

/** Byte-for-byte comparison of two file contents (strings or buffers). */
export function bytesEqual(a, b) {
  const x = toBytes(a);
  const y = toBytes(b);
  if (x.length !== y.length) return false;
  for (let i = 0; i < x.length; i += 1) {
    if (x[i] !== y[i]) return false;
  }
  return true;
}

const HEX = '0123456789abcdef';

/** A 40-char hex string that stands in for a git oid in the in-memory source. */
export function fakeOid() {
  const bytes = new Uint8Array(20);
  const cryptoObj = typeof globalThis !== 'undefined' ? globalThis.crypto : undefined;
  if (cryptoObj && typeof cryptoObj.getRandomValues === 'function') {
    cryptoObj.getRandomValues(bytes);
  } else {
    for (let i = 0; i < bytes.length; i += 1) bytes[i] = Math.floor(Math.random() * 256);
  }
  let out = '';
  for (const byte of bytes) out += HEX[byte >> 4] + HEX[byte & 0x0f];
  return out;
}

/** Diff a working tree against its committed baseline (both path -> content maps). */
export function diffTrees(working, baseline) {
  const changes = [];
  for (const path of Object.keys(working)) {
    if (!(path in baseline)) {
      changes.push({ path, status: 'new' });
    } else if (!bytesEqual(working[path], baseline[path])) {
      changes.push({ path, status: 'modified' });
    }
  }
  for (const path of Object.keys(baseline)) {
    if (!(path in working)) changes.push({ path, status: 'deleted' });
  }
  changes.sort((a, b) => a.path.localeCompare(b.path));
  return changes;
}

/** Strip a leading "./" or "/" so callers can't escape the repo root. */
function cleanRepoPath(path) {
  return String(path == null ? '' : path)
    .replace(/\\/g, '/')
    .replace(/^\.\//, '')
    .replace(/\/+/g, '/')
    .replace(/^\/+/, '')
    .replace(/\/+$/, '');
}

/**
 * In-memory RepoSource built from a plain spec:
 * {
 *   fullName, url, defaultBranch,
 *   branches: {
 *     <name>: {
 *       files: { '<path>': string | Uint8Array },
 *       commits: Commit[]   // newest first
 *     }
 *   }
 * }
 */
export class InMemoryRepoSource {
  constructor(spec) {
    this.fullName = spec.fullName || 'demo/repo';
    this.url = spec.url || null;
    // The in-memory source is fully editable, but it has no remote, so it can
    // be committed to locally yet never pushed. `readOnly === false` is what
    // lights up the editing UI; `canPush === false` keeps the Push action off.
    this.readOnly = spec.readOnly === true;
    this.canPush = false;
    this._branches = spec.branches || {};
    // Snapshot each branch's initial tree as its committed baseline so we can
    // compute working-tree status (new / modified / deleted) after edits.
    for (const branch of Object.values(this._branches)) {
      branch.files = branch.files || {};
      branch.commits = branch.commits || [];
      branch._committed = { ...branch.files };
    }
    const names = Object.keys(this._branches);
    this._defaultBranch = spec.defaultBranch || names[0] || 'main';
    this._current = this._defaultBranch;
  }

  getCurrentBranch() {
    return this._current;
  }

  async listBranches() {
    return Object.keys(this._branches).map((name) => ({
      name,
      current: name === this._current,
    }));
  }

  async setBranch(name) {
    if (!this._branches[name]) {
      throw new Error(`Unknown branch: ${name}`);
    }
    this._current = name;
  }

  _branch(ref) {
    const branch = this._branches[ref || this._current];
    if (!branch) throw new Error(`Unknown branch: ${ref || this._current}`);
    return branch;
  }

  async listFiles(ref) {
    return Object.keys(this._branch(ref).files);
  }

  async readFile(path, ref) {
    const files = this._branch(ref).files;
    if (!(path in files)) {
      throw new Error(`File not found: ${path}`);
    }
    return toBytes(files[path]);
  }

  async headCommit(ref) {
    const commits = this._branch(ref).commits || [];
    return commits[0] || null;
  }

  async log(limit = 50, ref) {
    const commits = this._branch(ref).commits || [];
    return commits.slice(0, limit);
  }

  // Demo data is static; "update" is a no-op that reports no changes.
  async update() {
    return { updated: false, changed: false };
  }

  /* -------- write surface (current branch only) -------- */

  async writeFile(path, content) {
    const clean = cleanRepoPath(path);
    if (!clean) throw new Error('A file path is required.');
    this._branch().files[clean] = content;
  }

  async deleteFile(path) {
    const clean = cleanRepoPath(path);
    const files = this._branch().files;
    if (!(clean in files)) throw new Error(`File not found: ${clean}`);
    delete files[clean];
  }

  /** Working-tree changes vs the last commit on the current branch. */
  async status() {
    const branch = this._branch();
    return diffTrees(branch.files, branch._committed);
  }

  async commit({ message, author } = {}) {
    const branch = this._branch();
    const changes = diffTrees(branch.files, branch._committed);
    if (changes.length === 0) throw new Error('Nothing to commit.');
    const summary = (message || '').trim();
    if (!summary) throw new Error('A commit message is required.');

    const oid = fakeOid();
    branch.commits = [
      {
        oid,
        message: summary,
        author: {
          name: (author && author.name) || 'You',
          email: (author && author.email) || 'you@example.com',
        },
        timestamp: Math.floor(Date.now() / 1000),
      },
      ...(branch.commits || []),
    ];
    // Advance the committed baseline so status is clean after the commit.
    branch._committed = { ...branch.files };
    return { oid };
  }

  async push() {
    throw new Error('This repository is local-only and cannot be pushed.');
  }
}
