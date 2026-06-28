/**
 * RepoSource is the read-only contract the UI talks to. It is implemented by:
 *   - InMemoryRepoSource (below) for demo mode and unit/e2e tests, and
 *   - GitRepoSource (gitClient.js) backed by isomorphic-git + lightning-fs.
 *
 * Keeping the UI behind this interface means the entire code browser
 * (file tree, viewer, fuzzy finder, branch switching, history) can be tested
 * without any network access.
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
 * @typedef {Object} RepoSource
 * @property {string} fullName
 * @property {string|null} url
 * @property {() => string} getCurrentBranch
 * @property {() => Promise<BranchInfo[]>} listBranches
 * @property {(name: string) => Promise<void>} setBranch
 * @property {() => Promise<string[]>} listFiles
 * @property {(path: string) => Promise<Uint8Array>} readFile
 * @property {() => Promise<Commit|null>} headCommit
 * @property {(limit?: number) => Promise<Commit[]>} log
 * @property {(onProgress?: Function) => Promise<{updated: boolean}>} update
 */

const textEncoder = new TextEncoder();

function toBytes(content) {
  if (content == null) return new Uint8Array(0);
  if (content instanceof Uint8Array) return content;
  if (ArrayBuffer.isView(content)) return new Uint8Array(content.buffer);
  return textEncoder.encode(String(content));
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
    this.readOnly = true;
    this._branches = spec.branches || {};
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
    return { updated: false };
  }
}
