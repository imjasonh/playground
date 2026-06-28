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
 * @property {string[]} parent   parent commit oids (empty for the root commit)
 *
 * @typedef {Object} FileChange
 * @property {string} path
 * @property {'added'|'removed'|'modified'} status
 * @property {?string} [oldOid]
 * @property {?string} [newOid]
 *
 * @typedef {Object} BranchInfo
 * @property {string} name
 * @property {boolean} current
 *
 * @typedef {Object} Ref
 * @property {'branch'|'tag'|'commit'} type
 * @property {string} name  branch/tag name, or the commit oid for type 'commit'
 *
 * @typedef {Object} UpdateResult
 * @property {boolean} updated  whether a fetch ran (false for static sources)
 * @property {boolean} changed  whether the current branch tip actually moved
 *
 * @typedef {Object} Capabilities
 * @property {boolean} read   can list/read files (true for every source today)
 * @property {boolean} fetch  can fetch new commits from a remote (Pull/Update)
 * @property {boolean} write  can stage/commit locally (no source does yet)
 * @property {boolean} push   can push to a remote (no source does yet)
 *
 * @typedef {Object} RepoSource
 * @property {string} fullName
 * @property {string|null} url
 * @property {Capabilities} capabilities  what the UI may offer for this source
 * @property {boolean} readOnly  derived: no write and no push capability
 * @property {() => string} getCurrentBranch  name of the current ref (back-compat)
 * @property {() => Ref} getCurrentRef  the generalized current ref descriptor
 * @property {() => Promise<BranchInfo[]>} listBranches
 * @property {() => Promise<string[]>} [listTags]  tag names, newest-ish first
 * @property {(name: string) => Promise<void>} setBranch
 * @property {(ref: Ref|string) => Promise<void>} setRef  switch to any ref
 * @property {(ref?: Ref|string) => Promise<string[]>} listFiles
 * @property {(path: string, ref?: Ref|string) => Promise<Uint8Array>} readFile
 * @property {(ref?: Ref|string) => Promise<Commit|null>} headCommit
 * @property {(limit?: number, ref?: Ref|string) => Promise<Commit[]>} log
 * @property {(path: string, limit?: number, ref?: Ref|string) => Promise<Commit[]>} [fileLog]
 * @property {(baseRef: ?(Ref|string), headRef: Ref|string) => Promise<FileChange[]>} [changedFiles]
 * @property {(onProgress?: Function) => Promise<UpdateResult>} update
 */

const textEncoder = new TextEncoder();

/** The safe read-only baseline for any capability flags a source omits. */
const BASELINE_CAPABILITIES = { read: true, fetch: false, write: false, push: false };

/**
 * Normalize a source's capability flags, filling anything unspecified with the
 * read-only baseline. The UI keys affordances off these (e.g. whether to enable
 * Pull/Update) instead of sniffing which concrete source it holds.
 *
 * @param {{capabilities?: Partial<Capabilities>}} source
 * @returns {Capabilities}
 */
export function capabilitiesOf(source) {
  const caps = (source && source.capabilities) || {};
  return {
    read: caps.read !== false, // readable unless a source explicitly opts out
    fetch: Boolean(caps.fetch),
    write: Boolean(caps.write),
    push: Boolean(caps.push),
  };
}

/** A source is read-only when it can neither write locally nor push. */
export function isReadOnly(capabilities) {
  return !capabilities.write && !capabilities.push;
}

const REF_TYPES = new Set(['branch', 'tag', 'commit']);

/**
 * Coerce a ref argument into a `{type, name}` descriptor. A bare string is
 * treated as a branch (the historical, branch-centric behavior); an object is
 * validated and defaulted to a branch when the type is missing/unknown.
 *
 * @param {Ref|string} ref
 * @returns {Ref}
 */
export function normalizeRef(ref) {
  if (typeof ref === 'string') return { type: 'branch', name: ref };
  if (ref && typeof ref.name === 'string') {
    const type = REF_TYPES.has(ref.type) ? ref.type : 'branch';
    return { type, name: ref.name };
  }
  throw new Error('Invalid ref');
}

/** Short, human-readable label for a ref (commits are abbreviated). */
export function refLabel(ref) {
  const r = normalizeRef(ref);
  return r.type === 'commit' ? r.name.slice(0, 7) : r.name;
}

/** Encode a ref as a "type:name" string for option values / URLs. */
export function refValue(ref) {
  const r = normalizeRef(ref);
  return `${r.type}:${r.name}`;
}

/** Parse a "type:name" string back into a ref descriptor. */
export function parseRefValue(value) {
  const str = String(value || '');
  const idx = str.indexOf(':');
  if (idx === -1) return { type: 'branch', name: str };
  return normalizeRef({ type: str.slice(0, idx), name: str.slice(idx + 1) });
}

function toBytes(content) {
  if (content == null) return new Uint8Array(0);
  if (content instanceof Uint8Array) return content;
  if (ArrayBuffer.isView(content)) return new Uint8Array(content.buffer);
  return textEncoder.encode(String(content));
}

function bytesEqual(a, b) {
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i += 1) {
    if (a[i] !== b[i]) return false;
  }
  return true;
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
 *   },
 *   tags: { '<tag>': '<branchName>' }   // optional: a tag aliases a branch snapshot
 * }
 */
export class InMemoryRepoSource {
  constructor(spec) {
    this.fullName = spec.fullName || 'demo/repo';
    this.url = spec.url || null;
    // In-memory data is static: readable, but there is no remote to fetch from
    // and nothing to write/push.
    this.capabilities = { ...BASELINE_CAPABILITIES };
    this.readOnly = isReadOnly(this.capabilities);
    this._branches = spec.branches || {};
    this._tags = spec.tags || {};
    const names = Object.keys(this._branches);
    this._defaultBranch = spec.defaultBranch || names[0] || 'main';
    this._ref = { type: 'branch', name: this._defaultBranch };
  }

  getCurrentBranch() {
    return this._ref.name;
  }

  getCurrentRef() {
    return { ...this._ref };
  }

  async listBranches() {
    return Object.keys(this._branches).map((name) => ({
      name,
      current: this._ref.type === 'branch' && name === this._ref.name,
    }));
  }

  async listTags() {
    return Object.keys(this._tags);
  }

  async setBranch(name) {
    if (!this._branches[name]) {
      throw new Error(`Unknown branch: ${name}`);
    }
    this._ref = { type: 'branch', name };
  }

  async setRef(ref) {
    const next = normalizeRef(ref);
    this._snapshot(next); // throws if it doesn't resolve
    this._ref = next;
  }

  /** Which branch a commit oid belongs to (first match), or null. */
  _commitBranch(oid) {
    for (const [name, branch] of Object.entries(this._branches)) {
      const hit = (branch.commits || []).some(
        (c) => c.oid === oid || (oid.length >= 4 && c.oid.startsWith(oid))
      );
      if (hit) return name;
    }
    return null;
  }

  /** Resolve a ref (descriptor, string, or current) to a branch snapshot. */
  _snapshot(ref) {
    if (ref == null) return this._snapshot(this._ref);
    const r = normalizeRef(ref);
    if (r.type === 'tag') {
      const target = this._tags[r.name];
      const branch = target && this._branches[target];
      if (!branch) throw new Error(`Unknown tag: ${r.name}`);
      return branch;
    }
    if (r.type === 'commit') {
      const name = this._commitBranch(r.name);
      if (!name) throw new Error(`Unknown commit: ${r.name}`);
      return this._branches[name];
    }
    // branch — but tolerate a bare string that is actually a tag/commit so the
    // optional `ref` argument stays forgiving for callers.
    if (this._branches[r.name]) return this._branches[r.name];
    if (this._tags[r.name]) return this._snapshot({ type: 'tag', name: r.name });
    const commitBranch = this._commitBranch(r.name);
    if (commitBranch) return this._branches[commitBranch];
    throw new Error(`Unknown branch: ${r.name}`);
  }

  async listFiles(ref) {
    return Object.keys(this._snapshot(ref).files);
  }

  async readFile(path, ref) {
    const files = this._snapshot(ref).files;
    if (!(path in files)) {
      throw new Error(`File not found: ${path}`);
    }
    return toBytes(files[path]);
  }

  /** Map spec commits to the Commit shape, deriving linear parents. */
  _normalizeCommits(subset, all) {
    const parentOf = new Map();
    for (let i = 0; i < all.length; i += 1) {
      parentOf.set(all[i].oid, i + 1 < all.length ? [all[i + 1].oid] : []);
    }
    return subset.map((c) => ({
      oid: c.oid,
      message: c.message || '',
      author: { name: (c.author && c.author.name) || '', email: (c.author && c.author.email) || '' },
      timestamp: typeof c.timestamp === 'number' ? c.timestamp : 0,
      parent: parentOf.get(c.oid) || [],
    }));
  }

  async headCommit(ref) {
    const commits = this._snapshot(ref).commits || [];
    if (!commits.length) return null;
    return this._normalizeCommits([commits[0]], commits)[0];
  }

  async log(limit = 50, ref) {
    const commits = this._snapshot(ref).commits || [];
    return this._normalizeCommits(commits.slice(0, limit), commits);
  }

  /**
   * Commits that touched a given file. When the spec annotates commits with a
   * `changed` path list this filters precisely; otherwise (no change data at
   * all) it falls back to the full history so callers still get something.
   */
  async fileLog(path, limit = 50, ref) {
    const commits = this._snapshot(ref).commits || [];
    const annotated = commits.some((c) => Array.isArray(c.changed));
    const filtered = annotated
      ? commits.filter((c) => Array.isArray(c.changed) && c.changed.includes(path))
      : commits;
    return this._normalizeCommits(filtered.slice(0, limit), commits);
  }

  /**
   * Files that differ between two refs (a null base means "compare against an
   * empty tree", i.e. every file is an addition).
   */
  async changedFiles(baseRef, headRef) {
    const base = baseRef == null ? {} : this._snapshot(baseRef).files;
    const head = this._snapshot(headRef).files;
    const paths = new Set([...Object.keys(base), ...Object.keys(head)]);
    const changes = [];
    for (const path of paths) {
      const inBase = path in base;
      const inHead = path in head;
      if (inBase && !inHead) changes.push({ path, status: 'removed' });
      else if (!inBase && inHead) changes.push({ path, status: 'added' });
      else if (!bytesEqual(toBytes(base[path]), toBytes(head[path]))) {
        changes.push({ path, status: 'modified' });
      }
    }
    changes.sort((x, y) => (x.path < y.path ? -1 : x.path > y.path ? 1 : 0));
    return changes;
  }

  // Demo data is static; "update" is a no-op that reports no changes.
  async update() {
    return { updated: false, changed: false };
  }
}
