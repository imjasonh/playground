/**
 * Browser-only adapter around isomorphic-git + lightning-fs.
 *
 * The heavy UMD bundles are vendored under ./vendor and lazy-loaded the first
 * time a real clone/open is requested, so the initial page load and demo mode
 * stay light and network-free. Each bundle registers a global:
 *   window.git        (isomorphic-git)
 *   window.GitHttp    (isomorphic-git/http/web)
 *   window.LightningFS
 */

const VENDOR = {
  polyfills: 'vendor/polyfills/node-globals.js',
  lightningFs: 'vendor/lightning-fs/lightning-fs.min.js',
  git: 'vendor/isomorphic-git/index.umd.min.js',
  http: 'vendor/isomorphic-git/http-web.umd.js',
};

import { normalizeRef } from './repoSource.js';
import { makeOnAuth } from './auth.js';
import { classifyGitMode, symlinkTarget, parseGitmodules } from './specialEntry.js';
import { blameLines } from './blame.js';

const FS_NAME = 'git-browser-fs';
const REGISTRY_KEY = 'git-browser:repos';
const REGISTRY_VERSION = 1;
// How far back blame walks a file's history. Each step reads the file's blob at
// one commit, so this caps the work (and the diff backstop in blame.js guards
// each pair). Deep enough for real files; bounded so a long history can't hang.
const BLAME_MAX_COMMITS = 200;

let globalsPromise = null;

function loadScript(src) {
  return new Promise((resolve, reject) => {
    const existing = document.querySelector(`script[data-vendor="${src}"]`);
    if (existing) {
      if (existing.dataset.loaded === 'true') resolve();
      else {
        existing.addEventListener('load', () => resolve());
        existing.addEventListener('error', () => reject(new Error(`Failed to load ${src}`)));
      }
      return;
    }
    const el = document.createElement('script');
    el.src = src;
    el.async = false;
    el.dataset.vendor = src;
    el.addEventListener('load', () => {
      el.dataset.loaded = 'true';
      resolve();
    });
    el.addEventListener('error', () => reject(new Error(`Failed to load ${src}`)));
    document.head.appendChild(el);
  });
}

/** Load the vendored git libraries and return their globals. */
export async function loadGitGlobals() {
  if (globalsPromise) return globalsPromise;
  globalsPromise = (async () => {
    // Buffer/process shim must be present before the isomorphic-git UMD runs.
    await loadScript(VENDOR.polyfills);
    await loadScript(VENDOR.lightningFs);
    await loadScript(VENDOR.git);
    await loadScript(VENDOR.http);

    const git = globalThis.git;
    const GitHttp = globalThis.GitHttp;
    const FS = globalThis.LightningFS;
    const http = GitHttp && (GitHttp.default || GitHttp);

    if (!git || !http || !FS) {
      throw new Error('Could not initialize the git engine (vendored bundles failed to load).');
    }
    return { git, http, FS };
  })();
  return globalsPromise;
}

async function mkdirp(fs, dir) {
  const parts = dir.split('/').filter(Boolean);
  let current = '';
  for (const part of parts) {
    current += `/${part}`;
    try {
      await fs.promises.mkdir(current);
    } catch (err) {
      if (!err || err.code !== 'EEXIST') throw err;
    }
  }
}

async function rmrf(fs, path) {
  let stat;
  try {
    stat = await fs.promises.lstat(path);
  } catch {
    return; // already gone
  }
  if (stat.isDirectory()) {
    const entries = await fs.promises.readdir(path);
    for (const entry of entries) {
      await rmrf(fs, `${path}/${entry}`);
    }
    await fs.promises.rmdir(path);
  } else {
    await fs.promises.unlink(path);
  }
}

/**
 * Coerce whatever is in storage into a clean array of repo entries.
 *
 * Accepts both the current `{ version, repos }` envelope and the legacy
 * bare-array format (so existing users don't lose their cloned repos), and
 * drops anything that doesn't at least have a usable `dir`. Pure + exported so
 * the migration is unit-testable without touching localStorage.
 */
export function normalizeRegistry(parsed) {
  let repos;
  if (Array.isArray(parsed)) {
    repos = parsed; // legacy: registry was a bare array
  } else if (parsed && Array.isArray(parsed.repos)) {
    repos = parsed.repos;
  } else {
    return [];
  }
  return repos.filter(
    (entry) => entry && typeof entry.dir === 'string' && entry.dir.length > 0
  );
}

function readRegistry() {
  try {
    const raw = localStorage.getItem(REGISTRY_KEY);
    if (!raw) return [];
    return normalizeRegistry(JSON.parse(raw));
  } catch {
    return [];
  }
}

function writeRegistry(list) {
  try {
    localStorage.setItem(
      REGISTRY_KEY,
      JSON.stringify({ version: REGISTRY_VERSION, repos: list })
    );
  } catch {
    /* storage may be unavailable; non-fatal */
  }
}

function toCommit(entry) {
  const c = entry.commit || {};
  const author = c.author || {};
  return {
    oid: entry.oid,
    message: c.message || '',
    author: { name: author.name || '', email: author.email || '' },
    timestamp: typeof author.timestamp === 'number' ? author.timestamp : 0,
    parent: Array.isArray(c.parent) ? c.parent : [],
  };
}

/**
 * RepoSource backed by a cloned repository living in lightning-fs.
 * Read-only: branch switching just changes which tree we read from.
 */
export class GitRepoSource {
  constructor({ fs, git, http, dir, url, fullName, corsProxy, singleBranch, depth }) {
    this._fs = fs;
    this._git = git;
    this._http = http;
    this._dir = dir;
    this.url = url || null;
    this.fullName = fullName || dir.replace(/^\//, '');
    this._corsProxy = corsProxy || undefined;
    // Remember how the repo was cloned so update() fetches the same scope
    // instead of accidentally widening it (all branches / full history).
    this._singleBranch = Boolean(singleBranch);
    this._depth = Number.isFinite(depth) && depth > 0 ? depth : 0;
    // A real clone is readable and can fetch from its remote; writing/pushing
    // is not implemented yet, so it stays read-only.
    this.capabilities = { read: true, fetch: true, write: false, push: false };
    this.readOnly = !this.capabilities.write && !this.capabilities.push;
    // The current ref is generalized: a branch, a tag, or a detached commit.
    this._current = 'HEAD';
    this._refType = 'branch';
    this._oidCache = new Map();
    // Per-tree caches keyed by the (immutable) commit oid: the entry kinds for
    // listFiles/entryMeta, and the parsed `.gitmodules`. Safe to keep across
    // ref switches and fetches, since a new tip resolves to a different oid.
    this._entryCache = new Map();
    this._gitmodulesCache = new Map();
    // Supplies a session-stored token (if any) for this repo's host on fetch.
    this._onAuth = makeOnAuth();
  }

  async init() {
    try {
      const branch = await this._git.currentBranch({
        fs: this._fs,
        dir: this._dir,
        fullname: false,
      });
      if (branch) {
        this._current = branch;
        this._refType = 'branch';
      }
    } catch {
      /* keep HEAD */
    }
    return this;
  }

  getCurrentBranch() {
    return this._current;
  }

  getCurrentRef() {
    return { type: this._refType, name: this._current };
  }

  async listBranches() {
    const [local, remote] = await Promise.all([
      this._git.listBranches({ fs: this._fs, dir: this._dir }),
      this._git
        .listBranches({ fs: this._fs, dir: this._dir, remote: 'origin' })
        .catch(() => []),
    ]);
    const names = new Set();
    for (const name of local) names.add(name);
    for (const name of remote) if (name !== 'HEAD') names.add(name);
    if (this._current) names.add(this._current);

    return [...names]
      .sort((a, b) => a.localeCompare(b))
      .map((name) => ({ name, current: name === this._current }));
  }

  async listTags() {
    if (typeof this._git.listTags !== 'function') return [];
    try {
      const tags = await this._git.listTags({ fs: this._fs, dir: this._dir });
      return tags.filter((name) => name !== 'HEAD').sort((a, b) => a.localeCompare(b));
    } catch {
      return [];
    }
  }

  async setBranch(name) {
    this._current = name;
    this._refType = 'branch';
    this._oidCache.clear();
  }

  /** Switch to any ref: a branch, a tag, or a detached commit (by oid). */
  async setRef(ref) {
    const r = normalizeRef(ref);
    this._current = r.name;
    this._refType = r.type;
    this._oidCache.clear();
  }

  /** Ordered resolveRef candidates for a ref name of a given type. */
  _candidatesFor(name, type) {
    // 'HEAD' tracks the checked-out commit directly.
    if (name === 'HEAD') return ['HEAD'];
    if (type === 'tag') return [`refs/tags/${name}`, name];
    // branch: prefer the remote-tracking ref. `fetch` advances
    // refs/remotes/origin/* but never the local refs/heads/* of a read-only
    // clone, so resolving the local head first would make "Pull / Update"
    // silently show stale trees.
    return [`refs/remotes/origin/${name}`, `refs/heads/${name}`, name];
  }

  async _resolveOid(ref) {
    let type;
    let name;
    if (ref == null) {
      type = this._refType;
      name = this._current;
    } else {
      const r = normalizeRef(ref);
      type = r.type;
      name = r.name;
    }
    const key = `${type}:${name}`;
    if (this._oidCache.has(key)) return this._oidCache.get(key);

    // A commit ref *is* an oid; expand short oids when the engine supports it,
    // otherwise trust it as a full oid.
    if (type === 'commit') {
      let oid = name;
      if (typeof this._git.expandOid === 'function') {
        try {
          oid = await this._git.expandOid({ fs: this._fs, dir: this._dir, oid: name });
        } catch {
          /* assume a full oid */
        }
      }
      this._oidCache.set(key, oid);
      return oid;
    }

    const candidates = this._candidatesFor(name, type);
    let resolved = null;
    let lastErr = null;
    for (const candidate of candidates) {
      try {
        resolved = await this._git.resolveRef({
          fs: this._fs,
          dir: this._dir,
          ref: candidate,
        });
        if (resolved) break;
      } catch (err) {
        lastErr = err;
      }
    }
    if (!resolved) {
      throw lastErr || new Error(`Could not resolve ref: ${name}`);
    }
    this._oidCache.set(key, resolved);
    return resolved;
  }

  async listFiles(ref) {
    const oid = await this._resolveOid(ref);
    const { kinds } = await this._entries(oid);
    return [...kinds.keys()];
  }

  async readFile(path, ref) {
    const oid = await this._resolveOid(ref);
    const { blob } = await this._git.readBlob({
      fs: this._fs,
      dir: this._dir,
      oid,
      filepath: path,
    });
    return blob;
  }

  /**
   * Classify a path so the viewer can render a symlink/submodule notice instead
   * of treating it as an ordinary file. Returns `{ kind: 'file' }` for normal
   * blobs (the common case) and for anything it can't resolve.
   *
   * @param {string} path
   * @param {Ref|string} [ref]
   * @returns {Promise<{kind: string, target?: string, url?: ?string, name?: ?string, oid?: ?string}>}
   */
  async entryMeta(path, ref) {
    const oid = await this._resolveOid(ref);
    const { kinds, submodules } = await this._entries(oid);
    const kind = kinds.get(path) || 'file';
    if (kind === 'symlink') {
      let target = '';
      try {
        const { blob } = await this._git.readBlob({
          fs: this._fs,
          dir: this._dir,
          oid,
          filepath: path,
        });
        target = symlinkTarget(blob);
      } catch {
        /* fall back to an empty target */
      }
      return { kind, target };
    }
    if (kind === 'submodule') {
      const info = (await this._gitmodules(oid)).get(path) || {};
      return {
        kind,
        url: info.url || null,
        name: info.name || null,
        oid: submodules.get(path) || null,
      };
    }
    return { kind };
  }

  /**
   * Walk a commit's tree once, recording every non-directory entry's path and
   * kind (so symlinks/submodules are navigable and classifiable) plus the
   * pinned oid of each submodule. Cached per commit oid.
   *
   * @param {string} oid  commit oid
   * @returns {Promise<{kinds: Map<string,string>, submodules: Map<string,string>}>}
   */
  async _entries(oid) {
    if (this._entryCache.has(oid)) return this._entryCache.get(oid);
    const { TREE, walk } = this._git;
    const kinds = new Map();
    const submodules = new Map();
    await walk({
      fs: this._fs,
      dir: this._dir,
      trees: [TREE({ ref: oid })],
      map: async (filepath, [entry]) => {
        if (filepath === '.' || !entry) return undefined;
        const type = await entry.type();
        if (type === 'tree') return undefined; // let walk descend on its own
        if (type === 'commit') {
          kinds.set(filepath, 'submodule');
          try {
            submodules.set(filepath, await entry.oid());
          } catch {
            /* a gitlink with no readable oid still lists as a submodule */
          }
          return undefined;
        }
        const mode = await entry.mode();
        kinds.set(filepath, classifyGitMode(mode) === 'symlink' ? 'symlink' : 'file');
        return undefined;
      },
    });
    const result = { kinds, submodules };
    this._entryCache.set(oid, result);
    return result;
  }

  /** Parsed `.gitmodules` for a commit (empty map when absent). Cached per oid. */
  async _gitmodules(oid) {
    if (this._gitmodulesCache.has(oid)) return this._gitmodulesCache.get(oid);
    let map = new Map();
    try {
      const { blob } = await this._git.readBlob({
        fs: this._fs,
        dir: this._dir,
        oid,
        filepath: '.gitmodules',
      });
      map = parseGitmodules(blob);
    } catch {
      /* no .gitmodules in this tree */
    }
    this._gitmodulesCache.set(oid, map);
    return map;
  }

  async headCommit(ref) {
    const commits = await this.log(1, ref);
    return commits[0] || null;
  }

  async log(limit = 50, ref) {
    const oid = await this._resolveOid(ref);
    const entries = await this._git.log({
      fs: this._fs,
      dir: this._dir,
      ref: oid,
      depth: limit,
    });
    return entries.map(toCommit);
  }

  /** Commits that changed a given file (isomorphic-git's filepath-filtered log). */
  async fileLog(path, limit = 50, ref) {
    const oid = await this._resolveOid(ref);
    const entries = await this._git.log({
      fs: this._fs,
      dir: this._dir,
      ref: oid,
      depth: limit,
      filepath: path,
      // Don't throw if the file is absent from the tip commit; just report the
      // commits where it did exist/change.
      force: true,
    });
    return entries.map(toCommit);
  }

  /**
   * Per-line blame: attribute each line of `path` (at `ref`) to the commit that
   * last changed it. Built from the file's filtered history plus the blob's
   * content at each of those commits, then the pure algorithm in blame.js.
   *
   * @param {string} path
   * @param {Ref|string} [ref]
   * @returns {Promise<{line: string, commit: Commit}[]>}  empty when untracked
   */
  async blame(path, ref) {
    const commits = await this.fileLog(path, BLAME_MAX_COMMITS, ref);
    if (!commits.length) return [];
    const versions = [];
    for (const commit of commits) {
      let blob;
      try {
        ({ blob } = await this._git.readBlob({
          fs: this._fs,
          dir: this._dir,
          oid: commit.oid,
          filepath: path,
        }));
      } catch {
        // The path didn't exist at this commit (a rename/creation boundary in a
        // history that still lists it); the versions gathered so far suffice.
        break;
      }
      versions.push({ commit, content: blob });
    }
    return blameLines(versions);
  }

  /**
   * Files that differ between two refs by walking both trees. A null baseRef
   * compares against the empty tree (every blob is an addition), which is what
   * the root commit's diff needs.
   */
  async changedFiles(baseRef, headRef) {
    const { TREE, walk } = this._git;
    const headOid = await this._resolveOid(headRef);
    const trees = [];
    let baseOid = null;
    if (baseRef != null) {
      baseOid = await this._resolveOid(baseRef);
      trees.push(TREE({ ref: baseOid }));
    }
    trees.push(TREE({ ref: headOid }));
    const baseIdx = baseRef != null ? 0 : -1;
    const headIdx = trees.length - 1;

    const changes = await walk({
      fs: this._fs,
      dir: this._dir,
      trees,
      map: async (filepath, entries) => {
        if (filepath === '.') return undefined;
        const a = baseIdx >= 0 ? entries[baseIdx] : null;
        const b = entries[headIdx];
        const [aType, bType] = await Promise.all([
          a ? a.type() : null,
          b ? b.type() : null,
        ]);
        // Only compare blobs; let walk descend into directories on its own.
        if (aType === 'tree' || bType === 'tree') return undefined;
        const [aOid, bOid] = await Promise.all([
          a ? a.oid() : null,
          b ? b.oid() : null,
        ]);
        if (aOid === bOid) return undefined;
        let status;
        if (!aOid) status = 'added';
        else if (!bOid) status = 'removed';
        else status = 'modified';
        return { path: filepath, status, oldOid: aOid, newOid: bOid };
      },
      // Flatten the per-node results, dropping the undefined (unchanged) ones.
      reduce: async (parent, children) => {
        const flat = [];
        for (const child of children) {
          if (Array.isArray(child)) flat.push(...child);
          else if (child) flat.push(child);
        }
        if (parent) flat.push(parent);
        return flat;
      },
    });

    const list = Array.isArray(changes) ? changes : [];
    list.sort((x, y) => (x.path < y.path ? -1 : x.path > y.path ? 1 : 0));
    return list;
  }

  /**
   * Fetch from origin using the same scope the repo was cloned with, then
   * report whether the current branch's tip actually moved.
   *
   * @returns {Promise<{updated: boolean, changed: boolean, oldOid: ?string, newOid: ?string}>}
   */
  async update(onProgress) {
    // Only a branch checkout has a remote branch to narrow a single-branch
    // fetch to; on a tag or detached commit we fetch the cloned scope and the
    // tip simply won't move.
    const onBranch = this._refType === 'branch';
    const branch = this._current;
    let oldOid = null;
    try {
      oldOid = await this._resolveOid();
    } catch {
      /* ref may not resolve yet; treat as unknown */
    }

    await this._git.fetch({
      fs: this._fs,
      http: this._http,
      dir: this._dir,
      corsProxy: this._corsProxy,
      onAuth: this._onAuth,
      ref: this._singleBranch && onBranch ? branch : undefined,
      singleBranch: this._singleBranch,
      depth: this._depth > 0 ? this._depth : undefined,
      tags: false,
      // Pruning is only meaningful when we track every remote branch.
      prune: !this._singleBranch,
      onProgress,
    });

    this._oidCache.clear();
    let newOid = null;
    try {
      newOid = await this._resolveOid();
    } catch {
      /* ignore */
    }

    return {
      updated: true,
      changed: Boolean(newOid && newOid !== oldOid),
      oldOid,
      newOid,
    };
  }
}

/**
 * Manages the lightning-fs instance, the registry of cloned repos, and the
 * clone / open / remove lifecycle. One instance per page.
 */
export class GitStorage {
  /**
   * @param {{fs?: object, git?: object, http?: object}} [engine]
   *   Optional pre-built engine. In the browser this is omitted and the
   *   vendored isomorphic-git + lightning-fs bundles are lazy-loaded on first
   *   use. A Node host (or a test) can inject its own `fs` / `git` / `http`
   *   so the same clone / open / update logic runs without the browser
   *   bootstrap (vendored `<script>` tags + lightning-fs).
   */
  constructor(engine = null) {
    this._fs = (engine && engine.fs) || null;
    this._git = (engine && engine.git) || null;
    this._http = (engine && engine.http) || null;
    // Per-dir promise chains used as an in-tab fallback when the Web Locks API
    // (which also coordinates across tabs) isn't available.
    this._lockChains = new Map();
  }

  async _ensure() {
    if (this._fs && this._git && this._http) return;
    const { git, http, FS } = await loadGitGlobals();
    this._git = this._git || git;
    this._http = this._http || http;
    this._fs = this._fs || new FS(FS_NAME);
  }

  /** Registry entries (most recently used first). Sync; no engine needed. */
  listRepos() {
    return readRegistry().sort((a, b) => (b.lastUsed || 0) - (a.lastUsed || 0));
  }

  _upsert(entry) {
    const list = readRegistry().filter((r) => r.dir !== entry.dir);
    list.push(entry);
    writeRegistry(list);
  }

  _touch(dir) {
    const list = readRegistry();
    const entry = list.find((r) => r.dir === dir);
    if (entry) {
      entry.lastUsed = Date.now();
      writeRegistry(list);
    }
  }

  /**
   * Override the stored CORS proxy for one repository. Takes effect the next
   * time the repo is opened (an already-open source keeps the proxy it was
   * built with). Sync; no engine needed. Returns whether an entry was updated.
   *
   * @param {string} dir
   * @param {string} corsProxy  the proxy URL, or '' for none/self-hosted
   * @returns {boolean}
   */
  setCorsProxy(dir, corsProxy) {
    const list = readRegistry();
    const entry = list.find((r) => r.dir === dir);
    if (!entry) return false;
    entry.corsProxy = corsProxy || '';
    writeRegistry(list);
    return true;
  }

  /**
   * Run `fn` while holding an exclusive lock for `dir`. Uses the Web Locks API
   * when available (which serializes across tabs as well as within one), and
   * falls back to a per-dir promise chain that at least serializes this tab.
   */
  _withLock(dir, fn) {
    const locks = globalThis.navigator && globalThis.navigator.locks;
    if (locks && typeof locks.request === 'function') {
      return locks.request(`git-browser:op:${dir}`, fn);
    }
    const prev = this._lockChains.get(dir) || Promise.resolve();
    const run = prev.then(() => fn());
    // Keep the tail unrejected so one failed op can't poison the next.
    this._lockChains.set(dir, run.then(() => {}, () => {}));
    return run;
  }

  /**
   * Subscribe to repository-set changes made by *other* tabs (a clone or
   * remove). The browser fires a `storage` event in every *other* tab when the
   * registry's localStorage value changes, which is exactly the cross-tab
   * signal we need — no BroadcastChannel handle to manage. Returns an
   * unsubscribe function.
   */
  onReposChanged(listener) {
    if (typeof globalThis.addEventListener !== 'function') return () => {};
    const onStorage = (e) => {
      // key === null is a localStorage.clear(); otherwise only our key matters.
      if (!e || e.key === null || e.key === REGISTRY_KEY) listener();
    };
    globalThis.addEventListener('storage', onStorage);
    return () => globalThis.removeEventListener('storage', onStorage);
  }

  async clone(params) {
    await this._ensure();
    // Lock the destination so two tabs (or two quick submits) can't clone or
    // remove the same dir concurrently and corrupt the FS / registry.
    return this._withLock(params.dir, () => this._cloneLocked(params));
  }

  async _cloneLocked({ url, dir, fullName, ref, depth, singleBranch, corsProxy, onProgress, onMessage }) {
    // Start fresh so re-cloning the same location can't mix histories.
    await rmrf(this._fs, dir);
    await mkdirp(this._fs, dir);

    const options = {
      fs: this._fs,
      http: this._http,
      dir,
      url,
      corsProxy: corsProxy || undefined,
      onAuth: makeOnAuth(),
      singleBranch: Boolean(singleBranch),
      noCheckout: true,
      onProgress,
      onMessage,
    };
    if (ref) options.ref = ref;
    if (Number.isFinite(depth) && depth > 0) options.depth = depth;

    try {
      await this._git.clone(options);
    } catch (err) {
      // A clone that fails mid-write leaves a half-populated dir the registry
      // never records. Remove it so it can't accumulate or shadow a retry.
      await rmrf(this._fs, dir).catch(() => {});
      throw err;
    }

    this._upsert({
      dir,
      url,
      fullName: fullName || dir.replace(/^\//, ''),
      addedAt: Date.now(),
      lastUsed: Date.now(),
      singleBranch: Boolean(singleBranch),
      depth: Number.isFinite(depth) && depth > 0 ? depth : 0,
      corsProxy: corsProxy || '',
    });

    return this.open(dir);
  }

  async open(dir) {
    await this._ensure();
    const meta = readRegistry().find((r) => r.dir === dir) || {};
    this._touch(dir);
    const source = new GitRepoSource({
      fs: this._fs,
      git: this._git,
      http: this._http,
      dir,
      url: meta.url,
      fullName: meta.fullName,
      corsProxy: meta.corsProxy,
      singleBranch: meta.singleBranch,
      depth: meta.depth,
    });
    await source.init();
    return source;
  }

  async remove(dir) {
    await this._ensure();
    await this._withLock(dir, async () => {
      await rmrf(this._fs, dir);
      writeRegistry(readRegistry().filter((r) => r.dir !== dir));
    });
  }

  /**
   * Reconcile the FS with the registry: delete repository directories that the
   * registry doesn't know about (leftovers from a clone that failed before it
   * was recorded, or a registry that was cleared) and prune the empty container
   * dirs left behind. Returns the repo dirs that were removed.
   */
  async repair() {
    await this._ensure();
    const known = new Set(readRegistry().map((r) => r.dir));
    const repoDirs = await this._findRepoDirs('/');
    const removed = [];
    for (const dir of repoDirs) {
      if (known.has(dir)) continue;
      // Lock per-dir and re-check the registry inside it: another tab may be
      // mid-clone of this very path (created the dir, not yet recorded).
      const didRemove = await this._withLock(dir, async () => {
        if (readRegistry().some((r) => r.dir === dir)) return false;
        await rmrf(this._fs, dir);
        return true;
      });
      if (didRemove) removed.push(dir);
    }
    await this._pruneEmptyDirs('/');
    return removed;
  }

  async _readdirSafe(path) {
    try {
      return await this._fs.promises.readdir(path);
    } catch {
      return [];
    }
  }

  async _isDir(path) {
    try {
      return (await this._fs.promises.lstat(path)).isDirectory();
    } catch {
      return false;
    }
  }

  /** Directories that look like git repositories (they contain a `.git` entry). */
  async _findRepoDirs(base) {
    const entries = await this._readdirSafe(base);
    // A repo root: stop here rather than descending into its `.git`.
    if (entries.includes('.git')) return [base];
    const found = [];
    for (const name of entries) {
      const child = base === '/' ? `/${name}` : `${base}/${name}`;
      if (await this._isDir(child)) found.push(...(await this._findRepoDirs(child)));
    }
    return found;
  }

  /** Depth-first removal of empty directories; never touches a repo root. */
  async _pruneEmptyDirs(base) {
    const entries = await this._readdirSafe(base);
    if (entries.includes('.git')) return; // a repo root: keep it
    for (const name of entries) {
      const child = base === '/' ? `/${name}` : `${base}/${name}`;
      if (await this._isDir(child)) await this._pruneEmptyDirs(child);
    }
    if (base !== '/' && (await this._readdirSafe(base)).length === 0) {
      try {
        await this._fs.promises.rmdir(base);
      } catch {
        /* racing with another tab, or not actually empty; leave it */
      }
    }
  }
}
