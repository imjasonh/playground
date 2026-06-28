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

const FS_NAME = 'git-browser-fs';
const REGISTRY_KEY = 'git-browser:repos';
const REGISTRY_VERSION = 1;

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
  };
}

/** Parent directory of a full lightning-fs path ("/a/b/c.txt" -> "/a/b"). */
function parentDir(fullPath) {
  const idx = fullPath.lastIndexOf('/');
  return idx <= 0 ? '/' : fullPath.slice(0, idx);
}

/**
 * RepoSource backed by a cloned repository living in lightning-fs.
 *
 * Reading is lazy and tree-based: branch switching just changes which commit
 * we read from. Writing is opt-in: the first edit materializes a working tree
 * for the current branch (a checkout) and from then on reads, status, commits,
 * and pushes operate against that working tree and the local branch ref.
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
    // Editable. Pushing additionally needs a remote URL.
    this.readOnly = false;
    this.canPush = Boolean(this.url);
    this._current = 'HEAD';
    this._oidCache = new Map();
    // Which branch (if any) is currently checked out into the working dir, and
    // which branches we now read from the local head (because they have been
    // checked out and may carry local commits not yet on origin).
    this._worktreeBranch = null;
    this._editedBranches = new Set();
  }

  async init() {
    try {
      const branch = await this._git.currentBranch({
        fs: this._fs,
        dir: this._dir,
        fullname: false,
      });
      if (branch) this._current = branch;
    } catch {
      /* keep HEAD */
    }
    try {
      await this._adoptLocalCommits();
    } catch {
      /* best effort; fall back to the default remote-tracking read path */
    }
    return this;
  }

  /**
   * On open, decide whether the local branch is authoritative. A fresh clone
   * has local == remote, and a plain `fetch` leaves the local head *behind*
   * origin (so we keep preferring the remote-tracking ref). But once a local
   * commit lands (this or a previous session, persisted in IndexedDB), the
   * local head is *ahead* of origin and must win — otherwise reopening the repo
   * would hide those commits, and the next edit would discard them.
   *
   * The resolved head is primed into the cache so this costs no extra ref reads
   * on the subsequent first access.
   */
  async _adoptLocalCommits() {
    const branch = this._current;
    if (!branch || branch === 'HEAD') return;

    let localHead = null;
    try {
      localHead = await this._git.resolveRef({ fs: this._fs, dir: this._dir, ref: `refs/heads/${branch}` });
    } catch {
      return; // no local branch ref; nothing to adopt
    }
    if (!localHead) return;

    let remoteHead = null;
    try {
      remoteHead = await this._git.resolveRef({ fs: this._fs, dir: this._dir, ref: `refs/remotes/origin/${branch}` });
    } catch {
      remoteHead = null;
    }

    if (!remoteHead) {
      // Local-only branch: the local head is the only truth.
      this._editedBranches.add(branch);
      this._oidCache.set(branch, localHead);
      return;
    }
    if (localHead === remoteHead) {
      this._oidCache.set(branch, remoteHead);
      return;
    }

    let localAhead = false;
    try {
      localAhead = await this._git.isDescendent({
        fs: this._fs,
        dir: this._dir,
        oid: localHead,
        ancestor: remoteHead,
        depth: -1,
      });
    } catch {
      localAhead = false;
    }

    if (localAhead) {
      this._editedBranches.add(branch);
      this._oidCache.set(branch, localHead);
    } else {
      this._oidCache.set(branch, remoteHead);
    }
  }

  getCurrentBranch() {
    return this._current;
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

  async setBranch(name) {
    this._current = name;
    this._oidCache.clear();
  }

  /** True when the current branch is materialized in the working directory. */
  _inWorktreeMode() {
    return this._worktreeBranch !== null && this._worktreeBranch === this._current;
  }

  async _resolveOid(ref) {
    const key = ref || this._current;
    if (this._oidCache.has(key)) return this._oidCache.get(key);

    // For a branch we've started editing, the local head is authoritative: it
    // was reset to the displayed commit at checkout and then advances with each
    // local commit, so it must win over the (now older) remote-tracking ref.
    //
    // Otherwise prefer the remote-tracking ref: `fetch` advances
    // refs/remotes/origin/* but never the local refs/heads/* of a fresh clone,
    // so resolving the local head first would make "Pull / Update" show stale
    // trees. 'HEAD' is resolved as-is (it tracks the checked-out commit).
    const editing = this._editedBranches.has(key);
    const candidates =
      key === 'HEAD'
        ? ['HEAD']
        : editing
          ? [`refs/heads/${key}`, `refs/remotes/origin/${key}`, key]
          : [`refs/remotes/origin/${key}`, `refs/heads/${key}`, key];
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
      throw lastErr || new Error(`Could not resolve ref: ${key}`);
    }
    this._oidCache.set(key, resolved);
    return resolved;
  }

  /** True when a read for `ref` should come from the live working tree. */
  _readsFromWorktree(ref) {
    return this._inWorktreeMode() && (!ref || ref === this._current);
  }

  async listFiles(ref) {
    if (this._readsFromWorktree(ref)) {
      // Derive the file list from the working tree so freshly created (and not
      // yet deleted) files appear immediately, before they are committed.
      const rows = await this._git.statusMatrix({ fs: this._fs, dir: this._dir });
      return rows.filter((row) => row[2] !== 0).map((row) => row[0]);
    }
    const oid = await this._resolveOid(ref);
    return this._git.listFiles({ fs: this._fs, dir: this._dir, ref: oid });
  }

  async readFile(path, ref) {
    if (this._readsFromWorktree(ref)) {
      // Read the working-tree copy so uncommitted edits are visible.
      return this._fs.promises.readFile(`${this._dir}/${path}`);
    }
    const oid = await this._resolveOid(ref);
    const { blob } = await this._git.readBlob({
      fs: this._fs,
      dir: this._dir,
      oid,
      filepath: path,
    });
    return blob;
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

  /**
   * Fetch from origin using the same scope the repo was cloned with, then
   * report whether the current branch's tip actually moved.
   *
   * @returns {Promise<{updated: boolean, changed: boolean, oldOid: ?string, newOid: ?string}>}
   */
  async update(onProgress) {
    const branch = this._current;
    let oldOid = null;
    try {
      oldOid = await this._resolveOid(branch);
    } catch {
      /* branch may not resolve yet; treat as unknown */
    }

    await this._git.fetch({
      fs: this._fs,
      http: this._http,
      dir: this._dir,
      corsProxy: this._corsProxy,
      ref: this._singleBranch ? branch : undefined,
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
      newOid = await this._resolveOid(branch);
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

  /* ---------------------------------------------------------------- */
  /* Write surface                                                    */
  /* ---------------------------------------------------------------- */

  /**
   * Materialize the current branch into the working directory so add / commit
   * have a real tree and index to work against. The clone is `noCheckout`, so
   * until this runs there is no working tree. Resets the local branch ref to
   * the commit we are currently displaying (the remote-tracking tip) before
   * checking out, so edits build on what the user actually sees.
   */
  async _ensureWorktree(onProgress) {
    const branch = this._current;
    if (branch === 'HEAD') {
      throw new Error('Detached HEAD — open a branch before editing.');
    }
    if (this._worktreeBranch === branch) return;

    const displayOid = await this._resolveOid(branch);
    await this._git.writeRef({
      fs: this._fs,
      dir: this._dir,
      ref: `refs/heads/${branch}`,
      value: displayOid,
      force: true,
    });
    await this._git.checkout({
      fs: this._fs,
      dir: this._dir,
      ref: branch,
      force: true,
      onProgress,
    });

    this._worktreeBranch = branch;
    this._editedBranches.add(branch);
    // Subsequent reads of this branch follow the (now authoritative) local head.
    this._oidCache.delete(branch);
  }

  async writeFile(path, content) {
    await this._ensureWorktree();
    const full = `${this._dir}/${path}`;
    await mkdirp(this._fs, parentDir(full));
    const bytes = content instanceof Uint8Array ? content : new TextEncoder().encode(String(content));
    await this._fs.promises.writeFile(full, bytes);
    await this._git.add({ fs: this._fs, dir: this._dir, filepath: path });
    this._oidCache.delete(this._current);
  }

  async deleteFile(path) {
    await this._ensureWorktree();
    try {
      await this._fs.promises.unlink(`${this._dir}/${path}`);
    } catch (err) {
      if (!err || err.code !== 'ENOENT') throw err;
    }
    await this._git.remove({ fs: this._fs, dir: this._dir, filepath: path });
    this._oidCache.delete(this._current);
  }

  /** Working-tree changes (vs HEAD) staged for the next commit. */
  async status() {
    if (!this._inWorktreeMode()) return [];
    const rows = await this._git.statusMatrix({ fs: this._fs, dir: this._dir });
    const changes = [];
    for (const [filepath, head, workdir] of rows) {
      if (head === 1 && workdir === 1) continue; // unchanged
      changes.push({
        path: filepath,
        status: head === 0 ? 'new' : workdir === 0 ? 'deleted' : 'modified',
      });
    }
    changes.sort((a, b) => a.path.localeCompare(b.path));
    return changes;
  }

  async commit({ message, author } = {}) {
    await this._ensureWorktree();
    const summary = (message || '').trim();
    if (!summary) throw new Error('A commit message is required.');
    const changes = await this.status();
    if (changes.length === 0) throw new Error('Nothing to commit.');

    const oid = await this._git.commit({
      fs: this._fs,
      dir: this._dir,
      message: summary,
      author: {
        name: (author && author.name) || 'You',
        email: (author && author.email) || 'you@example.com',
        timestamp: Math.floor(Date.now() / 1000),
      },
    });

    // The commit advanced refs/heads/<branch>; re-resolve from the local head.
    this._oidCache.delete(this._current);
    return { oid };
  }

  /**
   * Push the current branch to origin. Authentication is supplied per-request
   * via `onAuth` (a token, never persisted to disk by this layer).
   */
  async push({ token, username, onProgress, onMessage, force } = {}) {
    if (!this.canPush) {
      throw new Error('This repository has no remote to push to.');
    }
    const branch = this._current;
    if (branch === 'HEAD') {
      throw new Error('Detached HEAD — open a branch before pushing.');
    }

    const result = await this._git.push({
      fs: this._fs,
      http: this._http,
      dir: this._dir,
      corsProxy: this._corsProxy,
      remote: 'origin',
      ref: branch,
      force: Boolean(force),
      onProgress,
      onMessage,
      onAuth: () =>
        token
          ? username
            ? { username, password: token }
            : { username: token, password: '' }
          : {},
    });

    if (result && (result.ok === false || result.error)) {
      throw new Error(result.error || 'The remote rejected the push.');
    }
    return { ok: true, branch, result };
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

  async clone({ url, dir, fullName, ref, depth, singleBranch, corsProxy, onProgress, onMessage }) {
    await this._ensure();

    // Start fresh so re-cloning the same location can't mix histories.
    await rmrf(this._fs, dir);
    await mkdirp(this._fs, dir);

    const options = {
      fs: this._fs,
      http: this._http,
      dir,
      url,
      corsProxy: corsProxy || undefined,
      singleBranch: Boolean(singleBranch),
      noCheckout: true,
      onProgress,
      onMessage,
    };
    if (ref) options.ref = ref;
    if (Number.isFinite(depth) && depth > 0) options.depth = depth;

    await this._git.clone(options);

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
    await rmrf(this._fs, dir);
    writeRegistry(readRegistry().filter((r) => r.dir !== dir));
  }
}
