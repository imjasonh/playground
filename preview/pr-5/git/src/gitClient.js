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

function readRegistry() {
  try {
    const raw = localStorage.getItem(REGISTRY_KEY);
    const list = raw ? JSON.parse(raw) : [];
    return Array.isArray(list) ? list : [];
  } catch {
    return [];
  }
}

function writeRegistry(list) {
  try {
    localStorage.setItem(REGISTRY_KEY, JSON.stringify(list));
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

/**
 * RepoSource backed by a cloned repository living in lightning-fs.
 * Read-only: branch switching just changes which tree we read from.
 */
export class GitRepoSource {
  constructor({ fs, git, http, dir, url, fullName, corsProxy }) {
    this._fs = fs;
    this._git = git;
    this._http = http;
    this._dir = dir;
    this.url = url || null;
    this.fullName = fullName || dir.replace(/^\//, '');
    this._corsProxy = corsProxy || undefined;
    this._current = 'HEAD';
    this._oidCache = new Map();
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
    return this;
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

  async _resolveOid(ref) {
    const key = ref || this._current;
    if (this._oidCache.has(key)) return this._oidCache.get(key);

    const candidates = [
      key,
      `refs/heads/${key}`,
      `refs/remotes/origin/${key}`,
    ];
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

  async listFiles(ref) {
    const oid = await this._resolveOid(ref);
    return this._git.listFiles({ fs: this._fs, dir: this._dir, ref: oid });
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

  /** Fetch the latest commits for all branches and refresh resolved tips. */
  async update(onProgress) {
    await this._git.fetch({
      fs: this._fs,
      http: this._http,
      dir: this._dir,
      corsProxy: this._corsProxy,
      singleBranch: false,
      tags: false,
      prune: true,
      onProgress,
    });
    this._oidCache.clear();
    return { updated: true };
  }
}

/**
 * Manages the lightning-fs instance, the registry of cloned repos, and the
 * clone / open / remove lifecycle. One instance per page.
 */
export class GitStorage {
  constructor() {
    this._fs = null;
    this._git = null;
    this._http = null;
  }

  async _ensure() {
    if (this._fs) return;
    const { git, http, FS } = await loadGitGlobals();
    this._git = git;
    this._http = http;
    this._fs = new FS(FS_NAME);
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
