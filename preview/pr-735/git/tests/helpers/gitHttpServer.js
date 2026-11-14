/**
 * Test helpers for the real clone/fetch path: a smart-HTTP git server backed by
 * `git http-backend` (CGI) and a small repository builder. Everything binds to
 * 127.0.0.1 and shells out to the local `git` binary, so tests exercise the
 * actual isomorphic-git network protocol without any external egress.
 */
import http from 'node:http';
import { execFileSync, spawn } from 'node:child_process';
import { once } from 'node:events';
import { mkdtempSync, mkdirSync, writeFileSync, symlinkSync, existsSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

/** Resolve the directory holding git's helper executables (git-core). */
function gitExecPath() {
  try {
    return execFileSync('git', ['--exec-path'], { stdio: ['ignore', 'pipe', 'ignore'] })
      .toString()
      .trim();
  } catch {
    return null;
  }
}

/** Whether `git` and `git http-backend` are available on this machine. */
export function hasGitHttpBackend() {
  const execPath = gitExecPath();
  if (!execPath) return false;
  return (
    existsSync(join(execPath, 'git-http-backend')) ||
    existsSync(join(execPath, 'git-http-backend.exe'))
  );
}

const GIT_ENV = {
  GIT_AUTHOR_NAME: 'Integration Tester',
  GIT_AUTHOR_EMAIL: 'tester@example.com',
  GIT_COMMITTER_NAME: 'Integration Tester',
  GIT_COMMITTER_EMAIL: 'tester@example.com',
  // Isolate from any host-level git config (default branch, signing, hooks).
  GIT_CONFIG_GLOBAL: '/dev/null',
  GIT_CONFIG_SYSTEM: '/dev/null',
};

// A fabricated commit oid for the gitlink. A submodule references a commit that
// lives in another repository, so this object need not exist in our store.
export const SUBMODULE_OID = 'c0ffee0011223344556677889900aabbccddeeff';

function git(cwd, args) {
  return execFileSync('git', args, {
    cwd,
    stdio: ['ignore', 'pipe', 'pipe'],
    env: { ...process.env, ...GIT_ENV },
  }).toString();
}

/**
 * Build a bare repository (served over HTTP) with two branches that differ,
 * derived from a working tree we can keep committing to.
 *
 * @returns {{
 *   root: string, bare: string, work: string, repoPath: string,
 *   addCommitOnMain: (file: string, contents: string, message: string) => void,
 *   cleanup: () => void,
 * }}
 */
export function createServedRepo() {
  const root = mkdtempSync(join(tmpdir(), 'git-int-'));
  const work = join(root, 'work');
  mkdirSync(work);

  git(work, ['init', '-q', '-b', 'main']);
  writeFileSync(join(work, 'README.md'), '# Widget\n\nServed over a local git http-backend.\n');
  mkdirSync(join(work, 'src'));
  writeFileSync(join(work, 'src', 'index.js'), 'export default 1;\n');
  git(work, ['add', '.']);
  git(work, ['commit', '-q', '-m', 'Initial commit']);
  // An annotated tag on the initial commit, so tag browsing is observable.
  git(work, ['tag', '-a', 'v1.0', '-m', 'release 1.0']);

  // A second branch with an extra file so branch switching is observable.
  git(work, ['checkout', '-q', '-b', 'dev']);
  writeFileSync(join(work, 'src', 'dev.js'), 'export const dev = true;\n');
  git(work, ['add', '.']);
  git(work, ['commit', '-q', '-m', 'Add dev module']);
  git(work, ['checkout', '-q', 'main']);

  // A third branch carrying a symlink and a submodule (gitlink), so the special-
  // entry handling has real tree entries to classify. The submodule's commit
  // object is intentionally absent (that's what a gitlink is) — we add it
  // straight to the index with `update-index --cacheinfo`.
  git(work, ['checkout', '-q', '-b', 'special', 'main']);
  symlinkSync('src/index.js', join(work, 'latest.js'));
  git(work, ['add', 'latest.js']);
  git(work, [
    'update-index',
    '--add',
    '--cacheinfo',
    `160000,${SUBMODULE_OID},vendor/widget`,
  ]);
  writeFileSync(
    join(work, '.gitmodules'),
    '[submodule "widget"]\n\tpath = vendor/widget\n\turl = https://github.com/acme/widget.git\n'
  );
  git(work, ['add', '.gitmodules']);
  git(work, ['commit', '-q', '-m', 'Add a symlink and a submodule']);
  git(work, ['checkout', '-q', 'main']);

  // A fourth branch with one file edited across three commits, so blame has a
  // real per-commit history to attribute lines against. Each commit appends a
  // distinct, unambiguous line so the attribution can be asserted precisely.
  git(work, ['checkout', '-q', '-b', 'history', 'main']);
  const counterV1 = 'let count = 0;\nexport function inc() {\n  count += 1;\n}\n';
  const counterV2 = `${counterV1}export function reset() {\n  count = 0;\n}\n`;
  const counterV3 = `${counterV2}export function current() {\n  return count;\n}\n`;
  writeFileSync(join(work, 'counter.js'), counterV1);
  git(work, ['add', 'counter.js']);
  git(work, ['commit', '-q', '-m', 'Add counter']);
  writeFileSync(join(work, 'counter.js'), counterV2);
  git(work, ['add', 'counter.js']);
  git(work, ['commit', '-q', '-m', 'Add reset']);
  writeFileSync(join(work, 'counter.js'), counterV3);
  git(work, ['add', 'counter.js']);
  git(work, ['commit', '-q', '-m', 'Export current count']);
  git(work, ['checkout', '-q', 'main']);

  git(root, ['clone', '-q', '--bare', work, 'repo.git']);
  const bare = join(root, 'repo.git');
  git(bare, ['update-server-info']);

  return {
    root,
    bare,
    work,
    repoPath: 'repo.git',
    addCommitOnMain(file, contents, message) {
      writeFileSync(join(work, file), contents);
      git(work, ['add', '.']);
      git(work, ['commit', '-q', '-m', message]);
      // Advance the served (bare) repo's main so a fetch sees the new tip.
      git(work, ['push', '-q', bare, 'main']);
    },
    cleanup() {
      rmSync(root, { recursive: true, force: true });
    },
  };
}

/** Translate CGI stdout (headers, blank line, body) into an HTTP response. */
function pipeCgi(stdout, res) {
  let header = Buffer.alloc(0);
  let parsing = true;

  stdout.on('data', (chunk) => {
    if (!parsing) {
      res.write(chunk);
      return;
    }
    header = Buffer.concat([header, chunk]);
    let idx = header.indexOf('\r\n\r\n');
    let sep = 4;
    if (idx === -1) {
      idx = header.indexOf('\n\n');
      sep = 2;
    }
    if (idx === -1) return; // headers not complete yet
    const head = header.slice(0, idx).toString('utf8');
    const rest = header.slice(idx + sep);
    parsing = false;

    let status = 200;
    for (const line of head.split(/\r?\n/)) {
      const m = /^([^:]+):\s*(.*)$/.exec(line);
      if (!m) continue;
      if (m[1].toLowerCase() === 'status') status = parseInt(m[2], 10) || 200;
      else res.setHeader(m[1], m[2]);
    }
    res.statusCode = status;
    if (rest.length) res.write(rest);
  });
  stdout.on('end', () => res.end());
}

/**
 * Start a smart-HTTP git server (CGI over `git http-backend`) that serves every
 * repository under `projectRoot`, bound to a random port on 127.0.0.1.
 *
 * @param {{projectRoot: string}} opts
 * @returns {Promise<{url: string, port: number, close: () => Promise<void>}>}
 */
export async function startGitHttpServer({ projectRoot }) {
  const server = http.createServer((req, res) => {
    const url = new URL(req.url, 'http://127.0.0.1');
    const env = {
      ...process.env,
      GIT_PROJECT_ROOT: projectRoot,
      GIT_HTTP_EXPORT_ALL: '1',
      REQUEST_METHOD: req.method,
      PATH_INFO: decodeURIComponent(url.pathname),
      QUERY_STRING: url.searchParams.toString(),
      CONTENT_TYPE: req.headers['content-type'] || '',
      REMOTE_ADDR: req.socket.remoteAddress || '127.0.0.1',
    };
    if (req.headers['content-length']) env.CONTENT_LENGTH = req.headers['content-length'];
    // Pass through protocol negotiation (e.g. v2) when the client asks for it.
    if (req.headers['git-protocol']) env.GIT_PROTOCOL = req.headers['git-protocol'];

    const backend = spawn('git', ['http-backend'], { env });
    backend.on('error', (e) => {
      if (!res.headersSent) res.writeHead(500);
      res.end(`git http-backend failed: ${e.message}`);
    });
    backend.stderr.resume(); // drain so the child never blocks on a full pipe

    req.pipe(backend.stdin);
    pipeCgi(backend.stdout, res);
  });

  server.listen(0, '127.0.0.1');
  await once(server, 'listening');
  const { port } = server.address();
  return {
    url: `http://127.0.0.1:${port}`,
    port,
    close: () => new Promise((resolve) => server.close(() => resolve())),
  };
}
