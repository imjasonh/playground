import { execFileSync, spawn } from "node:child_process";
import { once } from "node:events";
import { mkdtempSync, mkdirSync, rmSync, writeFileSync } from "node:fs";
import http from "node:http";
import { tmpdir } from "node:os";
import { join } from "node:path";

const GIT_ENV = {
  GIT_AUTHOR_NAME: "Browser Tester",
  GIT_AUTHOR_EMAIL: "browser@example.com",
  GIT_COMMITTER_NAME: "Browser Tester",
  GIT_COMMITTER_EMAIL: "browser@example.com",
  GIT_CONFIG_GLOBAL: "/dev/null",
  GIT_CONFIG_SYSTEM: "/dev/null",
};

function git(cwd, args, env = {}) {
  return execFileSync("git", args, {
    cwd,
    env: { ...process.env, ...GIT_ENV, ...env },
    stdio: ["ignore", "pipe", "pipe"],
  }).toString();
}

export function createServedRepo() {
  const root = mkdtempSync(join(tmpdir(), "gitdb-web-"));
  const work = join(root, "work");
  mkdirSync(work);
  git(work, ["init", "-q", "-b", "main"]);

  writeFileSync(join(work, "README.md"), "# Live repository\n\nfirst line\n");
  writeFileSync(join(work, "app.js"), "export const version = 1;\n");
  git(work, ["add", "."]);
  git(work, ["commit", "-q", "-m", "Initial live commit"], {
    GIT_AUTHOR_DATE: "2021-01-01T10:00:00Z",
    GIT_COMMITTER_DATE: "2021-01-01T10:00:00Z",
  });
  git(work, ["tag", "-a", "v1.0", "-m", "release 1.0"]);

  writeFileSync(join(work, "README.md"), "# Live repository\n\nsecond line\n");
  writeFileSync(join(work, "app.js"), "export const version = 2;\n");
  git(work, ["add", "."]);
  git(work, ["commit", "-q", "-m", "Update real data"], {
    GIT_AUTHOR_DATE: "2021-01-02T10:00:00Z",
    GIT_COMMITTER_DATE: "2021-01-02T10:00:00Z",
  });

  git(root, ["clone", "-q", "--bare", work, "repo.git"]);
  return {
    root,
    repoPath: "repo.git",
    cleanup: () => rmSync(root, { recursive: true, force: true }),
  };
}

function pipeCGI(stdout, res) {
  let header = Buffer.alloc(0);
  let parsing = true;
  stdout.on("data", (chunk) => {
    if (!parsing) {
      res.write(chunk);
      return;
    }
    header = Buffer.concat([header, chunk]);
    let index = header.indexOf("\r\n\r\n");
    let separatorLength = 4;
    if (index === -1) {
      index = header.indexOf("\n\n");
      separatorLength = 2;
    }
    if (index === -1) return;

    const headers = header.slice(0, index).toString("utf8");
    const rest = header.slice(index + separatorLength);
    parsing = false;
    for (const line of headers.split(/\r?\n/)) {
      const match = /^([^:]+):\s*(.*)$/.exec(line);
      if (!match) continue;
      if (match[1].toLowerCase() === "status") {
        res.statusCode = Number.parseInt(match[2], 10) || 200;
      } else {
        res.setHeader(match[1], match[2]);
      }
    }
    if (rest.length) res.write(rest);
  });
  stdout.on("end", () => res.end());
}

function setCORS(req, res) {
  res.setHeader("Access-Control-Allow-Origin", req.headers.origin || "*");
  res.setHeader("Access-Control-Allow-Methods", "GET, POST, OPTIONS");
  res.setHeader(
    "Access-Control-Allow-Headers",
    req.headers["access-control-request-headers"] || "Content-Type, Git-Protocol",
  );
  res.setHeader(
    "Access-Control-Expose-Headers",
    "Content-Type, Content-Length",
  );
}

export async function startGitHTTPServer(projectRoot) {
  const server = http.createServer((req, res) => {
    setCORS(req, res);
    if (req.method === "OPTIONS") {
      res.writeHead(204);
      res.end();
      return;
    }

    const requestURL = new URL(req.url, "http://127.0.0.1");
    const env = {
      ...process.env,
      GIT_PROJECT_ROOT: projectRoot,
      GIT_HTTP_EXPORT_ALL: "1",
      REQUEST_METHOD: req.method,
      PATH_INFO: decodeURIComponent(requestURL.pathname),
      QUERY_STRING: requestURL.searchParams.toString(),
      CONTENT_TYPE: req.headers["content-type"] || "",
      REMOTE_ADDR: req.socket.remoteAddress || "127.0.0.1",
    };
    if (req.headers["content-length"]) {
      env.CONTENT_LENGTH = req.headers["content-length"];
    }
    if (req.headers["git-protocol"]) {
      env.GIT_PROTOCOL = req.headers["git-protocol"];
    }

    const backend = spawn("git", ["http-backend"], { env });
    backend.on("error", (error) => {
      if (!res.headersSent) res.writeHead(500);
      res.end(`git http-backend failed: ${error.message}`);
    });
    backend.stderr.resume();
    req.pipe(backend.stdin);
    pipeCGI(backend.stdout, res);
  });

  server.listen(0, "127.0.0.1");
  await once(server, "listening");
  const { port } = server.address();
  return {
    url: `http://127.0.0.1:${port}`,
    close: () => new Promise((resolve) => server.close(resolve)),
  };
}
