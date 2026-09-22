import http from "node:http";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const MIME = {
  ".html": "text/html; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".css": "text/css; charset=utf-8",
  ".json": "application/json; charset=utf-8",
  ".svg": "image/svg+xml",
};

export function createHudServer(options = {}) {
  const hudDir = options.hudDir ?? defaultHudDir();
  const clients = new Set();
  let latest = null;

  const server = http.createServer((req, res) => {
    const url = new URL(req.url, "http://127.0.0.1");
    if (url.pathname === "/stream") {
      res.writeHead(200, {
        "Content-Type": "text/event-stream",
        "Cache-Control": "no-cache",
        Connection: "keep-alive",
        "Access-Control-Allow-Origin": "*",
      });
      res.write(":\n\n");
      clients.add(res);
      if (latest) {
        res.write(`data: ${JSON.stringify(latest)}\n\n`);
      }
      req.on("close", () => clients.delete(res));
      return;
    }
    if (url.pathname === "/health") {
      res.writeHead(200, { "Content-Type": "application/json" });
      res.end(JSON.stringify({ ok: true, clients: clients.size }));
      return;
    }
    let filePath = url.pathname === "/" ? "/index.html" : url.pathname;
    filePath = path.normalize(filePath).replace(/^(\.\.(\/|\\|$))+/, "");
    const full = path.join(hudDir, filePath);
    if (!full.startsWith(hudDir)) {
      res.writeHead(403);
      res.end("no");
      return;
    }
    fs.readFile(full, (err, data) => {
      if (err) {
        res.writeHead(404);
        res.end("not found");
        return;
      }
      res.writeHead(200, { "Content-Type": MIME[path.extname(full)] ?? "application/octet-stream" });
      res.end(data);
    });
  });

  return {
    server,
    publish(frame) {
      latest = frame;
      const line = `data: ${JSON.stringify(frame)}\n\n`;
      for (const res of clients) {
        res.write(line);
      }
    },
    listen(port = 8788) {
      return new Promise((resolve) => {
        server.listen(port, "127.0.0.1", () => resolve(server.address()));
      });
    },
    close() {
      for (const res of clients) {
        res.end();
      }
      return new Promise((resolve) => server.close(resolve));
    },
  };
}

function defaultHudDir() {
  return path.join(path.dirname(fileURLToPath(import.meta.url)), "..", "hud");
}
