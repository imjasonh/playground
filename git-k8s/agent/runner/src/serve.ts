import { timingSafeEqual } from "node:crypto";
import { once } from "node:events";
import { readFile } from "node:fs/promises";
import { createServer, type Server } from "node:http";

/**
 * Returns a server that answers GET /result with body, but only to a
 * request with the bearer token. The operator uses the Pod's UID, which it
 * reads from the API server, so other Pods that can reach this one can't
 * read the result.
 */
export function resultServer(body: Buffer, token: string, log: (line: string) => void = () => undefined): Server {
  const expected = Buffer.from(`Bearer ${token}`);
  return createServer((req, res) => {
    let status = 200;
    const got = Buffer.from(req.headers.authorization ?? "");
    if (req.url !== "/result") {
      status = 404;
    } else if (req.method !== "GET") {
      status = 405;
    } else if (got.length !== expected.length || !timingSafeEqual(got, expected)) {
      status = 401;
    }
    log(`${req.method} ${req.url} ${status}`);
    if (status !== 200) {
      res.writeHead(status, { Connection: "close" }).end();
      return;
    }
    res.writeHead(200, { "Content-Type": "application/json", "Content-Length": body.length }).end(body);
  });
}

/**
 * Serves the result file on PORT until the container stops. POD_UID is the
 * bearer token.
 */
export async function serveFromEnv(env: NodeJS.ProcessEnv): Promise<Server> {
  const token = env.POD_UID;
  if (!token) {
    throw new Error("POD_UID isn't set");
  }
  const path = env.RESULT_FILE || "/result/result.json";
  const port = Number(env.PORT || "8080");
  const body = await readFile(path);
  const server = resultServer(body, token, (line) => console.log(line));
  server.listen(port);
  await once(server, "listening");
  console.log(`serving ${path} on port ${port}`);
  return server;
}
