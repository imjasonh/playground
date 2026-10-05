import assert from "node:assert/strict";
import { once } from "node:events";
import type { AddressInfo } from "node:net";
import { test } from "node:test";
import { resultServer, serveFromEnv } from "../src/serve.js";

test("serves the result only to a request with the token", async (t) => {
  const body = Buffer.from('{"verdict":"pass"}');
  const server = resultServer(body, "pod-uid");
  server.listen(0, "127.0.0.1");
  await once(server, "listening");
  t.after(() => {
    server.closeAllConnections();
    server.close();
  });
  const url = `http://127.0.0.1:${(server.address() as AddressInfo).port}`;
  const auth = { Authorization: "Bearer pod-uid" };

  const ok = await fetch(`${url}/result`, { headers: auth });
  assert.equal(ok.status, 200);
  assert.equal(ok.headers.get("content-type"), "application/json");
  assert.equal(await ok.text(), '{"verdict":"pass"}');

  const cases: [string, RequestInit, number][] = [
    ["/result", {}, 401],
    ["/result", { headers: { Authorization: "Bearer other" } }, 401],
    ["/result", { headers: { Authorization: "Bearer pod-uid-and-more" } }, 401],
    ["/", { headers: auth }, 404],
    ["/result?x=1", { headers: auth }, 404],
    ["/result", { method: "POST", headers: auth, body: "{}" }, 405],
  ];
  for (const [path, init, want] of cases) {
    const res = await fetch(`${url}${path}`, init);
    await res.arrayBuffer();
    assert.equal(res.status, want, `${init.method ?? "GET"} ${path}`);
  }
});

test("needs the Pod's UID", async () => {
  await assert.rejects(serveFromEnv({ RESULT_FILE: "/nonexistent" }), /POD_UID isn't set/);
});
