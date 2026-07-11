import test from "node:test";
import assert from "node:assert/strict";

import { redirectUri, SCOPES } from "../src/config.js";

test("required Web Playback scopes stay documented in one place", () => {
  for (const scope of [
    "streaming",
    "user-read-email",
    "user-read-private",
    "user-read-playback-state",
    "user-modify-playback-state",
  ]) {
    assert.match(SCOPES, new RegExp(`(?:^| )${scope}(?:$| )`));
  }
});

test("localhost redirect matches what npm start serves", () => {
  assert.equal(
    redirectUri({ origin: "http://localhost:3000", pathname: "/" }),
    "http://localhost:3000/",
  );
});
