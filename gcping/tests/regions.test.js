import test from "node:test";
import assert from "node:assert/strict";

import {
  GLOBAL_ID,
  PING_BUCKET,
  REGIONS,
  hostFor,
  pingUrl,
} from "../src/regions.js";

test("each region id is unique", () => {
  const ids = REGIONS.map((region) => region.id);
  assert.equal(new Set(ids).size, ids.length);
});

test("each region has a location label", () => {
  for (const region of REGIONS) {
    assert.ok(region.location.length > 0, region.id);
  }
});

test("the global host is the anycast XML/JSON endpoint", () => {
  assert.equal(hostFor(GLOBAL_ID), "storage.googleapis.com");
});

test("a regional host uses the .rep.googleapis.com form", () => {
  assert.equal(
    hostFor("australia-southeast1"),
    "storage.australia-southeast1.rep.googleapis.com",
  );
});

test("pingUrl puts a unique object name on the missing bucket", () => {
  const url = pingUrl("us-east1", "abc-123");
  assert.equal(
    url,
    `https://storage.us-east1.rep.googleapis.com/${PING_BUCKET}/abc-123`,
  );
});

test("the region list includes us-east1 and australia-southeast1", () => {
  const ids = new Set(REGIONS.map((region) => region.id));
  assert.ok(ids.has("us-east1"));
  assert.ok(ids.has("australia-southeast1"));
  assert.ok(ids.has(GLOBAL_ID));
});
