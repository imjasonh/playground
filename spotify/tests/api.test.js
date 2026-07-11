import test from "node:test";
import assert from "node:assert/strict";

import {
  artistLine,
  formatDuration,
  mapTrack,
  playUris,
  searchTracks,
} from "../src/api.js";

test("formatDuration renders m:ss", () => {
  assert.equal(formatDuration(0), "0:00");
  assert.equal(formatDuration(65_000), "1:05");
  assert.equal(formatDuration(3_661_000), "61:01");
});

test("artistLine joins names", () => {
  assert.equal(artistLine([]), "Unknown artist");
  assert.equal(artistLine(["A", "B"]), "A, B");
});

test("mapTrack picks a mid-size image and artist names", () => {
  const mapped = mapTrack({
    id: "1",
    uri: "spotify:track:1",
    name: "Song",
    explicit: true,
    duration_ms: 200000,
    artists: [{ name: "Artist" }, { name: "Feat" }],
    album: {
      name: "Album",
      images: [
        { url: "large.jpg", width: 640 },
        { url: "mid.jpg", width: 300 },
        { url: "tiny.jpg", width: 64 },
      ],
    },
  });

  assert.deepEqual(mapped, {
    id: "1",
    uri: "spotify:track:1",
    name: "Song",
    artists: ["Artist", "Feat"],
    album: "Album",
    imageUrl: "mid.jpg",
    durationMs: 200000,
    explicit: true,
  });
});

test("searchTracks returns [] for blank queries without calling the API", async () => {
  let called = false;
  const fetchImpl = async () => {
    called = true;
    return { ok: true, text: async () => "{}" };
  };
  assert.deepEqual(await searchTracks("tok", "  ", { fetchImpl }), []);
  assert.equal(called, false);
});

test("searchTracks maps track items from the Web API", async () => {
  const fetchImpl = async (url, init) => {
    assert.match(url, /\/search\?/);
    assert.match(url, /type=track/);
    assert.match(url, /q=radiohead/);
    assert.equal(init.headers.Authorization, "Bearer tok");
    return {
      ok: true,
      text: async () =>
        JSON.stringify({
          tracks: {
            items: [
              {
                id: "t1",
                uri: "spotify:track:t1",
                name: "Karma Police",
                duration_ms: 1000,
                artists: [{ name: "Radiohead" }],
                album: { name: "OK Computer", images: [] },
              },
            ],
          },
        }),
    };
  };

  const tracks = await searchTracks("tok", "radiohead", { fetchImpl });
  assert.equal(tracks.length, 1);
  assert.equal(tracks[0].name, "Karma Police");
  assert.equal(tracks[0].uri, "spotify:track:t1");
});

test("playUris PUTs uris to the device player endpoint", async () => {
  const calls = [];
  const fetchImpl = async (url, init) => {
    calls.push({ url, init });
    return { ok: true, status: 204, text: async () => "" };
  };

  await playUris("tok", "device-1", ["spotify:track:abc"], { fetchImpl });
  assert.equal(calls.length, 1);
  assert.match(calls[0].url, /\/me\/player\/play\?device_id=device-1/);
  assert.equal(calls[0].init.method, "PUT");
  assert.deepEqual(JSON.parse(calls[0].init.body), {
    uris: ["spotify:track:abc"],
  });
});

test("playUris rejects when the device is missing", async () => {
  await assert.rejects(
    () => playUris("tok", "", ["spotify:track:abc"]),
    /device is not ready/i,
  );
});
