import {
  DEFAULT_PROXY_BASE,
  OTA_APP_INKBOT,
  OTA_APP_MAZE,
  OTA_CONFIG_MEDIA_TYPE,
  OTA_LAYER_MEDIA_TYPE,
  OTA_SLOT_BYTES,
} from "../src/constants.js";
import {
  blobUrl,
  checkFirmwareConfig,
  fetchFirmware,
  manifestUrl,
  pickFirmwareLayer,
  proxiedUrl,
  repoPath,
  tokenUrl,
} from "../src/ghcr.js";
import test from "node:test";
import assert from "node:assert/strict";

test("repo helpers name the public GHCR packages", () => {
  assert.equal(repoPath(OTA_APP_INKBOT), "imjasonh/playground/inkbot-esp32");
  assert.equal(
    tokenUrl(OTA_APP_INKBOT),
    "https://ghcr.io/token?service=ghcr.io&scope=repository:imjasonh/playground/inkbot-esp32:pull",
  );
  assert.equal(
    manifestUrl(OTA_APP_INKBOT, "latest"),
    "https://ghcr.io/v2/imjasonh/playground/inkbot-esp32/manifests/latest",
  );
  assert.equal(
    blobUrl(OTA_APP_MAZE, "sha256:abc"),
    "https://ghcr.io/v2/imjasonh/playground/maze-esp32/blobs/sha256:abc",
  );
  assert.throws(() => repoPath("not-an-app"), /unknown firmware app/);
});

test("proxiedUrl uses the cors-proxy query form", () => {
  assert.equal(
    proxiedUrl(`${DEFAULT_PROXY_BASE}/`, "https://ghcr.io/token"),
    `${DEFAULT_PROXY_BASE}/?url=${encodeURIComponent("https://ghcr.io/token")}`,
  );
  assert.throws(() => proxiedUrl("", "https://example.com"), /proxy base/);
});

test("pickFirmwareLayer requires one firmware.bin layer", () => {
  const layer = {
    mediaType: OTA_LAYER_MEDIA_TYPE,
    digest: "sha256:aa",
    size: 100,
  };
  assert.deepEqual(pickFirmwareLayer({ layers: [layer] }), layer);
  assert.throws(() => pickFirmwareLayer({ layers: [] }), /expected exactly 1/);
  assert.throws(
    () => pickFirmwareLayer({ layers: [{ ...layer, mediaType: "application/octet-stream" }] }),
    /mediaType/,
  );
  assert.throws(
    () => pickFirmwareLayer({ layers: [{ ...layer, size: OTA_SLOT_BYTES + 1 }] }),
    /OTA slot/,
  );
});

test("checkFirmwareConfig mirrors the device OTA checks", () => {
  const cfg = { target_chip: "esp32", app: OTA_APP_INKBOT, bin_size: 100 };
  checkFirmwareConfig(cfg, 100, OTA_APP_INKBOT);
  assert.throws(() => checkFirmwareConfig(cfg, 100, OTA_APP_MAZE), /want maze-esp32/);
  assert.throws(
    () => checkFirmwareConfig({ ...cfg, target_chip: "esp32s3" }, 100, OTA_APP_INKBOT),
    /target_chip/,
  );
});

test("fetchFirmware pulls token, manifest, config, and blob through the proxy", async () => {
  const firmware = new Uint8Array([0xe9, 1, 2, 3]);
  const calls = [];
  const fetchImpl = async (url, init = {}) => {
    calls.push({ url, headers: init.headers || {}, cache: init.cache });
    const target = new URL(url).searchParams.get("url");
    if (target.includes("/token?")) {
      return json({ token: "anon" });
    }
    if (target.includes("/manifests/latest")) {
      return json({
        config: { mediaType: OTA_CONFIG_MEDIA_TYPE, digest: "sha256:cfg" },
        layers: [
          { mediaType: OTA_LAYER_MEDIA_TYPE, digest: "sha256:fw", size: firmware.length },
        ],
      });
    }
    if (target.endsWith("/blobs/sha256:cfg")) {
      return json({ target_chip: "esp32", app: OTA_APP_INKBOT, bin_size: firmware.length });
    }
    if (target.endsWith("/blobs/sha256:fw")) {
      return bytes(firmware);
    }
    throw new Error(`unexpected ${target}`);
  };

  const result = await fetchFirmware({
    app: OTA_APP_INKBOT,
    proxyBase: DEFAULT_PROXY_BASE,
    fetchImpl,
  });
  assert.equal(result.digest, "sha256:fw");
  assert.equal(result.size, 4);
  assert.deepEqual([...result.bytes], [0xe9, 1, 2, 3]);
  assert.equal(result.config.app, OTA_APP_INKBOT);
  assert.equal(new URL(calls[0].url).searchParams.get("url").includes("ghcr.io/token"), true);
  assert.equal(calls[1].headers.Authorization, "Bearer anon");
  assert.equal(calls[0].cache, "no-store");
  assert.equal(calls[1].cache, "no-store");
});

function json(obj) {
  return {
    ok: true,
    status: 200,
    text: async () => JSON.stringify(obj),
    arrayBuffer: async () => new TextEncoder().encode(JSON.stringify(obj)).buffer,
  };
}

function bytes(u8) {
  return {
    ok: true,
    status: 200,
    text: async () => "",
    arrayBuffer: async () => u8.buffer,
  };
}
