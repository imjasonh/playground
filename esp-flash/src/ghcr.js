import {
  DEFAULT_OTA_TAG,
  DEFAULT_PROXY_BASE,
  GHCR_NAMESPACE,
  OTA_APPS,
  OTA_CONFIG_MEDIA_TYPE,
  OTA_LAYER_MEDIA_TYPE,
  OTA_SLOT_BYTES,
  OTA_TARGET_CHIP,
} from "./constants.js";

/**
 * GHCR repository path (`owner/name`) for a firmware app.
 *
 * @param {string} app
 */
export function repoPath(app) {
  if (!OTA_APPS.includes(app)) {
    throw new Error(`unknown firmware app ${app}`);
  }
  return `${GHCR_NAMESPACE.replace(/^ghcr\.io\//, "")}/${app}`;
}

/**
 * Full `ghcr.io/…` repo name for a firmware app.
 *
 * @param {string} app
 */
export function defaultOtaRepo(app) {
  return `${GHCR_NAMESPACE}/${app}`;
}

/**
 * cors-proxy query URL for an upstream target.
 *
 * @param {string} proxyBase
 * @param {string} target
 */
export function proxiedUrl(proxyBase, target) {
  const base = String(proxyBase || "").trim().replace(/\/+$/, "");
  if (!base) {
    throw new Error("proxy base URL is empty");
  }
  if (!target) {
    throw new Error("upstream URL is empty");
  }
  return `${base}/?url=${encodeURIComponent(target)}`;
}

export function tokenUrl(app) {
  return `https://ghcr.io/token?service=ghcr.io&scope=repository:${repoPath(app)}:pull`;
}

export function manifestUrl(app, tag = DEFAULT_OTA_TAG) {
  return `https://ghcr.io/v2/${repoPath(app)}/manifests/${tag}`;
}

export function blobUrl(app, digest) {
  if (!digest) {
    throw new Error("blob digest is empty");
  }
  return `https://ghcr.io/v2/${repoPath(app)}/blobs/${digest}`;
}

/**
 * Pick the single firmware layer from an OCI image manifest.
 *
 * @param {{ layers?: { mediaType?: string, digest?: string, size?: number }[] }} manifest
 */
export function pickFirmwareLayer(manifest) {
  const layers = manifest?.layers;
  if (!Array.isArray(layers) || layers.length !== 1) {
    throw new Error(
      `firmware manifest has ${Array.isArray(layers) ? layers.length : 0} layers, expected exactly 1`,
    );
  }
  const layer = layers[0];
  if (layer.mediaType !== OTA_LAYER_MEDIA_TYPE) {
    throw new Error(`unexpected layer mediaType: ${layer.mediaType}`);
  }
  if (!layer.digest) {
    throw new Error("firmware layer is missing a digest");
  }
  const size = Number(layer.size) || 0;
  if (size === 0 || size > OTA_SLOT_BYTES) {
    throw new Error(
      `firmware layer size ${size} does not fit OTA slot (${OTA_SLOT_BYTES} bytes)`,
    );
  }
  return layer;
}

/**
 * Check that a signed config blob is the requested app and fits one OTA slot.
 *
 * @param {{ target_chip?: string, app?: string, bin_size?: number }} cfg
 * @param {number} layerSize
 * @param {string} expectedApp
 */
export function checkFirmwareConfig(cfg, layerSize, expectedApp) {
  if (!OTA_APPS.includes(expectedApp)) {
    throw new Error(`unknown expected app ${expectedApp}`);
  }
  if (cfg.target_chip !== OTA_TARGET_CHIP) {
    throw new Error(
      `firmware config target_chip=${cfg.target_chip} (want ${OTA_TARGET_CHIP})`,
    );
  }
  if (cfg.app !== expectedApp) {
    throw new Error(`firmware config app=${cfg.app} (want ${expectedApp})`);
  }
  if (layerSize === 0 || layerSize > OTA_SLOT_BYTES) {
    throw new Error(
      `firmware layer size ${layerSize} does not fit OTA slot (${OTA_SLOT_BYTES} bytes)`,
    );
  }
  if (cfg.bin_size != null && Number(cfg.bin_size) !== layerSize) {
    throw new Error(
      `firmware config bin_size=${cfg.bin_size} does not match layer size ${layerSize}`,
    );
  }
}

/**
 * Pull `:tag` of `app` from GHCR through cors-proxy.
 *
 * This path does not verify Cosign. USB flash is a trusted-computer operation;
 * the device still verifies signatures on its own OTA pulls.
 *
 * @param {{
 *   app: string,
 *   tag?: string,
 *   proxyBase?: string,
 *   fetchImpl?: typeof fetch,
 * }} opts
 * @returns {Promise<{ bytes: Uint8Array, digest: string, size: number, config: object }>}
 */
export async function fetchFirmware(opts) {
  const app = opts.app;
  const tag = opts.tag || DEFAULT_OTA_TAG;
  const proxyBase = opts.proxyBase || DEFAULT_PROXY_BASE;
  const fetchImpl = opts.fetchImpl || globalThis.fetch;
  if (typeof fetchImpl !== "function") {
    throw new Error("fetch is not available");
  }

  const token = await fetchAnonToken(fetchImpl, proxyBase, app);
  const manifest = await fetchJson(fetchImpl, proxiedUrl(proxyBase, manifestUrl(app, tag)), {
    headers: {
      Authorization: `Bearer ${token}`,
      Accept: "application/vnd.oci.image.manifest.v1+json",
    },
  });
  const layer = pickFirmwareLayer(manifest);

  if (manifest.config?.mediaType && manifest.config.mediaType !== OTA_CONFIG_MEDIA_TYPE) {
    throw new Error(`unexpected config mediaType: ${manifest.config.mediaType}`);
  }
  let config = { target_chip: OTA_TARGET_CHIP, app, bin_size: layer.size };
  if (manifest.config?.digest) {
    config = await fetchJson(
      fetchImpl,
      proxiedUrl(proxyBase, blobUrl(app, manifest.config.digest)),
      {
        headers: {
          Authorization: `Bearer ${token}`,
          Accept: "application/json",
        },
      },
    );
    checkFirmwareConfig(config, layer.size, app);
  }

  const bytes = await fetchBytes(fetchImpl, proxiedUrl(proxyBase, blobUrl(app, layer.digest)), {
    headers: {
      Authorization: `Bearer ${token}`,
      Accept: OTA_LAYER_MEDIA_TYPE,
    },
  });
  if (bytes.length !== layer.size) {
    throw new Error(
      `firmware blob is ${bytes.length} bytes, manifest says ${layer.size}`,
    );
  }

  return {
    bytes,
    digest: layer.digest,
    size: bytes.length,
    config,
  };
}

async function fetchAnonToken(fetchImpl, proxyBase, app) {
  const data = await fetchJson(fetchImpl, proxiedUrl(proxyBase, tokenUrl(app)));
  const token = data.token || data.access_token;
  if (!token) {
    throw new Error("GHCR token response had no token");
  }
  return token;
}

async function fetchJson(fetchImpl, url, init) {
  const res = await fetchOk(fetchImpl, url, init);
  const text = await res.text();
  try {
    return JSON.parse(text);
  } catch {
    throw new Error(`expected JSON from ${describeUrl(url)}, got ${text.slice(0, 120)}`);
  }
}

async function fetchBytes(fetchImpl, url, init) {
  const res = await fetchOk(fetchImpl, url, init);
  const buf = await res.arrayBuffer();
  return new Uint8Array(buf);
}

async function fetchOk(fetchImpl, url, init = {}) {
  const res = await fetchImpl(url, { ...init, cache: "no-store" });
  if (!res.ok) {
    const body = await res.text().catch(() => "");
    throw new Error(
      `${res.status} fetching ${describeUrl(url)}${body ? `: ${body.slice(0, 180)}` : ""}`,
    );
  }
  return res;
}

function describeUrl(url) {
  try {
    const parsed = new URL(url);
    const target = parsed.searchParams.get("url");
    return target || parsed.pathname;
  } catch {
    return url;
  }
}
