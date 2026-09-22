import { bundleUrls, CACHE_NAME } from "./models.js";

export function memoryCache() {
  const map = new Map();
  return {
    async match(url) {
      return map.get(url) ?? null;
    },
    async put(url, buffer) {
      map.set(url, buffer);
    },
    async delete(url) {
      map.delete(url);
    },
  };
}

export async function openCache(cachesApi = globalThis.caches) {
  if (!cachesApi?.open) {
    return memoryCache();
  }
  const cache = await cachesApi.open(CACHE_NAME);
  return {
    async match(url) {
      const response = await cache.match(url);
      if (!response) {
        return null;
      }
      return response.arrayBuffer();
    },
    async put(url, buffer) {
      await cache.put(url, new Response(buffer.slice(0)));
    },
    async delete(url) {
      await cache.delete(url);
    },
  };
}

export async function fetchFile(url, { cache, fetchImpl = fetch, onProgress } = {}) {
  if (cache) {
    const hit = await cache.match(url);
    if (hit) {
      onProgress?.({ url, received: hit.byteLength, total: hit.byteLength, cached: true });
      return hit;
    }
  }
  const response = await fetchImpl(url, { redirect: "follow" });
  if (!response.ok) {
    throw new Error(`failed to download ${url}: ${response.status} ${response.statusText}`);
  }
  const total = Number(response.headers.get("content-length"));
  const known = Number.isFinite(total) && total > 0 ? total : null;
  if (!response.body || !response.body.getReader) {
    const buffer = await response.arrayBuffer();
    if (cache) {
      await cache.put(url, buffer);
    }
    onProgress?.({ url, received: buffer.byteLength, total: buffer.byteLength, cached: false });
    return buffer;
  }
  const reader = response.body.getReader();
  const chunks = [];
  let received = 0;
  let more = true;
  while (more) {
    const { done, value } = await reader.read();
    more = !done;
    if (done) {
      break;
    }
    chunks.push(value);
    received += value.byteLength;
    onProgress?.({ url, received, total: known, cached: false });
  }
  const buffer = concat(chunks, received);
  if (cache) {
    await cache.put(url, buffer);
  }
  return buffer;
}

export function concat(chunks, length) {
  const out = new Uint8Array(length);
  let offset = 0;
  for (const chunk of chunks) {
    out.set(chunk, offset);
    offset += chunk.byteLength;
  }
  return out.buffer;
}

export async function fetchBundle(model, options = {}) {
  const files = {};
  const urls = bundleUrls(model);
  if (urls.length === 0) {
    throw new Error(`${model.title} has no files to fetch.`);
  }
  for (const { file, url } of urls) {
    files[file] = await fetchFile(url, {
      cache: options.cache,
      fetchImpl: options.fetchImpl,
      onProgress: (info) => options.onProgress?.({ file, ...info }),
    });
  }
  return files;
}

export function textFromBuffer(buffer) {
  return new TextDecoder().decode(buffer);
}

export function jsonFromBuffer(buffer) {
  return JSON.parse(textFromBuffer(buffer));
}
