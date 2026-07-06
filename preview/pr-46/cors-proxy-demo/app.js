/*
 * CORS proxy demo front-end.
 *
 * Drives the Rust Cloudflare Worker in ../cors-proxy:
 *   1. point it at your deployed proxy URL,
 *   2. build a request to any public API,
 *   3. send it through the proxy and inspect the CORS-enabled response.
 *
 * Everything is a cross-origin fetch to the proxy, which adds the
 * Access-Control-* headers that let this static page read the result.
 */

(() => {
  "use strict";

  const STORAGE_KEY = "cors-proxy-demo.proxyBase";
  const MAX_BODY_CHARS = 20000;

  const el = {};

  /* ----------------------------- utilities ------------------------------ */

  function $(id) {
    return document.getElementById(id);
  }

  function log(message, level = "info") {
    const line = document.createElement("div");
    line.className = `log-line log-${level}`;
    const time = new Date().toLocaleTimeString();
    line.textContent = `[${time}] ${message}`;
    el.log.appendChild(line);
    el.log.scrollTop = el.log.scrollHeight;
  }

  function setBadge(node, text, state) {
    node.textContent = text;
    node.dataset.state = state; // "ok" | "warn" | "bad" | "unknown"
  }

  function methodHasBody(method) {
    return !["GET", "HEAD"].includes(method);
  }

  /* --------------------------- proxy base config ------------------------- */

  function getProxyBase() {
    return (el.proxyBase.value || "").trim().replace(/\/+$/, "");
  }

  function saveProxyBase() {
    const value = getProxyBase();
    try {
      if (value) localStorage.setItem(STORAGE_KEY, value);
      else localStorage.removeItem(STORAGE_KEY);
    } catch (_e) {
      /* storage may be blocked; the in-memory value still works */
    }
  }

  function buildProxiedUrl() {
    const base = getProxyBase();
    const target = (el.targetUrl.value || "").trim();
    if (!base || !target) return "";
    if (el.style.value === "path") {
      return `${base}/${target}`;
    }
    return `${base}/?url=${encodeURIComponent(target)}`;
  }

  function updateProxiedPreview() {
    const url = buildProxiedUrl();
    el.proxiedUrl.textContent = url || "—";
  }

  /* ------------------------------ headers -------------------------------- */

  // Parse a "Name: value" per line block into an array of [name, value].
  function parseHeaders(text) {
    const out = [];
    for (const raw of (text || "").split("\n")) {
      const line = raw.trim();
      if (!line) continue;
      const idx = line.indexOf(":");
      if (idx <= 0) {
        log(`Ignoring malformed header line: ${line}`, "warn");
        continue;
      }
      out.push([line.slice(0, idx).trim(), line.slice(idx + 1).trim()]);
    }
    return out;
  }

  function formatResponseHeaders(headers) {
    const lines = [];
    headers.forEach((value, name) => lines.push(`${name}: ${value}`));
    lines.sort();
    return lines.join("\n") || "(no readable headers)";
  }

  /* ------------------------------ actions -------------------------------- */

  async function checkProxy() {
    const base = getProxyBase();
    if (!base) {
      log("Set your proxy base URL first.", "warn");
      return;
    }
    try {
      log(`Checking ${base}/ …`);
      const res = await fetch(`${base}/`);
      const data = await res.json().catch(() => null);
      if (res.ok && data && data.service === "cors-proxy") {
        setBadge(el.proxyState, "reachable", "ok");
        log("Proxy is reachable.", "success");
        if (data.limits) {
          el.limits.textContent = JSON.stringify(data.limits);
          el.limitsRow.hidden = false;
        }
      } else {
        setBadge(el.proxyState, `unexpected ${res.status}`, "warn");
        log("Reached the URL, but it didn't look like a cors-proxy.", "warn");
      }
    } catch (err) {
      setBadge(el.proxyState, "unreachable", "bad");
      log(`Could not reach the proxy: ${err.message}`, "error");
    }
  }

  async function sendRequest() {
    const proxied = buildProxiedUrl();
    if (!proxied) {
      log("Set both a proxy base URL and a target URL.", "warn");
      return;
    }
    const method = el.method.value;
    const options = { method, headers: parseHeaders(el.reqHeaders.value) };
    if (methodHasBody(method) && el.reqBody.value) {
      options.body = el.reqBody.value;
    }

    el.sendBtn.disabled = true;
    el.respDetails.hidden = true;
    el.respEmpty.hidden = false;
    setBadge(el.respStatus, "…", "unknown");
    el.respTime.textContent = "";

    const started = performance.now();
    try {
      log(`${method} via proxy → ${el.targetUrl.value.trim()}`);
      const res = await fetch(proxied, options);
      const elapsed = Math.round(performance.now() - started);
      const text = await res.text();

      const state = res.ok ? "ok" : res.status >= 500 ? "bad" : "warn";
      setBadge(el.respStatus, `${res.status} ${res.statusText}`.trim(), state);
      el.respTime.textContent = `${elapsed} ms`;
      el.respHeaders.textContent = formatResponseHeaders(res.headers);

      const size = new Blob([text]).size;
      el.respSize.textContent = `(${size.toLocaleString()} bytes)`;
      el.respBody.textContent =
        text.length > MAX_BODY_CHARS
          ? `${text.slice(0, MAX_BODY_CHARS)}\n… (truncated, ${text.length.toLocaleString()} chars total)`
          : text || "(empty body)";

      el.respEmpty.hidden = true;
      el.respDetails.hidden = false;
      log(`Response ${res.status} in ${elapsed} ms (${size.toLocaleString()} bytes).`, res.ok ? "success" : "warn");
    } catch (err) {
      setBadge(el.respStatus, "failed", "bad");
      log(`Request failed: ${err.message}. Is the proxy URL correct and reachable over HTTPS?`, "error");
    } finally {
      el.sendBtn.disabled = false;
    }
  }

  function refreshBodyVisibility() {
    el.bodyField.hidden = !methodHasBody(el.method.value);
  }

  /* ------------------------------- wiring -------------------------------- */

  function cacheElements() {
    [
      "proxy-base", "check-btn", "proxy-state", "limits-row", "limits",
      "target-url", "method", "style", "req-headers", "headers-field",
      "req-body", "body-field", "proxied-url", "send-btn",
      "resp-status", "resp-time", "resp-details", "resp-headers",
      "resp-size", "resp-body", "resp-empty",
      "log", "clear-log-btn",
    ].forEach((id) => {
      const camel = id.replace(/-([a-z])/g, (_m, c) => c.toUpperCase());
      el[camel] = $(id);
    });
  }

  function init() {
    cacheElements();

    const params = new URLSearchParams(window.location.search);
    const fromQuery = params.get("proxy");
    let stored = null;
    try {
      stored = localStorage.getItem(STORAGE_KEY);
    } catch (_e) {
      /* ignore */
    }
    el.proxyBase.value = (fromQuery || stored || "").trim();
    if (fromQuery) saveProxyBase();

    refreshBodyVisibility();
    updateProxiedPreview();

    el.checkBtn.addEventListener("click", () => {
      saveProxyBase();
      checkProxy();
    });
    el.proxyBase.addEventListener("change", () => {
      saveProxyBase();
      updateProxiedPreview();
    });
    el.proxyBase.addEventListener("input", updateProxiedPreview);
    el.targetUrl.addEventListener("input", updateProxiedPreview);
    el.style.addEventListener("change", updateProxiedPreview);
    el.method.addEventListener("change", refreshBodyVisibility);
    el.sendBtn.addEventListener("click", () => {
      saveProxyBase();
      sendRequest();
    });
    el.clearLogBtn.addEventListener("click", () => {
      el.log.textContent = "";
    });

    document.querySelectorAll(".chip").forEach((chip) => {
      chip.addEventListener("click", () => {
        el.targetUrl.value = chip.dataset.url;
        updateProxiedPreview();
      });
    });

    log("Ready. Set your proxy URL, then Send a request.");
    if (getProxyBase()) checkProxy();
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();
