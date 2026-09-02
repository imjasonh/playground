/*
 * Web Push demo front-end.
 *
 * Drives the Rust Cloudflare Worker in ../web-push end to end:
 *   1. point it at your deployed Worker URL,
 *   2. grant notification permission,
 *   3. subscribe (registers the service worker + POSTs the PushSubscription),
 *   4. send a test notification via POST /notify and watch it arrive.
 *
 * Everything talks to the Worker over cross-origin fetch; the Worker sends
 * permissive CORS headers so this static page can live on GitHub Pages.
 */

(() => {
  "use strict";

  const STORAGE_KEY = "web-push-demo.apiBase";
  const SW_URL = "sw.js";

  const el = {};
  let activeRegistration = null;

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

  function logObject(label, obj, level = "info") {
    log(`${label} ${JSON.stringify(obj)}`, level);
  }

  function setBadge(node, text, state) {
    node.textContent = text;
    node.dataset.state = state; // "ok" | "warn" | "bad" | "unknown"
  }

  // base64url (unpadded) -> Uint8Array. Browsers want a BufferSource for
  // applicationServerKey; passing the raw string is not universally supported.
  function urlBase64ToUint8Array(base64String) {
    const padding = "=".repeat((4 - (base64String.length % 4)) % 4);
    const base64 = (base64String + padding).replace(/-/g, "+").replace(/_/g, "/");
    const raw = atob(base64);
    const output = new Uint8Array(raw.length);
    for (let i = 0; i < raw.length; i += 1) {
      output[i] = raw.charCodeAt(i);
    }
    return output;
  }

  function bytesToBase64Url(bytes) {
    let binary = "";
    for (let i = 0; i < bytes.length; i += 1) {
      binary += String.fromCharCode(bytes[i]);
    }
    return btoa(binary).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
  }

  // Mirrors the Worker's id_for_endpoint: base64url(SHA-256(endpoint)).
  // Lets us target "this device only" without depending on a stored response.
  async function idForEndpoint(endpoint) {
    const data = new TextEncoder().encode(endpoint);
    const digest = await crypto.subtle.digest("SHA-256", data);
    return bytesToBase64Url(new Uint8Array(digest));
  }

  function buffersEqual(a, b) {
    const x = new Uint8Array(a);
    const y = new Uint8Array(b);
    if (x.length !== y.length) return false;
    for (let i = 0; i < x.length; i += 1) {
      if (x[i] !== y[i]) return false;
    }
    return true;
  }

  /* --------------------------- API base config --------------------------- */

  function getApiBase() {
    return (el.apiBase.value || "").trim().replace(/\/+$/, "");
  }

  function saveApiBase() {
    const value = getApiBase();
    try {
      if (value) {
        localStorage.setItem(STORAGE_KEY, value);
      } else {
        localStorage.removeItem(STORAGE_KEY);
      }
    } catch (_e) {
      /* storage may be blocked; the in-memory value still works */
    }
  }

  function apiUrl(path) {
    const base = getApiBase();
    if (!base) {
      throw new Error("Set your Worker API base URL first (e.g. https://web-push-worker.example.workers.dev).");
    }
    return base + path;
  }

  // Surface the two URL mistakes that otherwise fail with an opaque
  // "Failed to fetch": a missing scheme, or an http:// Worker called from this
  // https:// page (blocked as mixed content).
  function warnAboutBase() {
    const base = getApiBase();
    if (!base) return;
    if (!/^https?:\/\//i.test(base)) {
      log("Worker URL should start with https:// (or http:// for localhost).", "warn");
      return;
    }
    try {
      const target = new URL(base);
      const localish = /^(localhost|127\.0\.0\.1|\[?::1\]?)$/.test(target.hostname);
      if (window.location.protocol === "https:" && target.protocol === "http:" && !localish) {
        log("This page is HTTPS but the Worker URL is HTTP — the browser will block it (mixed content). Use the https:// URL.", "warn");
      }
    } catch (_e) {
      /* an unparseable URL will be surfaced by the fetch failure */
    }
  }

  async function apiFetch(path, options) {
    const url = apiUrl(path);
    warnAboutBase();
    const res = await fetch(url, options);
    const text = await res.text();
    let data = text;
    try {
      data = text ? JSON.parse(text) : null;
    } catch (_e) {
      /* leave as text */
    }
    return { ok: res.ok, status: res.status, data };
  }

  /* --------------------------- feature support --------------------------- */

  const support = {
    secure: () => window.isSecureContext,
    serviceWorker: () => "serviceWorker" in navigator,
    pushManager: () => "PushManager" in window,
    notification: () => "Notification" in window,
  };

  function refreshSupport() {
    const rows = [
      ["support-secure", support.secure(), "Secure context (HTTPS)"],
      ["support-sw", support.serviceWorker(), "Service workers"],
      ["support-push", support.pushManager(), "Push API"],
      ["support-notification", support.notification(), "Notifications"],
    ];
    let allOk = true;
    for (const [id, ok] of rows) {
      const node = $(id);
      if (node) {
        setBadge(node.querySelector(".badge"), ok ? "yes" : "no", ok ? "ok" : "bad");
      }
      allOk = allOk && ok;
    }
    return allOk;
  }

  function pushSupported() {
    return support.secure() && support.serviceWorker() && support.pushManager() && support.notification();
  }

  /* --------------------------- service worker ---------------------------- */

  async function ensureServiceWorker() {
    if (!activeRegistration) {
      activeRegistration = await navigator.serviceWorker.register(SW_URL);
    }
    // Always wait for an active worker before subscribing — on a return visit
    // the cached registration may not be active yet.
    await navigator.serviceWorker.ready;
    return activeRegistration;
  }

  function postConfigToWorker(vapidPublicKey) {
    const sw = navigator.serviceWorker.controller || (activeRegistration && activeRegistration.active);
    if (sw) {
      sw.postMessage({ type: "config", apiBase: getApiBase(), vapidPublicKey });
    }
  }

  function onServiceWorkerMessage(event) {
    const data = event.data || {};
    if (data.type === "push") {
      logObject("Push received by service worker:", data.payload, "success");
    } else if (data.type === "resubscribed") {
      log("Service worker re-subscribed after a key rotation.", "success");
    } else if (data.type === "error") {
      log(data.message, "error");
    }
  }

  /* ----------------------------- permission ------------------------------ */

  function refreshPermission() {
    if (!support.notification()) {
      setBadge(el.permState, "unsupported", "bad");
      return "unsupported";
    }
    const state = Notification.permission;
    const map = { granted: "ok", denied: "bad", default: "warn" };
    setBadge(el.permState, state, map[state] || "unknown");
    return state;
  }

  async function requestPermission() {
    if (!support.notification()) {
      log("Notifications are not supported in this browser.", "error");
      return;
    }
    log("Requesting notification permission…");
    const result = await Notification.requestPermission();
    refreshPermission();
    if (result === "granted") {
      log("Notification permission granted.", "success");
    } else {
      log(`Notification permission: ${result}. You must allow notifications to receive pushes.`, "warn");
    }
  }

  /* -------------------------- subscription state ------------------------- */

  async function currentSubscription() {
    if (!support.serviceWorker()) return null;
    const reg = await navigator.serviceWorker.getRegistration();
    if (!reg) return null;
    return reg.pushManager.getSubscription();
  }

  async function refreshSubscriptionState() {
    const sub = await currentSubscription();
    if (!sub) {
      setBadge(el.subState, "not subscribed", "warn");
      el.subDetails.hidden = true;
      el.unsubscribeBtn.disabled = true;
      return null;
    }
    const id = await idForEndpoint(sub.endpoint);
    setBadge(el.subState, "subscribed", "ok");
    el.subDetails.hidden = false;
    el.subId.textContent = id;
    el.subEndpoint.textContent = sub.endpoint;
    el.unsubscribeBtn.disabled = false;
    return sub;
  }

  /* ------------------------------- actions ------------------------------- */

  async function checkServer() {
    try {
      log(`Checking ${apiUrl("/health")} …`);
      const health = await apiFetch("/health");
      if (!health.ok) {
        setBadge(el.serverState, `error ${health.status}`, "bad");
        logObject("Health check failed:", health.data, "error");
        return;
      }
      setBadge(el.serverState, "reachable", "ok");
      logObject("Worker is reachable:", health.data, "success");
      if (health.data && health.data.vapidPublicKey) {
        el.vapidKey.textContent = health.data.vapidPublicKey;
        el.vapidRow.hidden = false;
      }
    } catch (err) {
      setBadge(el.serverState, "unreachable", "bad");
      log(`Could not reach the Worker: ${err.message}`, "error");
    }
  }

  async function subscribe() {
    if (!pushSupported()) {
      log("This browser is missing the APIs needed for Web Push (see Browser support).", "error");
      return;
    }
    try {
      el.subscribeBtn.disabled = true;
      log("Registering service worker…");
      const reg = await ensureServiceWorker();

      const permission = await Notification.requestPermission();
      refreshPermission();
      if (permission !== "granted") {
        const hint =
          permission === "denied"
            ? " Reset it in your browser's site settings to try again."
            : "";
        log(`Cannot subscribe: notification permission is "${permission}".${hint}`, "error");
        return;
      }

      log("Fetching VAPID public key from the Worker…");
      const keyRes = await apiFetch("/vapidPublicKey");
      if (!keyRes.ok || !keyRes.data || !keyRes.data.publicKey) {
        logObject("Could not get VAPID public key:", keyRes.data, "error");
        return;
      }
      const publicKey = keyRes.data.publicKey;
      el.vapidKey.textContent = publicKey;
      el.vapidRow.hidden = false;
      const applicationServerKey = urlBase64ToUint8Array(publicKey);

      let sub = await reg.pushManager.getSubscription();
      if (sub) {
        // If the existing subscription used a different VAPID key (e.g. you
        // switched Workers), drop it so we can subscribe with the new one.
        const existingKey = sub.options && sub.options.applicationServerKey;
        if (existingKey && !buffersEqual(existingKey, applicationServerKey)) {
          log("Existing subscription used a different VAPID key; replacing it.", "warn");
          await sub.unsubscribe();
          sub = null;
        }
      }
      if (!sub) {
        log("Subscribing with the push service…");
        sub = await reg.pushManager.subscribe({ userVisibleOnly: true, applicationServerKey });
      }

      log("Registering the subscription with the Worker…");
      const res = await apiFetch("/subscribe", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(sub),
      });
      if (res.ok) {
        logObject("Subscribed:", res.data, "success");
        postConfigToWorker(publicKey);
      } else {
        logObject("Worker rejected the subscription:", res.data, "error");
      }
      await refreshSubscriptionState();
    } catch (err) {
      log(`Subscribe failed: ${err.message}`, "error");
    } finally {
      el.subscribeBtn.disabled = false;
    }
  }

  async function unsubscribe() {
    try {
      el.unsubscribeBtn.disabled = true;
      const sub = await currentSubscription();
      if (!sub) {
        log("No active subscription on this device.", "warn");
        return;
      }
      const endpoint = sub.endpoint;
      log("Unsubscribing from the push service…");
      const removed = await sub.unsubscribe();
      log(removed ? "Removed local subscription." : "Local unsubscribe returned false.", removed ? "info" : "warn");

      try {
        const res = await apiFetch("/unsubscribe", {
          method: "POST",
          headers: { "Content-Type": "application/json" },
          body: JSON.stringify({ endpoint }),
        });
        logObject("Worker unsubscribe:", res.data, res.ok ? "success" : "error");
      } catch (err) {
        log(`Could not tell the Worker (it will prune on next push): ${err.message}`, "warn");
      }
    } catch (err) {
      log(`Unsubscribe failed: ${err.message}`, "error");
    } finally {
      // Re-sync the UI regardless of which branch above ran.
      await refreshSubscriptionState();
    }
  }

  async function sendNotification() {
    try {
      el.notifyBtn.disabled = true;
      const payload = {
        title: el.notifyTitle.value || "Hello from Web Push",
        body: el.notifyBody.value || "It works end to end!",
        url: window.location.href,
        icon: new URL("./icon.svg", window.location.href).href,
      };
      const request = { payload };

      const ttl = parseInt(el.notifyTtl.value, 10);
      if (!Number.isNaN(ttl) && ttl >= 0) request.ttl = ttl;
      if (el.notifyUrgency.value) request.urgency = el.notifyUrgency.value;
      if (el.notifyTopic.value.trim()) request.topic = el.notifyTopic.value.trim();

      if (el.onlyThisDevice.checked) {
        const sub = await currentSubscription();
        if (!sub) {
          log("You're not subscribed on this device. Subscribe first, or uncheck \"only this device\".", "warn");
          return;
        }
        request.id = await idForEndpoint(sub.endpoint);
      }

      log(`Sending /notify (${el.onlyThisDevice.checked ? "this device" : "broadcast"})…`);
      const res = await apiFetch("/notify", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(request),
      });
      logObject("Notify result:", res.data, res.ok ? "success" : "error");
    } catch (err) {
      log(`Notify failed: ${err.message}`, "error");
    } finally {
      el.notifyBtn.disabled = false;
    }
  }

  /* ------------------------------- wiring -------------------------------- */

  function cacheElements() {
    [
      "api-base", "check-btn", "server-state", "vapid-row", "vapid-key",
      "permission-btn", "perm-state",
      "subscribe-btn", "unsubscribe-btn", "sub-state", "sub-details", "sub-id", "sub-endpoint",
      "notify-title", "notify-body", "notify-ttl", "notify-urgency", "notify-topic",
      "only-this-device", "notify-btn",
      "log", "clear-log-btn",
    ].forEach((id) => {
      const camel = id.replace(/-([a-z])/g, (_m, c) => c.toUpperCase());
      el[camel] = $(id);
    });
  }

  function init() {
    cacheElements();

    // Prefill API base from ?api= query param, then localStorage.
    const params = new URLSearchParams(window.location.search);
    const fromQuery = params.get("api");
    let stored = null;
    try {
      stored = localStorage.getItem(STORAGE_KEY);
    } catch (_e) {
      /* ignore */
    }
    el.apiBase.value = (fromQuery || stored || "").trim();
    // Persist a URL passed via ?api= so it survives a reload without the param.
    if (fromQuery) saveApiBase();

    const ok = refreshSupport();
    refreshPermission();

    if (!ok) {
      log("Your browser can't run this demo. iOS Safari requires installing the page to the Home Screen first.", "warn");
    } else {
      log("Ready. Set your Worker URL, then Subscribe.");
    }

    el.checkBtn.addEventListener("click", () => {
      saveApiBase();
      checkServer();
    });
    el.apiBase.addEventListener("change", saveApiBase);
    el.permissionBtn.addEventListener("click", requestPermission);
    el.subscribeBtn.addEventListener("click", () => {
      saveApiBase();
      subscribe();
    });
    el.unsubscribeBtn.addEventListener("click", unsubscribe);
    el.notifyBtn.addEventListener("click", () => {
      saveApiBase();
      sendNotification();
    });
    el.clearLogBtn.addEventListener("click", () => {
      el.log.textContent = "";
    });

    if (support.serviceWorker()) {
      navigator.serviceWorker.addEventListener("message", onServiceWorkerMessage);
      // Register early so we can receive pushes without an explicit subscribe.
      navigator.serviceWorker
        .getRegistration()
        .then((reg) => {
          if (reg) activeRegistration = reg;
          return refreshSubscriptionState();
        })
        .catch(() => {});
    }

    // Auto-check the server if we already have a URL configured.
    if (getApiBase()) {
      checkServer();
    }
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();
