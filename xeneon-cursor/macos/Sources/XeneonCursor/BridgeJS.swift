enum BridgeJS {
  /// Fallback bridge source when Bridge.js is not found next to the binary.
  static let source = #"""
  (() => {
    const pending = new Map();

    function post(message) {
      if (window.webkit?.messageHandlers?.xeneon) {
        window.webkit.messageHandlers.xeneon.postMessage(message);
        return true;
      }
      return false;
    }

    window.__xeneonBridgeResolve = (payload) => {
      const entry = pending.get(payload.id);
      if (!entry) return;
      pending.delete(payload.id);
      if (payload.ok) entry.resolve(payload.data);
      else {
        const err = new Error(payload.data?.message || payload.data?.error || 'Request failed');
        err.status = payload.status;
        err.data = payload.data;
        entry.reject(err);
      }
    };

    window.XeneonCursor = {
      async request(path, options = {}) {
        const id = `req_${Date.now().toString(36)}_${Math.random().toString(36).slice(2, 8)}`;
        const ok = post({
          type: 'request',
          id,
          path,
          method: options.method || 'GET',
          body: options.body ?? null,
        });
        if (!ok) {
          const res = await fetch(`/api${path}`, {
            method: options.method || 'GET',
            headers: {
              Accept: 'application/json',
              ...(options.body ? { 'Content-Type': 'application/json' } : {}),
            },
            body: options.body ? JSON.stringify(options.body) : undefined,
          });
          const data = await res.json().catch(() => ({}));
          if (!res.ok) {
            throw new Error(data.message || data.error || `HTTP ${res.status}`);
          }
          return data;
        }
        return new Promise((resolve, reject) => {
          pending.set(id, { resolve, reject });
          setTimeout(() => {
            if (pending.has(id)) {
              pending.delete(id);
              reject(new Error('Native bridge timeout'));
            }
          }, 60_000);
        });
      },

      async openExternal(url) {
        const ok = post({ type: 'openExternal', url });
        if (!ok) window.open(url, '_blank', 'noopener,noreferrer');
      },
    };
  })();
  """#
}
