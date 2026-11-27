// WebSocket multiplayer client for the rails-server Cloudflare Worker.

export class RoomClient {
  constructor(serverUrl, callbacks) {
    this.serverUrl = serverUrl.replace(/\/+$/, "");
    this.cb = callbacks;
    this.ws = null;
    this.code = null;
    this.slot = null;
    this.token = null;
    this.pingTimer = null;
    this.closedIntentionally = false;
    this.lastDraftSentAt = 0;
  }

  async createRoom() {
    const res = await fetch(`${this.serverUrl}/api/rooms`, { method: "POST" });
    if (!res.ok) {
      throw new Error(`Failed to create room (HTTP ${res.status})`);
    }
    const data = await res.json();
    return data.code;
  }

  connect(code, name, color = null) {
    this.closedIntentionally = false;
    this.code = code.toUpperCase();
    const savedToken = localStorage.getItem(`rails_token_${this.code}`) || null;
    const wsBase = this.serverUrl.replace(/^http/, "ws");
    const url = `${wsBase}/api/rooms/${this.code}/ws`;

    this.ws = new WebSocket(url);
    this.ws.addEventListener("open", () => {
      this.send({
        type: "join",
        name,
        color,
        token: savedToken,
      });
      this.startPing();
    });

    this.ws.addEventListener("message", (ev) => {
      try {
        const msg = JSON.parse(ev.data);
        if (msg.type === "welcome") {
          this.slot = msg.slot ?? null;
          this.token = msg.token ?? null;
          if (this.token) {
            localStorage.setItem(`rails_token_${this.code}`, this.token);
          }
          this.cb.onWelcome?.(msg);
        } else if (msg.type === "lobby_update") {
          this.cb.onLobby?.(msg.lobby);
        } else if (msg.type === "state_update") {
          this.cb.onState?.(msg.state, msg.seq);
        } else if (msg.type === "draft_broadcast") {
          this.cb.onDraft?.(msg.draft);
        } else if (msg.type === "error") {
          this.cb.onError?.(msg.message);
        }
      } catch (err) {
        this.cb.onError?.(`Bad server frame: ${err.message}`);
      }
    });

    this.ws.addEventListener("close", () => {
      this.stopPing();
      if (!this.closedIntentionally) {
        this.cb.onDisconnect?.();
        setTimeout(() => {
          if (!this.closedIntentionally && this.code) {
            this.connect(this.code, name, color);
          }
        }, 2000);
      }
    });
  }

  send(msg) {
    if (this.ws && this.ws.readyState === WebSocket.OPEN) {
      this.ws.send(JSON.stringify(msg));
    }
  }

  sendDraft(buildEdges, movePath) {
    const now = performance.now();
    if (now - this.lastDraftSentAt < 65) return;
    this.lastDraftSentAt = now;
    this.send({
      type: "draft",
      build_edges: buildEdges,
      move_path: movePath,
    });
  }

  close() {
    this.closedIntentionally = true;
    this.stopPing();
    if (this.ws) {
      this.ws.close();
      this.ws = null;
    }
  }

  startPing() {
    this.stopPing();
    this.pingTimer = setInterval(() => this.send({ type: "ping" }), 25000);
  }

  stopPing() {
    if (this.pingTimer) {
      clearInterval(this.pingTimer);
      this.pingTimer = null;
    }
  }
}
