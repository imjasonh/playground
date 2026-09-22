import net from "node:net";

const DEFAULT_HTTP = "http://127.0.0.1:9146";
const DEFAULT_TELNET_PORT = 5501;

const SENSOR_PATHS = {
  lat: "/position/latitude-deg",
  lon: "/position/longitude-deg",
  altitude_ft: "/position/altitude-ft",
  heading_deg: "/orientation/heading-deg",
  pitch_deg: "/orientation/pitch-deg",
  roll_deg: "/orientation/roll-deg",
  airspeed_kt: "/velocities/airspeed-kt",
  vsi_fpm: "/velocities/vertical-speed-fps",
  slip_deg: "/orientation/side-slip-deg",
  aileron: "/controls/flight/aileron",
  elevator: "/controls/flight/elevator",
  rudder: "/controls/flight/rudder",
  throttle: "/controls/engines/engine/throttle",
};

/**
 * FlightGear property tree over Phi HTTP, with a telnet fallback.
 * 2020.3 Phi serves /json/path and /set?/path=value.
 */
export function createFgClient(options = {}) {
  return {
    httpBase: options.httpBase ?? process.env.FG_HTTP ?? DEFAULT_HTTP,
    telnetHost: options.telnetHost ?? "127.0.0.1",
    telnetPort: options.telnetPort ?? DEFAULT_TELNET_PORT,
    transport: options.transport ?? "auto",
    telnet: null,
  };
}

export async function fgProbe(client) {
  if (client.transport !== "telnet") {
    try {
      const value = await fgHttpGet(client.httpBase, "/sim/time/elapsed-sec");
      if (value != null) {
        client.transport = "http";
        return "http";
      }
    } catch {
      // try telnet
    }
  }
  if (client.transport !== "http") {
    client.telnet = await FgTelnet.connect(client.telnetHost, client.telnetPort);
    client.transport = "telnet";
    return "telnet";
  }
  throw new Error("FlightGear HTTP and telnet are both unreachable");
}

export async function fgReadSensors(client) {
  const raw = {};
  for (const [key, path] of Object.entries(SENSOR_PATHS)) {
    raw[key] = await fgGet(client, path);
  }
  if (Number.isFinite(raw.vsi_fpm)) {
    // FG vertical-speed-fps → fpm
    if (Math.abs(raw.vsi_fpm) < 80) {
      raw.vsi_fpm = raw.vsi_fpm * 60;
    }
  }
  return raw;
}

export async function fgWriteControls(client, controls, meta = {}) {
  await fgSet(client, "/controls/flight/aileron", controls.aileron);
  await fgSet(client, "/controls/flight/elevator", controls.elevator);
  await fgSet(client, "/controls/flight/rudder", controls.rudder);
  await fgSet(client, "/controls/engines/engine/throttle", controls.throttle);
  await fgSet(client, "/laya/cmd/aileron", controls.aileron);
  await fgSet(client, "/laya/cmd/elevator", controls.elevator);
  await fgSet(client, "/laya/cmd/rudder", controls.rudder);
  await fgSet(client, "/laya/cmd/throttle", controls.throttle);
  await fgSet(client, "/laya/cmd/stamp", Math.floor(Date.now() / 1000));
  if (meta.backend) {
    await fgSet(client, "/laya/backend", meta.backend);
  }
  if (meta.choice) {
    await fgSet(client, "/laya/last-choice", meta.choice);
  }
}

export async function fgGet(client, path) {
  if (client.transport === "telnet") {
    return client.telnet.get(path);
  }
  return fgHttpGet(client.httpBase, path);
}

export async function fgSet(client, path, value) {
  if (client.transport === "telnet") {
    return client.telnet.set(path, value);
  }
  return fgHttpSet(client.httpBase, path, value);
}

export async function fgHttpGet(base, path) {
  const url = `${base.replace(/\/$/, "")}/json${path}`;
  const response = await fetch(url, { signal: AbortSignal.timeout(2000) });
  if (!response.ok) {
    throw new Error(`FG HTTP get ${path} ${response.status}`);
  }
  const body = await response.json();
  if (body && typeof body === "object" && "value" in body) {
    return coerce(body.value);
  }
  return coerce(body);
}

export async function fgHttpSet(base, path, value) {
  const url = `${base.replace(/\/$/, "")}/set?${path}=${encodeURIComponent(String(value))}`;
  const response = await fetch(url, { signal: AbortSignal.timeout(2000) });
  if (!response.ok) {
    throw new Error(`FG HTTP set ${path} ${response.status}`);
  }
}

class FgTelnet {
  static connect(host, port, timeoutMs = 4000) {
    return new Promise((resolve, reject) => {
      const socket = net.createConnection({ host, port });
      const client = new FgTelnet(socket);
      const timer = setTimeout(() => {
        socket.destroy();
        reject(new Error(`telnet ${host}:${port} timed out`));
      }, timeoutMs);
      socket.once("error", reject);
      socket.once("connect", () => {
        clearTimeout(timer);
        resolve(client);
      });
    });
  }

  constructor(socket) {
    this.socket = socket;
    this.buf = "";
    this.queue = [];
    this.ready = Promise.resolve();
    socket.on("data", (chunk) => {
      this.buf += chunk.toString("utf8");
      this.flush();
    });
    socket.on("error", (err) => {
      const pending = this.queue.shift();
      if (pending) {
        pending.reject(err);
      }
    });
  }

  flush() {
    if (this.queue.length === 0) {
      return;
    }
    const pending = this.queue[0];
    const idx = this.buf.search(/\/?> $/m);
    if (idx < 0 && !this.buf.includes("\n")) {
      return;
    }
    const cut = idx >= 0 ? idx : this.buf.length;
    const text = this.buf.slice(0, cut).trim();
    this.buf = idx >= 0 ? this.buf.slice(idx).replace(/\/?>\s*$/, "") : "";
    this.queue.shift();
    pending.resolve(text);
  }

  cmd(line) {
    return new Promise((resolve, reject) => {
      this.queue.push({ resolve, reject });
      this.socket.write(`${line}\r\n`);
    });
  }

  async get(path) {
    const text = await this.cmd(`get ${path}`);
    const match = text.match(/=\s*'([^']*)'/);
    if (match) {
      return coerce(match[1]);
    }
    const loose = text.match(/=\s*(\S+)/);
    return loose ? coerce(loose[1]) : null;
  }

  async set(path, value) {
    await this.cmd(`set ${path} ${value}`);
  }

  close() {
    this.socket.end();
  }
}

function coerce(value) {
  if (typeof value === "number") {
    return value;
  }
  if (value === "true") return true;
  if (value === "false") return false;
  const n = Number(value);
  return Number.isFinite(n) ? n : value;
}

export { SENSOR_PATHS };
