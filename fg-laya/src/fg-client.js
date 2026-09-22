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

const ENGINE_PROPS = [
  ["/controls/switches/master-bat", true],
  ["/controls/switches/master-alt", true],
  ["/controls/switches/magnetos", 3],
  ["/controls/engines/engine/magnetos", 3],
  ["/controls/engines/engine/mixture", 1],
  ["/controls/engines/current-engine/mixture", 1],
  ["/controls/engines/engine/throttle", 0.8],
  ["/controls/engines/engine/primer", 4],
  ["/controls/engines/engine/starter", true],
  ["/controls/switches/starter", true],
  ["/fdm/jsbsim/propulsion/engine[0]/set-running", 1],
  ["/fdm/jsbsim/propulsion/set-running", -1],
  ["/engines/active-engine/running", true],
  ["/engines/engine/running", true],
  ["/controls/gear/brake-parking", false],
  ["/controls/gear/gear-down", false],
  ["/controls/flight/flaps", 0],
  ["/sim/crashed", false],
];

/**
 * FlightGear property tree over Phi HTTP, with a telnet fallback.
 * 2020.3 Phi serves GET/POST /json/path and GET /run.cgi?value=<fgcommand>.
 */
export function createFgClient(options = {}) {
  return {
    httpBase: options.httpBase ?? process.env.FG_HTTP ?? DEFAULT_HTTP,
    telnetHost: options.telnetHost ?? "127.0.0.1",
    telnetPort: options.telnetPort ?? DEFAULT_TELNET_PORT,
    transport: options.transport ?? "auto",
    telnet: null,
    writeAddon: options.writeAddon === true,
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
  const entries = Object.entries(SENSOR_PATHS);
  const values = client.transport === "http"
    ? await Promise.all(entries.map(([, path]) => fgGet(client, path)))
    : await mapSequential(entries, ([, path]) => fgGet(client, path));
  const raw = {};
  entries.forEach(([key], i) => {
    raw[key] = values[i];
  });
  if (Number.isFinite(raw.vsi_fpm) && Math.abs(raw.vsi_fpm) < 80) {
    raw.vsi_fpm = raw.vsi_fpm * 60;
  }
  return raw;
}

export function airbornePresets(options = {}) {
  return [
    ["/sim/presets/latitude-deg", options.lat ?? 37.576],
    ["/sim/presets/longitude-deg", options.lon ?? -122.65],
    ["/sim/presets/altitude-ft", options.alt_ft ?? 3500],
    ["/sim/presets/airspeed-kt", options.airspeed_kt ?? 105],
    ["/sim/presets/heading-deg", options.heading_deg ?? 90],
    ["/sim/presets/pitch-deg", options.pitch_deg ?? 2],
    ["/sim/presets/roll-deg", 0],
    ["/sim/presets/offset-distance-nm", 0],
    ["/sim/presets/airport-id", ""],
    ["/sim/presets/runway", ""],
  ];
}

export function engineProps() {
  return ENGINE_PROPS.slice();
}

export function needsAirborneReset(raw) {
  if (!raw) {
    return false;
  }
  const alt = Number(raw.altitude_ft);
  const ias = Number(raw.airspeed_kt);
  const roll = Number(raw.roll_deg);
  const pitch = Number(raw.pitch_deg);
  if (Number.isFinite(alt) && alt < 400) {
    return true;
  }
  if (Number.isFinite(ias) && ias < 50) {
    return true;
  }
  if (Number.isFinite(roll) && Math.abs(roll) > 80) {
    return true;
  }
  if (Number.isFinite(pitch) && Math.abs(pitch) > 50) {
    return true;
  }
  return false;
}

/**
 * Freeze, start the C172 engine, put the airplane back at cruise, then
 * unfreeze. Uses Phi /run.cgi reposition. Missing nodes are ignored so the
 * same list works on a simpler aircraft.
 */
export async function fgPrepAirborne(client, options = {}) {
  await setQuiet(client, "/sim/freeze/master", true);
  await setQuiet(client, "/sim/freeze/clock", true);
  await setQuiet(client, "/sim/crashed", false);
  for (const [path, value] of ENGINE_PROPS) {
    await setQuiet(client, path, value);
  }
  for (const [path, value] of airbornePresets(options)) {
    await setQuiet(client, path, value);
  }
  try {
    await fgRun(client, "reposition");
  } catch {
    // Older builds without /run.cgi still get the property writes above.
  }
  for (const [path, value] of ENGINE_PROPS) {
    await setQuiet(client, path, value);
  }
  await setQuiet(client, "/sim/menubar/visibility", false);
  await setQuiet(client, "/sim/current-view/view-number", options.view ?? 2);
  await setQuiet(client, "/autopilot/locks/heading", "");
  await setQuiet(client, "/autopilot/locks/altitude", "");
  await setQuiet(client, "/autopilot/locks/speed", "");
  await setQuiet(client, "/sim/freeze/master", false);
  await setQuiet(client, "/sim/freeze/clock", false);
}

export async function fgWriteControls(client, controls, meta = {}) {
  const writes = [
    ["/controls/flight/aileron", controls.aileron],
    ["/controls/flight/elevator", controls.elevator],
    ["/controls/flight/rudder", controls.rudder],
    ["/controls/engines/engine/throttle", controls.throttle],
  ];
  if (client.writeAddon) {
    writes.push(
      ["/laya/cmd/aileron", controls.aileron],
      ["/laya/cmd/elevator", controls.elevator],
      ["/laya/cmd/rudder", controls.rudder],
      ["/laya/cmd/throttle", controls.throttle],
      ["/laya/cmd/stamp", Math.floor(Date.now() / 1000)],
    );
    if (meta.backend) {
      writes.push(["/laya/backend", meta.backend]);
    }
    if (meta.choice) {
      writes.push(["/laya/last-choice", meta.choice]);
    }
  }
  if (client.transport === "http") {
    await Promise.all(writes.map(([path, value]) => setQuiet(client, path, value)));
    return;
  }
  for (const [path, value] of writes) {
    await setQuiet(client, path, value);
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

export async function fgRun(client, command) {
  if (client.transport === "telnet") {
    return client.telnet.cmd(`run ${command}`);
  }
  return fgHttpRun(client.httpBase, command);
}

export function runCgiUrl(base, command) {
  return `${String(base).replace(/\/$/, "")}/run.cgi?value=${encodeURIComponent(command)}`;
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
  const url = `${base.replace(/\/$/, "")}/json${path}`;
  const response = await fetch(url, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ value }),
    signal: AbortSignal.timeout(2000),
  });
  if (!response.ok) {
    throw new Error(`FG HTTP set ${path} ${response.status}`);
  }
}

export async function fgHttpRun(base, command) {
  const response = await fetch(runCgiUrl(base, command), {
    signal: AbortSignal.timeout(5000),
  });
  if (!response.ok) {
    throw new Error(`FG run ${command} ${response.status}`);
  }
  return response.text();
}

async function setQuiet(client, path, value) {
  try {
    await fgSet(client, path, value);
  } catch {
    // Aircraft-specific nodes (mixture, JSBSim set-running, locks) are optional.
  }
}

async function mapSequential(items, fn) {
  const out = [];
  for (const item of items) {
    out.push(await fn(item));
  }
  return out;
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
