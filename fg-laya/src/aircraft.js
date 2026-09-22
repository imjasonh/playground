import { clamp, wrap360 } from "./geo.js";
import { DEFAULT_ALT_FT, DEFAULT_HOME, DEFAULT_SPEED_KT } from "./nav.js";

/** Light Cessna-shaped kinematics. Bank turns, pitch climbs, throttle sets speed. */
export function createAircraft(ic = {}) {
  return {
    lat: ic.lat ?? DEFAULT_HOME.lat,
    lon: ic.lon ?? DEFAULT_HOME.lon,
    alt_ft: ic.alt_ft ?? DEFAULT_ALT_FT,
    heading_deg: ic.heading_deg ?? 0,
    pitch_deg: ic.pitch_deg ?? 2,
    roll_deg: ic.roll_deg ?? 0,
    airspeed_kt: ic.airspeed_kt ?? DEFAULT_SPEED_KT,
    vsi_fpm: ic.vsi_fpm ?? 0,
    slip_deg: 0,
    aileron: 0,
    elevator: 0,
    rudder: 0,
    throttle: ic.throttle ?? 0.72,
    engine_running: true,
    gear_down: false,
    time_s: 0,
  };
}

export function applyControls(ac, controls) {
  ac.aileron = clamp(controls.aileron, -1, 1);
  ac.elevator = clamp(controls.elevator, -1, 1);
  ac.rudder = clamp(controls.rudder, -1, 1);
  ac.throttle = clamp(controls.throttle, 0, 1);
  return ac;
}

export function stepAircraft(ac, dt) {
  const tas = Math.max(45, ac.airspeed_kt);
  ac.roll_deg = clamp(ac.roll_deg + ac.aileron * 42 * dt, -42, 42);
  const bankRad = (ac.roll_deg * Math.PI) / 180;
  const turnRate = (1091 * Math.tan(bankRad)) / tas;
  ac.heading_deg = wrap360(ac.heading_deg + turnRate * dt);

  ac.pitch_deg = clamp(ac.pitch_deg + ac.elevator * 14 * dt, -16, 18);
  const tgtSpeed = 58 + 82 * ac.throttle - ac.pitch_deg * 1.15;
  ac.airspeed_kt = clamp(ac.airspeed_kt + (tgtSpeed - ac.airspeed_kt) * 0.38 * dt, 42, 155);

  const stalled = ac.airspeed_kt < 55;
  const gamma = stalled ? ac.pitch_deg - 14 : ac.pitch_deg - 1.6;
  ac.vsi_fpm = tas * 101.27 * Math.sin((gamma * Math.PI) / 180);
  ac.alt_ft = Math.max(0, ac.alt_ft + (ac.vsi_fpm / 60) * dt);

  const nm = (ac.airspeed_kt / 3600) * dt;
  const hdg = (ac.heading_deg * Math.PI) / 180;
  ac.lat += (nm / 60) * Math.cos(hdg);
  ac.lon += ((nm / 60) * Math.sin(hdg)) / Math.cos((ac.lat * Math.PI) / 180);
  ac.slip_deg = ac.rudder * 7 - ac.roll_deg * 0.04;
  ac.time_s += dt;
  return ac;
}

export function aircraftRaw(ac) {
  return {
    lat: ac.lat,
    lon: ac.lon,
    altitude_ft: ac.alt_ft,
    heading_deg: ac.heading_deg,
    pitch_deg: ac.pitch_deg,
    roll_deg: ac.roll_deg,
    airspeed_kt: ac.airspeed_kt,
    vsi_fpm: ac.vsi_fpm,
    slip_deg: ac.slip_deg,
    aileron: ac.aileron,
    elevator: ac.elevator,
    rudder: ac.rudder,
    throttle: ac.throttle,
  };
}
