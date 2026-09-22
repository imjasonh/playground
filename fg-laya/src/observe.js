import { headingErrorDeg } from "./geo.js";

function band(value, edges, labels) {
  for (let i = 0; i < edges.length; i++) {
    if (value < edges[i]) {
      return labels[i];
    }
  }
  return labels[labels.length - 1];
}

/**
 * Turn raw instruments plus a nav target into the JSON state a System One
 * model reads. Numbers stay on the object. Feelings are short English so Jev
 * and Laya do not have to parse raw degrees.
 */
export function observe(raw, nav) {
  const headingErr = headingErrorDeg(raw.heading_deg, nav.desired_heading_deg);
  const altErr = raw.altitude_ft - nav.target_alt_ft;
  const speedErr = raw.airspeed_kt - nav.target_speed_kt;
  const radiusErr = nav.radius_nm == null ? null : nav.distance_nm - nav.radius_nm;

  const state = {
    mission: nav.mission,
    altitude_ft: round(raw.altitude_ft, 0),
    altitude_err_ft: round(altErr, 0),
    altitude_feel: band(altErr, [-400, -120, 120, 400], [
      "much too low",
      "a bit low",
      "on altitude",
      "a bit high",
      "much too high",
    ]),
    airspeed_kt: round(raw.airspeed_kt, 1),
    airspeed_err_kt: round(speedErr, 1),
    airspeed_feel: band(speedErr, [-15, -5, 5, 15], [
      "dangerously slow",
      "a bit slow",
      "on speed",
      "a bit fast",
      "much too fast",
    ]),
    pitch_deg: round(raw.pitch_deg, 1),
    pitch_feel: band(raw.pitch_deg, [-8, -2, 4, 10], [
      "steep nose down",
      "slight nose down",
      "almost level",
      "slight nose up",
      "steep nose up",
    ]),
    roll_deg: round(raw.roll_deg, 1),
    roll_feel: describeRoll(raw.roll_deg),
    heading_deg: round(raw.heading_deg, 0),
    desired_heading_deg: round(nav.desired_heading_deg, 0),
    heading_err_deg: round(headingErr, 0),
    heading_feel: describeHeading(headingErr),
    vsi_fpm: round(raw.vsi_fpm, 0),
    vsi_feel: band(raw.vsi_fpm, [-800, -200, 200, 800], [
      "descending fast",
      "descending",
      "level",
      "climbing",
      "climbing fast",
    ]),
    slip_deg: round(raw.slip_deg ?? 0, 1),
    throttle: round(raw.throttle, 2),
    aileron: round(raw.aileron, 2),
    elevator: round(raw.elevator, 2),
    rudder: round(raw.rudder, 2),
    waypoint: {
      name: nav.waypoint_name,
      bearing_deg: round(nav.bearing_deg, 0),
      distance_nm: round(nav.distance_nm, 2),
      arrived: nav.distance_nm <= nav.arrival_nm,
    },
    target_alt_ft: nav.target_alt_ft,
    target_speed_kt: nav.target_speed_kt,
  };

  if (radiusErr != null) {
    state.orbit = {
      radius_nm: nav.radius_nm,
      distance_to_center_nm: round(nav.distance_nm_center ?? nav.distance_nm, 2),
      radius_err_nm: round(radiusErr, 2),
      radius_feel: band(radiusErr, [-0.4, -0.1, 0.1, 0.4], [
        "well inside the circle",
        "a bit inside",
        "on the circle",
        "a bit outside",
        "well outside the circle",
      ]),
    };
  }

  state.stall_risk = raw.airspeed_kt < 60 ? "high" : raw.airspeed_kt < 70 ? "watch" : "none";
  state.overbank_risk = Math.abs(raw.roll_deg) > 35 ? "high" : Math.abs(raw.roll_deg) > 28 ? "watch" : "none";
  return state;
}

function describeRoll(roll) {
  const side = roll < 0 ? "left" : "right";
  const mag = Math.abs(roll);
  if (mag < 4) {
    return "wings almost level";
  }
  if (mag < 15) {
    return `shallow ${side} bank`;
  }
  if (mag < 28) {
    return `${side} bank about ${Math.round(mag)} deg`;
  }
  return `steep ${side} bank`;
}

function describeHeading(err) {
  const side = err < 0 ? "left" : "right";
  const mag = Math.abs(err);
  if (mag < 5) {
    return "nose on the desired heading";
  }
  if (mag < 15) {
    return `need a little ${side}`;
  }
  if (mag < 45) {
    return `turn ${side} about ${Math.round(mag)} deg`;
  }
  return `waypoint is far ${side}, turn ${side}`;
}

function round(value, digits) {
  const n = Number(value);
  if (!Number.isFinite(n)) {
    return 0;
  }
  const p = 10 ** digits;
  return Math.round(n * p) / p;
}

export function rawFromAircraft(ac) {
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
