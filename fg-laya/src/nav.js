import { bearingDeg, clamp, haversineNm, headingErrorDeg, offsetNm, wrap360 } from "./geo.js";

export const DEFAULT_HOME = { lat: 37.55, lon: -122.65 };
export const DEFAULT_ALT_FT = 3500;
export const DEFAULT_SPEED_KT = 100;
export const CIRCLE_RADIUS_NM = 1.6;
export const ARRIVAL_NM = 0.35;

export function createNav(options = {}) {
  const home = options.home ?? DEFAULT_HOME;
  const mission = options.mission ?? "circle";
  const rng = options.rng ?? Math.random;
  const nav = {
    mission,
    home,
    center: options.center ?? { ...home },
    radius_nm: options.radius_nm ?? CIRCLE_RADIUS_NM,
    arrival_nm: options.arrival_nm ?? ARRIVAL_NM,
    target_alt_ft: options.target_alt_ft ?? DEFAULT_ALT_FT,
    target_speed_kt: options.target_speed_kt ?? DEFAULT_SPEED_KT,
    waypoint_index: 0,
    waypoints: [],
    waypoint_name: "orbit",
    rng,
    arrivals: 0,
  };
  if (mission === "waypoints") {
    nav.waypoints = [offsetNm(home, 20, 0.9), randomWaypoint(nav)];
    nav.waypoint_name = "wp0";
  }
  return nav;
}

export function updateNav(nav, pos) {
  if (nav.mission === "circle") {
    return updateCircle(nav, pos);
  }
  return updateWaypoints(nav, pos);
}

function updateCircle(nav, pos) {
  const bearingToCenter = bearingDeg(pos, nav.center);
  const dist = haversineNm(pos, nav.center);
  const radiusErr = dist - nav.radius_nm;
  // Outside the ring, cut in toward the center. Inside, steer out.
  const intercept = clamp(-radiusErr * 28, -50, 50);
  const desired = wrap360(bearingToCenter + 90 + intercept);
  nav.desired_heading_deg = desired;
  nav.bearing_deg = desired;
  nav.distance_nm = dist;
  nav.distance_nm_center = dist;
  nav.waypoint_name = "orbit-left";
  if (Math.abs(headingErrorDeg(pos.heading_deg ?? desired, desired)) < 25 && Math.abs(radiusErr) < 0.25) {
    nav.arrivals += 0;
  }
  return nav;
}

function updateWaypoints(nav, pos) {
  if (nav.waypoints.length === 0) {
    nav.waypoints.push(randomWaypoint(nav));
  }
  let wp = nav.waypoints[nav.waypoint_index % nav.waypoints.length];
  let dist = haversineNm(pos, wp);
  if (dist <= nav.arrival_nm) {
    nav.arrivals += 1;
    nav.waypoints.push(randomWaypoint(nav));
    nav.waypoint_index = nav.waypoints.length - 1;
    wp = nav.waypoints[nav.waypoint_index];
    dist = haversineNm(pos, wp);
  }
  nav.desired_heading_deg = bearingDeg(pos, wp);
  nav.bearing_deg = nav.desired_heading_deg;
  nav.distance_nm = dist;
  nav.waypoint_name = `wp${nav.waypoint_index}`;
  nav.distance_nm_center = haversineNm(pos, nav.center);
  return nav;
}

export function maybeArrive(nav, pos, arrivedYes) {
  if (nav.mission !== "waypoints") {
    return nav;
  }
  if (!arrivedYes) {
    return nav;
  }
  const wp = nav.waypoints[nav.waypoint_index % nav.waypoints.length];
  if (!wp) {
    return nav;
  }
  const dist = haversineNm(pos, wp);
  if (dist > nav.arrival_nm * 1.8) {
    return nav;
  }
  nav.arrivals += 1;
  nav.waypoints.push(randomWaypoint(nav));
  nav.waypoint_index = nav.waypoints.length - 1;
  nav.waypoint_name = `wp${nav.waypoint_index}`;
  return nav;
}

export function randomWaypoint(nav) {
  const bearing = nav.rng() * 360;
  const dist = 1.2 + nav.rng() * 2.4;
  const point = offsetNm(nav.center, bearing, dist);
  point.alt_ft = nav.target_alt_ft;
  return point;
}

export function navSnapshot(nav) {
  return {
    mission: nav.mission,
    desired_heading_deg: nav.desired_heading_deg ?? 0,
    target_alt_ft: nav.target_alt_ft,
    target_speed_kt: nav.target_speed_kt,
    waypoint_name: nav.waypoint_name,
    bearing_deg: nav.bearing_deg ?? 0,
    distance_nm: nav.distance_nm ?? 0,
    distance_nm_center: nav.distance_nm_center ?? 0,
    radius_nm: nav.mission === "circle" ? nav.radius_nm : null,
    arrival_nm: nav.arrival_nm,
    arrivals: nav.arrivals,
    waypoint: nav.waypoints[nav.waypoint_index % Math.max(1, nav.waypoints.length)] ?? nav.center,
    center: nav.center,
  };
}
