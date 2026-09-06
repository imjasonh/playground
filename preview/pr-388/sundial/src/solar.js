// Sun position follows the NOAA solar calculator (Meeus).
// Azimuth is degrees clockwise from north: 0 north, 90 east, 180 south, 270 west.

export const DEFAULT_LATITUDE = 40.7;

const DEG = Math.PI / 180;
const RAD = 180 / Math.PI;
const MINUTES_PER_DAY = 1440;

export function clamp(value, minimum, maximum) {
  return Math.min(maximum, Math.max(minimum, value));
}

export function wrapDegrees(value) {
  return ((value % 360) + 360) % 360;
}

function wrapMinutes(value) {
  return ((value % MINUTES_PER_DAY) + MINUTES_PER_DAY) % MINUTES_PER_DAY;
}

function toDeg(radians) {
  return radians * RAD;
}

function toRad(degrees) {
  return degrees * DEG;
}

function acosClamped(value) {
  return Math.acos(clamp(value, -1, 1));
}

function asinClamped(value) {
  return Math.asin(clamp(value, -1, 1));
}

export function julianDate(date) {
  return date.getTime() / 86400000 + 2440587.5;
}

export function longitudeFromTimezoneOffset(offsetMinutes) {
  return (-offsetMinutes / 60) * 15 + 0;
}

export function parseLocation(search, date) {
  const params = new URLSearchParams(search);
  let latitude = DEFAULT_LATITUDE;
  let longitude = longitudeFromTimezoneOffset(date.getTimezoneOffset());

  if (params.has("lat")) {
    const parsed = Number.parseFloat(params.get("lat"));
    if (Number.isFinite(parsed)) {
      latitude = clamp(parsed, -90, 90);
    }
  }
  if (params.has("lon")) {
    const parsed = Number.parseFloat(params.get("lon"));
    if (Number.isFinite(parsed)) {
      longitude = clamp(parsed, -180, 180);
    }
  }

  return { latitude, longitude };
}

export function resolveLocation(search, date, geo) {
  if (
    geo &&
    Number.isFinite(geo.latitude) &&
    Number.isFinite(geo.longitude)
  ) {
    return {
      latitude: clamp(geo.latitude, -90, 90),
      longitude: clamp(geo.longitude, -180, 180),
      source: "geo",
    };
  }

  const fallback = parseLocation(search, date);
  return {
    latitude: fallback.latitude,
    longitude: fallback.longitude,
    source: "clock",
  };
}

export function parsePinnedTime(search) {
  const params = new URLSearchParams(search);
  if (!params.has("at")) {
    return null;
  }
  const parsed = new Date(params.get("at"));
  if (Number.isNaN(parsed.getTime())) {
    return null;
  }
  return parsed;
}

export function sunPosition(date, latitude, longitude) {
  const jd = julianDate(date);
  const century = (jd - 2451545) / 36525;

  const geomMeanLong = wrapDegrees(
    280.46646 + century * (36000.76983 + century * 0.0003032),
  );
  const geomMeanAnom =
    357.52911 + century * (35999.05029 - 0.0001537 * century);
  const eccent =
    0.016708634 - century * (0.000042037 + 0.0000001267 * century);

  const anomRad = toRad(geomMeanAnom);
  const eqCenter =
    Math.sin(anomRad) *
      (1.914602 - century * (0.004817 + 0.000014 * century)) +
    Math.sin(2 * anomRad) * (0.019993 - 0.000101 * century) +
    Math.sin(3 * anomRad) * 0.000289;

  const sunTrueLong = geomMeanLong + eqCenter;
  const omega = 125.04 - 1934.136 * century;
  const sunAppLong =
    sunTrueLong - 0.00569 - 0.00478 * Math.sin(toRad(omega));

  const meanObliq =
    23 +
    (26 +
      (21.448 -
        century * (46.815 + century * (0.00059 - century * 0.001813))) /
        60) /
      60;
  const obliq = meanObliq + 0.00256 * Math.cos(toRad(omega));

  const declination = toDeg(
    asinClamped(Math.sin(toRad(obliq)) * Math.sin(toRad(sunAppLong))),
  );

  const y = Math.tan(toRad(obliq / 2)) ** 2;
  const meanLongRad = toRad(geomMeanLong);
  const eqOfTime =
    4 *
    toDeg(
      y * Math.sin(2 * meanLongRad) -
        2 * eccent * Math.sin(anomRad) +
        4 * eccent * y * Math.sin(anomRad) * Math.cos(2 * meanLongRad) -
        0.5 * y * y * Math.sin(4 * meanLongRad) -
        1.25 * eccent * eccent * Math.sin(2 * anomRad),
    );

  const utcMinutes =
    date.getUTCHours() * 60 +
    date.getUTCMinutes() +
    date.getUTCSeconds() / 60 +
    date.getUTCMilliseconds() / 60000;
  const trueSolarTime = wrapMinutes(utcMinutes + eqOfTime + 4 * longitude);
  const hourAngle = trueSolarTime / 4 - 180;

  const latRad = toRad(latitude);
  const decRad = toRad(declination);
  const haRad = toRad(hourAngle);
  const zenith = toDeg(
    acosClamped(
      Math.sin(latRad) * Math.sin(decRad) +
        Math.cos(latRad) * Math.cos(decRad) * Math.cos(haRad),
    ),
  );
  const altitude = 90 - zenith;

  const sinZenith = Math.sin(toRad(zenith));
  let azimuth = 180;
  if (sinZenith >= 1e-10) {
    const azCos = acosClamped(
      (Math.sin(latRad) * Math.cos(toRad(zenith)) - Math.sin(decRad)) /
        (Math.cos(latRad) * sinZenith),
    );
    const azDeg = toDeg(azCos);
    if (hourAngle > 0) {
      azimuth = wrapDegrees(azDeg + 180);
    } else {
      azimuth = wrapDegrees(540 - azDeg);
    }
  }

  return {
    altitude,
    azimuth,
    declination,
    hourAngle,
  };
}

export function isNight(altitudeDeg) {
  return altitudeDeg <= 0;
}

export function shadowStrength(altitudeDeg) {
  if (altitudeDeg <= 0) {
    return 0;
  }
  return clamp(altitudeDeg / 2, 0, 1);
}

export function shadowLengthFactor(altitudeDeg) {
  const rise = clamp(altitudeDeg, 0, 90) / 90;
  return 1 - 0.42 * rise * rise;
}

export function gnomonShadow(sun, maxLengthPx) {
  const strength = shadowStrength(sun.altitude);
  if (strength <= 0) {
    return {
      visible: false,
      azimuth: 0,
      length: 0,
      offsetX: 0,
      offsetY: 0,
      strength: 0,
    };
  }

  const azimuth = wrapDegrees(sun.azimuth + 180);
  const length = Math.max(
    maxLengthPx * 0.34,
    maxLengthPx * shadowLengthFactor(sun.altitude) * strength,
  );
  const theta = toRad(azimuth);
  return {
    visible: true,
    azimuth,
    length,
    offsetX: Math.sin(theta) * length,
    offsetY: -Math.cos(theta) * length,
    strength,
  };
}

export function castLayers(shadow, color) {
  if (shadow.strength <= 0 || shadow.length <= 0) {
    return [];
  }

  const angle = Math.atan2(shadow.offsetX, shadow.offsetY) * (180 / Math.PI);
  return [
    {
      x: shadow.offsetX * 0.76,
      y: shadow.offsetY * 0.76,
      blur: 4 + shadow.length * 0.012,
      opacity: clamp(color.a * shadow.strength * 1.25, 0, 0.4),
      stretch: 1,
      angle,
    },
    {
      x: shadow.offsetX * 1.14,
      y: shadow.offsetY * 1.14,
      blur: 16 + shadow.length * 0.09,
      opacity: clamp(color.a * shadow.strength * 0.75, 0, 0.3),
      stretch: 1 + clamp(shadow.length / 1200, 0, 0.22),
      angle,
    },
  ];
}

export function castTransform(layer) {
  return `translate(${layer.x.toFixed(2)}px, ${layer.y.toFixed(2)}px) rotate(${layer.angle.toFixed(2)}deg) scaleY(${layer.stretch.toFixed(3)}) rotate(${(-layer.angle).toFixed(2)}deg)`;
}

export function mixRgb(from, to, amount) {
  const t = clamp(amount, 0, 1);
  return {
    r: Math.round(from.r + (to.r - from.r) * t),
    g: Math.round(from.g + (to.g - from.g) * t),
    b: Math.round(from.b + (to.b - from.b) * t),
  };
}

export function rgbCss(color) {
  return `rgb(${color.r}, ${color.g}, ${color.b})`;
}

export function rgbToHex(color) {
  const parts = [color.r, color.g, color.b].map((value) =>
    value.toString(16).padStart(2, "0"),
  );
  return `#${parts.join("")}`;
}

function ramp(stops, value) {
  if (value <= stops[0].at) {
    return stops[0].color;
  }
  for (let i = 1; i < stops.length; i += 1) {
    if (value <= stops[i].at) {
      const span = stops[i].at - stops[i - 1].at;
      const amount = (value - stops[i - 1].at) / span;
      return mixRgb(stops[i - 1].color, stops[i].color, amount);
    }
  }
  return stops[stops.length - 1].color;
}

const INK_DAY = { r: 28, g: 24, b: 18 };
const INK_NIGHT = { r: 228, g: 222, b: 208 };
const PAPER_NIGHT = { r: 10, g: 12, b: 16 };
const PAPER_DAWN = { r: 56, g: 50, b: 68 };
const PAPER_DUSK = { r: 62, g: 36, b: 44 };
const PAPER_GOLDEN = { r: 234, g: 172, b: 118 };
const PAPER_DAY = { r: 244, g: 236, b: 220 };
const PAPER_NOON = { r: 248, g: 245, b: 236 };
const SHADOW_GOLDEN = { r: 58, g: 36, b: 26 };
const SHADOW_DAY = { r: 40, g: 38, b: 36 };

export function sceneFromSun(sun) {
  const morning = sun.azimuth < 180;
  let twilight;
  if (morning) {
    twilight = PAPER_DAWN;
  } else {
    twilight = PAPER_DUSK;
  }

  const paper = ramp(
    [
      { at: -90, color: PAPER_NIGHT },
      { at: -12, color: PAPER_NIGHT },
      { at: 0, color: twilight },
      { at: 7, color: PAPER_GOLDEN },
      { at: 28, color: PAPER_DAY },
      { at: 62, color: PAPER_NOON },
    ],
    sun.altitude,
  );

  let ink;
  if (sun.altitude <= 0) {
    const nightLift = clamp((sun.altitude + 12) / 12, 0, 1);
    ink = mixRgb(INK_NIGHT, INK_DAY, nightLift * 0.15);
  } else {
    ink = INK_DAY;
  }

  const shadowMix = clamp(sun.altitude / 28, 0, 1);
  const shadowRgb = mixRgb(SHADOW_GOLDEN, SHADOW_DAY, shadowMix);
  let shadowAlpha = 0.42;
  if (sun.altitude < 10) {
    shadowAlpha = 0.5;
  }

  const sunX = 50 + Math.sin(toRad(sun.azimuth)) * 44;
  const sunY = 50 - Math.cos(toRad(sun.azimuth)) * 38;

  let highlight;
  if (isNight(sun.altitude)) {
    highlight = { r: paper.r, g: paper.g, b: paper.b };
  } else {
    highlight = mixRgb(paper, { r: 255, g: 248, b: 230 }, 0.55);
  }

  return {
    ink,
    paper,
    shadow: {
      r: shadowRgb.r,
      g: shadowRgb.g,
      b: shadowRgb.b,
      a: shadowAlpha,
    },
    highlight,
    sunX,
    sunY,
    night: isNight(sun.altitude),
    colorScheme: isNight(sun.altitude) ? "dark" : "light",
  };
}

export function pageBackground(scene) {
  if (scene.night) {
    return rgbCss(scene.paper);
  }
  return `radial-gradient(ellipse 90% 70% at ${scene.sunX.toFixed(1)}% ${scene.sunY.toFixed(1)}%, ${rgbCss(scene.highlight)} 0%, transparent 56%), ${rgbCss(scene.paper)}`;
}
