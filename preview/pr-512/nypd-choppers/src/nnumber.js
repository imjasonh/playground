// Convert a US FAA tail number (N-number) to its 24-bit ICAO Mode-S address.
//
// US civil aircraft use a deterministic mapping between the registration
// (e.g. "N917PD") and the ICAO hex broadcast over ADS-B (e.g. "ACB1F5").
// Encoding it ourselves lets the scraper query adsb.lol purely by hex and lets
// the app label aircraft without any live registration lookup.
//
// The mapping is a sequential allocation from 0xA00001 ("N1") to 0xADF7C7
// ("N99999"). This is the forward of the well-documented ADSBExchange
// `n_reg()` decoder; see
// https://github.com/guillaumemichel/icao-nnumber_converter.

// Letters used in N-numbers, excluding I and O (they resemble 1 and 0).
const CHARSET = "ABCDEFGHJKLMNPQRSTUVWXYZ";

const ICAO_BASE = 0xa00001; // maps to "N1"

// Size of the block of tail numbers reachable from each digit position.
const BUCKET_1 = 101711; // leading digit (1-9)
const BUCKET_2 = 10111; // second character, when a digit
const BUCKET_3 = 951; // third character, when a digit
const BUCKET_4 = 35; // fourth character, when a digit

// Pure-suffix states ("", A..Z, AA..ZZ) sharing each digit prefix. The final
// character position only allows a single-letter suffix ("", A..Z) = 25 states.
const SUFFIX_STATES = 601;
const LAST_SUFFIX_STATES = 25;

function isDigit(ch) {
  return ch >= "0" && ch <= "9";
}

// Offset contributed by a 0-, 1-, or 2-letter suffix. Returns null if the
// suffix contains an invalid character. Range: 0 ("") .. 600 ("ZZ").
function suffixOffset(suffix) {
  if (suffix.length === 0) return 0;
  const first = CHARSET.indexOf(suffix[0]);
  if (first < 0) return null;
  let offset = first * 25 + 1;
  if (suffix.length === 1) return offset;
  if (suffix.length > 2) return null;
  const second = CHARSET.indexOf(suffix[1]);
  if (second < 0) return null;
  return offset + second + 1;
}

/**
 * Convert an N-number to an uppercase ICAO hex string, or null when the input
 * is not a US registration this scheme can encode.
 * @param {string} nnumber e.g. "N917PD"
 * @returns {string|null} e.g. "ACB1F5"
 */
export function nNumberToIcao(nnumber) {
  if (typeof nnumber !== "string") return null;
  const tail = nnumber.trim().toUpperCase();
  if (tail.length < 2 || tail.length > 6 || tail[0] !== "N") return null;

  const rest = tail.slice(1);
  if (!isDigit(rest[0]) || rest[0] === "0") return null;

  let offset = (Number(rest[0]) - 1) * BUCKET_1;
  const buckets = [BUCKET_2, BUCKET_3, BUCKET_4];
  let i = 1;

  // Positions 2-4: each may be a digit (advancing to the next bucket) or the
  // start of the letter suffix (which ends the number).
  for (const bucket of buckets) {
    if (i >= rest.length) return finish(offset);
    const ch = rest[i];
    if (CHARSET.includes(ch)) {
      const s = suffixOffset(rest.slice(i));
      return s === null ? null : finish(offset + s);
    }
    if (!isDigit(ch)) return null;
    offset += SUFFIX_STATES + Number(ch) * bucket;
    i += 1;
  }

  // Position 5: a single trailing letter or digit (no further suffix).
  if (i < rest.length) {
    const ch = rest[i];
    if (CHARSET.includes(ch)) {
      offset += CHARSET.indexOf(ch) + 1;
    } else if (isDigit(ch)) {
      offset += LAST_SUFFIX_STATES + Number(ch);
    } else {
      return null;
    }
  }

  return finish(offset);
}

function finish(offset) {
  return (ICAO_BASE + offset).toString(16).toUpperCase().padStart(6, "0");
}
