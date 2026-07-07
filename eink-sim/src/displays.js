// Catalog of real-world e-ink / e-paper displays and the palette + physical
// response models used to simulate them.
//
// Sources (2024-2025 manufacturer spec sheets and teardown/converter projects):
//   - E Ink brand pages: Carta 1300, Kaleido 3, Gallery 3, Spectra 6
//   - Waveshare e-Paper product/wiki pages (E6, ACeP 7-color, tri/four-color)
//   - Kobo / Amazon / Boox device spec sheets
//   - Community converters for the canonical ACeP 7-color and E6 palettes
//
// The RGB values in the "ideal" palettes are the pure targets the converters
// dither toward. The muted, reflective look is applied separately by each
// display's `response` (see dither.js -> applyPanelResponse), so the same
// palette can look right on panels with different substrate/contrast.

// ---------------------------------------------------------------------------
// Ideal palette definitions (targets for quantization)
// ---------------------------------------------------------------------------

const BLACK = [0, 0, 0];
const WHITE = [255, 255, 255];
const RED = [255, 0, 0];
const GREEN = [0, 255, 0];
const BLUE = [0, 0, 255];
const YELLOW = [255, 255, 0];
const ORANGE = [255, 128, 0];

export const PALETTES = {
  mono1: { kind: "channel", levels: 2, grayscale: true },
  gray4: { kind: "channel", levels: 4, grayscale: true },
  gray16: { kind: "channel", levels: 16, grayscale: true },
  bwr: { kind: "list", colors: [BLACK, WHITE, RED] },
  bwry: { kind: "list", colors: [BLACK, WHITE, RED, YELLOW] },
  // E Ink Spectra 6 (E6): black, white, red, yellow, green, blue.
  spectra6: { kind: "list", colors: [BLACK, WHITE, RED, YELLOW, GREEN, BLUE] },
  // ACeP 7-color (Waveshare F / 5.65"): the classic converter palette.
  acep7: {
    kind: "list",
    colors: [BLACK, WHITE, GREEN, BLUE, RED, YELLOW, ORANGE],
  },
  // Color-filter-array panels render continuous color but at reduced bit depth;
  // 4 bits/channel (~4096 colors) matches Kaleido 3's marketing figure.
  kaleido3: { kind: "channel", levels: 16, grayscale: false },
  // Gallery 3 (true ACeP) reaches a wider gamut than Kaleido; model with more
  // channel levels but still muted via its response.
  gallery3: { kind: "channel", levels: 12, grayscale: false },
};

// ---------------------------------------------------------------------------
// Physical panel-response presets (reflective appearance)
// ---------------------------------------------------------------------------
//
// white/black are the measured-ish reflective extremes; saturation is the
// fraction of ideal chroma the inks retain. These are tuned to *look* like the
// technology on a bright monitor, not to be colorimetrically exact.

const RESPONSE = {
  carta: { white: [212, 211, 202], black: [46, 46, 44], saturation: 1 },
  cartaMono: { white: [216, 215, 206], black: [40, 40, 38], saturation: 1 },
  kaleido3: { white: [176, 175, 166], black: [58, 57, 54], saturation: 0.42 },
  gallery3: { white: [198, 196, 186], black: [45, 44, 42], saturation: 0.62 },
  spectra6: { white: [220, 218, 206], black: [42, 42, 40], saturation: 0.66 },
  acep7: { white: [205, 202, 190], black: [50, 49, 46], saturation: 0.55 },
  esl: { white: [214, 212, 201], black: [46, 46, 43], saturation: 0.72 },
};

// ---------------------------------------------------------------------------
// Device catalog
// ---------------------------------------------------------------------------
//
// Each display: id, name, category, physical size (inches, diagonal), native
// resolution (colorW/H), ppi, palette key, response key, refresh estimate, and
// a short note. `colorPpi` (when present) reflects CFA panels whose effective
// color resolution is half the mono resolution.

export const DISPLAYS = [
  // --- Monochrome (Carta) ---
  {
    id: "kindle-paperwhite-2024",
    name: "Kindle Paperwhite (2024)",
    category: "Monochrome (Carta)",
    inches: 7,
    width: 1264,
    height: 1680,
    ppi: 300,
    palette: "gray16",
    response: "carta",
    refresh: "~0.5 s full refresh",
    note: "E Ink Carta 1300, 16-level grayscale, 300 ppi.",
  },
  {
    id: "kobo-clara-bw",
    name: "Kindle / Kobo 6\" (mono)",
    category: "Monochrome (Carta)",
    inches: 6,
    width: 1072,
    height: 1448,
    ppi: 300,
    palette: "gray16",
    response: "carta",
    refresh: "~0.5 s full refresh",
    note: "Typical 6\" Carta reader, 16-level grayscale.",
  },
  {
    id: "remarkable-2",
    name: "reMarkable 2",
    category: "Monochrome (Carta)",
    inches: 10.3,
    width: 1404,
    height: 1872,
    ppi: 226,
    palette: "gray16",
    response: "carta",
    refresh: "~0.3 s, fast partial refresh",
    note: "10.3\" Carta note tablet, 226 ppi, 16-level grayscale.",
  },
  {
    id: "waveshare-7in5-mono",
    name: "Waveshare 7.5\" (mono)",
    category: "Monochrome (Carta)",
    inches: 7.5,
    width: 800,
    height: 480,
    ppi: 125,
    palette: "gray4",
    response: "carta",
    refresh: "~4 s full refresh",
    note: "Hobbyist SPI panel, 4-level grayscale, 800x480.",
  },
  {
    id: "waveshare-2in13-mono",
    name: "Waveshare 2.13\" (1-bit)",
    category: "Monochrome (Carta)",
    inches: 2.13,
    width: 250,
    height: 122,
    ppi: 122,
    palette: "mono1",
    response: "cartaMono",
    refresh: "~2 s full refresh",
    note: "Tiny 1-bit badge/label panel, pure black & white.",
  },

  // --- Color filter array (Kaleido 3) ---
  {
    id: "kobo-clara-colour",
    name: "Kobo Clara Colour",
    category: "Color CFA (Kaleido 3)",
    inches: 6,
    width: 1072,
    height: 1448,
    ppi: 300,
    colorPpi: 150,
    palette: "kaleido3",
    response: "kaleido3",
    refresh: "~0.5 s full refresh",
    note: "E Ink Kaleido 3: 4096 muted colors at 150 ppi over a 300 ppi mono base.",
  },
  {
    id: "kobo-libra-colour",
    name: "Kobo Libra Colour",
    category: "Color CFA (Kaleido 3)",
    inches: 7,
    width: 1264,
    height: 1680,
    ppi: 300,
    colorPpi: 150,
    palette: "kaleido3",
    response: "kaleido3",
    refresh: "~0.5 s full refresh",
    note: "7\" Kaleido 3, 300 ppi B/W, 150 ppi color.",
  },
  {
    id: "boox-go-color-7",
    name: "Boox Go Color 7",
    category: "Color CFA (Kaleido 3)",
    inches: 7,
    width: 1264,
    height: 1680,
    ppi: 300,
    colorPpi: 150,
    palette: "kaleido3",
    response: "kaleido3",
    refresh: "~0.4 s (fast modes available)",
    note: "7\" Kaleido 3 Android reader.",
  },

  // --- Advanced full color (Gallery 3) ---
  {
    id: "gallery3-8in",
    name: "E Ink Gallery 3 (8\")",
    category: "Full color (Gallery 3 / ACeP)",
    inches: 8,
    width: 1600,
    height: 1200,
    ppi: 300,
    palette: "gallery3",
    response: "gallery3",
    refresh: "0.35 s B/W / 1.5 s best color",
    note: "True ACeP (CMYW), 300 ppi, wide muted gamut.",
  },

  // --- Spectra 6 (E6) full-color ---
  {
    id: "waveshare-7in3-e6",
    name: "Waveshare 7.3\" Spectra 6",
    category: "6-color (Spectra 6 / E6)",
    inches: 7.3,
    width: 800,
    height: 480,
    ppi: 137,
    palette: "spectra6",
    response: "spectra6",
    refresh: "~25 s full refresh",
    note: "E Ink Spectra 6: black, white, red, yellow, green, blue.",
  },
  {
    id: "waveshare-4in-e6",
    name: "Waveshare 4\" Spectra 6",
    category: "6-color (Spectra 6 / E6)",
    inches: 4,
    width: 600,
    height: 400,
    ppi: 200,
    palette: "spectra6",
    response: "spectra6",
    refresh: "~19 s full refresh",
    note: "200 ppi E6 module for shelf labels.",
  },
  {
    id: "waveshare-13in3-e6",
    name: "Waveshare 13.3\" Spectra 6",
    category: "6-color (Spectra 6 / E6)",
    inches: 13.3,
    width: 1600,
    height: 1200,
    ppi: 150,
    palette: "spectra6",
    response: "spectra6",
    refresh: "~30 s full refresh",
    note: "Large-format E6 signage panel.",
  },

  // --- ACeP 7-color ---
  {
    id: "waveshare-5in65-acep",
    name: "Waveshare 5.65\" 7-color",
    category: "7-color (ACeP)",
    inches: 5.65,
    width: 600,
    height: 448,
    ppi: 134,
    palette: "acep7",
    response: "acep7",
    refresh: "~33 s full refresh",
    note: "Classic ACeP photo-frame panel: B/W/G/B/R/Y/orange.",
  },
  {
    id: "waveshare-7in3-acep",
    name: "Waveshare 7.3\" 7-color",
    category: "7-color (ACeP)",
    inches: 7.3,
    width: 800,
    height: 480,
    ppi: 137,
    palette: "acep7",
    response: "acep7",
    refresh: "~35 s full refresh",
    note: "800x480 ACeP 7-color photo frame.",
  },

  // --- Tri / four-color ESL ---
  {
    id: "waveshare-7in5-bwr",
    name: "Waveshare 7.5\" (B/W/R)",
    category: "ESL (3 & 4 color)",
    inches: 7.5,
    width: 800,
    height: 480,
    ppi: 125,
    palette: "bwr",
    response: "esl",
    refresh: "~26 s full refresh",
    note: "Black/white/red shelf-label panel.",
  },
  {
    id: "waveshare-7in5-bwry",
    name: "Waveshare 7.5\" (B/W/R/Y)",
    category: "ESL (3 & 4 color)",
    inches: 7.5,
    width: 800,
    height: 480,
    ppi: 125,
    palette: "bwry",
    response: "esl",
    refresh: "~22 s full refresh",
    note: "Black/white/red/yellow four-color panel.",
  },
  {
    id: "waveshare-2in9-bwr",
    name: "Waveshare 2.9\" (B/W/R)",
    category: "ESL (3 & 4 color)",
    inches: 2.9,
    width: 296,
    height: 128,
    ppi: 111,
    palette: "bwr",
    response: "esl",
    refresh: "~15 s full refresh",
    note: "Small tri-color electronic shelf label.",
  },
];

export function getDisplay(id) {
  return DISPLAYS.find((d) => d.id === id) ?? null;
}

export function getPalette(display) {
  return PALETTES[display.palette];
}

export function getResponse(display) {
  return RESPONSE[display.response];
}

// Distinct categories in catalog order, for grouping the picker.
export function displayCategories() {
  const seen = [];
  for (const d of DISPLAYS) {
    if (!seen.includes(d.category)) seen.push(d.category);
  }
  return seen;
}

export { RESPONSE };
