// Display-aware photo conversion presets for e-ink panels.
// Kept pure (no DOM) so presets can be unit-tested against the catalog and
// dithering engine.

export function paletteCategory(palette) {
  if (palette.kind === "list") return "discrete-color";
  if (palette.grayscale) return "monochrome";
  return "continuous-color";
}

const PRESETS_BY_CATEGORY = {
  // Spectra 6, ACeP 7-color, and 3/4-color ESL panels.
  "discrete-color": [
    {
      id: "photopainter",
      label: "PhotoPainter",
      description:
        "Inspired by PhotoPainter Spectra 6: Atkinson dithering with hue-prioritized RGB+Luma matching, contrast/saturation lift, and sharpening.",
      dither: {
        method: "atkinson",
        serpentine: true,
        colorMetric: "photopainter",
        linearLight: false,
      },
      adjust: {
        saturation: 1.2,
        contrast: 1.2,
        brightness: 1.1,
        gamma: 1,
        sharpen: 0.6,
        autoLevels: false,
      },
    },
    {
      id: "perceptual-oklab",
      label: "Perceptual (Oklab)",
      description:
        "Oklab perceptual matching with linear-light Floyd–Steinberg diffusion for accurate skies, foliage, and skin tones.",
      dither: {
        method: "floyd-steinberg",
        serpentine: true,
        colorMetric: "oklab",
        linearLight: true,
      },
      adjust: {
        saturation: 1.4,
        contrast: 1.15,
        brightness: 1.05,
        gamma: 1,
        sharpen: 0.4,
        autoLevels: false,
      },
    },
    {
      id: "yliluoma-ordered",
      label: "Yliluoma ordered",
      description:
        "Arbitrary-palette positional dithering with Oklab color matching — clean color mixing without error-diffusion smearing.",
      dither: {
        method: "yliluoma",
        serpentine: true,
        colorMetric: "oklab",
        linearLight: false,
      },
      adjust: {
        saturation: 1.35,
        contrast: 1.15,
        brightness: 1.05,
        gamma: 1,
        sharpen: 0.4,
        autoLevels: false,
      },
    },
    {
      id: "blue-noise-color",
      label: "Blue noise",
      description:
        "Isotropic 64×64 void-and-cluster blue noise with Oklab matching for a natural film-grain texture.",
      dither: {
        method: "blue-noise",
        serpentine: true,
        colorMetric: "oklab",
        linearLight: false,
      },
      adjust: {
        saturation: 1.35,
        contrast: 1.15,
        brightness: 1.05,
        gamma: 1,
        sharpen: 0.4,
        autoLevels: false,
      },
    },
  ],

  // Kaleido 3 (CFA) and Gallery 3 (continuous ACeP).
  "continuous-color": [
    {
      id: "vivid-photo",
      label: "Vivid photo",
      description:
        "Compensates for muted CFA / ACeP inks with Ostromoukhov diffusion and a saturation/sharpen lift.",
      dither: {
        method: "ostromoukhov",
        serpentine: true,
        linearLight: false,
      },
      adjust: {
        saturation: 1.65,
        contrast: 1.15,
        brightness: 1.05,
        gamma: 1,
        sharpen: 0.4,
        autoLevels: false,
      },
    },
    {
      id: "blue-noise-cfa",
      label: "Smooth (Blue noise)",
      description:
        "Organic blue-noise dithering with moderate saturation boost for soft tonal transitions.",
      dither: {
        method: "blue-noise",
        serpentine: true,
        linearLight: false,
      },
      adjust: {
        saturation: 1.5,
        contrast: 1.1,
        brightness: 1.02,
        gamma: 1,
        sharpen: 0.3,
        autoLevels: false,
      },
    },
    {
      id: "neutral-color",
      label: "Neutral",
      description:
        "Unadjusted source colors with standard Floyd–Steinberg dithering.",
      dither: {
        method: "floyd-steinberg",
        serpentine: true,
        linearLight: false,
      },
      adjust: {
        saturation: 1,
        contrast: 1,
        brightness: 1,
        gamma: 1,
        sharpen: 0,
        autoLevels: false,
      },
    },
  ],

  // Monochrome Carta (1-bit, 4-gray, 16-gray).
  monochrome: [
    {
      id: "bw-ostromoukhov",
      label: "B&W photo",
      description:
        "Ostromoukhov variable-coefficient error diffusion in linear light with auto-levels and sharpening — eliminates midtone worms.",
      dither: {
        method: "ostromoukhov",
        serpentine: true,
        grayMode: "luma",
        linearLight: true,
      },
      adjust: {
        saturation: 1,
        contrast: 1.15,
        brightness: 1,
        gamma: 1,
        sharpen: 0.45,
        autoLevels: true,
      },
    },
    {
      id: "bw-blue-noise",
      label: "Blue noise",
      description:
        "64×64 void-and-cluster blue-noise stippling in linear light for smooth, isotropic film-grain halftones.",
      dither: {
        method: "blue-noise",
        serpentine: true,
        grayMode: "luma",
        linearLight: true,
      },
      adjust: {
        saturation: 1,
        contrast: 1.15,
        brightness: 1,
        gamma: 1,
        sharpen: 0.4,
        autoLevels: true,
      },
    },
    {
      id: "bw-riemersma",
      label: "Hilbert stipple",
      description:
        "Riemersma Hilbert-curve error diffusion in linear light — zero scanline artifacts.",
      dither: {
        method: "riemersma",
        serpentine: true,
        grayMode: "luma",
        linearLight: true,
      },
      adjust: {
        saturation: 1,
        contrast: 1.15,
        brightness: 1,
        gamma: 1,
        sharpen: 0.4,
        autoLevels: true,
      },
    },
    {
      id: "bw-atkinson",
      label: "Classic 1-bit",
      description:
        "Crisp Atkinson dithering with an orange B&W filter for high-contrast portraits and dramatic skies.",
      dither: {
        method: "atkinson",
        serpentine: true,
        grayMode: "orange",
        linearLight: false,
      },
      adjust: {
        saturation: 1,
        contrast: 1.2,
        brightness: 1.05,
        gamma: 1,
        sharpen: 0.5,
        autoLevels: true,
      },
    },
    {
      id: "bw-document",
      label: "Crisp document",
      description:
        "No dithering, lifted contrast, and light sharpening for clean text and line art.",
      dither: {
        method: "none",
        serpentine: true,
        grayMode: "luma",
        linearLight: false,
      },
      adjust: {
        saturation: 1,
        contrast: 1.2,
        brightness: 1,
        gamma: 1,
        sharpen: 0.3,
        autoLevels: false,
      },
    },
  ],
};

export function presetsForPalette(palette) {
  return PRESETS_BY_CATEGORY[paletteCategory(palette)];
}

export function getPreset(palette, id) {
  return presetsForPalette(palette).find((p) => p.id === id) ?? null;
}

export function autoBoostForPalette(palette) {
  const cat = paletteCategory(palette);
  if (cat === "monochrome") {
    return {
      saturation: 1,
      contrast: 1.15,
      brightness: 1.02,
      gamma: 1,
      sharpen: 0.45,
      autoLevels: true,
    };
  }
  if (cat === "discrete-color") {
    return {
      saturation: 1.25,
      contrast: 1.2,
      brightness: 1.08,
      gamma: 1,
      sharpen: 0.55,
      autoLevels: false,
    };
  }
  return {
    saturation: 1.7,
    contrast: 1.15,
    brightness: 1.02,
    gamma: 1,
    sharpen: 0.35,
    autoLevels: false,
  };
}
