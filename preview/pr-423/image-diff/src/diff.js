// Pixel compare + alignment. Pure functions so Node can test them
// without a canvas. The browser decodes files and then calls compareImages.

export const MAX_EDGE = 4096;

// Relative aspect gap under this is treated as the same shape, so we
// scale to the larger image instead of inventing a compromise canvas.
const ASPECT_EPSILON = 0.01;

const CROP_EPSILON = 0.5;

// Count a pixel as "different" once it moves more than two raw channel
// units. JPEG noise still tints, but the percentage ignores it.
const DIFFERS_AT = 2 / (255 * 2);

export function createImage(width, height) {
  return {
    width,
    height,
    data: new Uint8ClampedArray(width * height * 4),
  };
}

export function clamp(value, lo, hi) {
  if (value < lo) {
    return lo;
  }
  if (value > hi) {
    return hi;
  }
  return value;
}

export function pixelDistance(r1, g1, b1, a1, r2, g2, b2, a2) {
  const dr = r1 - r2;
  const dg = g1 - g2;
  const db = b1 - b2;
  const da = a1 - a2;
  return Math.sqrt(dr * dr + dg * dg + db * db + da * da) / (255 * 2);
}

export function tintPixel(r, g, b, t) {
  const keep = 1 - t;
  return [r * keep + 255 * t, g * keep, b * keep];
}

export function fitMaxEdge(width, height, maxEdge = MAX_EDGE) {
  const long = Math.max(width, height);
  if (long <= maxEdge) {
    return { width, height };
  }
  const scale = maxEdge / long;
  return {
    width: Math.max(1, Math.round(width * scale)),
    height: Math.max(1, Math.round(height * scale)),
  };
}

export function comparisonSize(a, b, maxEdge = MAX_EDGE) {
  const aspectA = a.width / a.height;
  const aspectB = b.width / b.height;
  const relativeGap =
    Math.abs(aspectA - aspectB) / Math.max(aspectA, aspectB);
  const aspectClose = relativeGap < ASPECT_EPSILON;

  if (aspectClose) {
    const larger = a.width * a.height >= b.width * b.height ? a : b;
    const fitted = fitMaxEdge(larger.width, larger.height, maxEdge);
    return { ...fitted, aspectClose: true };
  }

  const aspect = Math.sqrt(aspectA * aspectB);
  const long = Math.min(maxEdge, Math.max(a.width, a.height, b.width, b.height));
  let width;
  let height;
  if (aspect >= 1) {
    width = long;
    height = Math.max(1, Math.round(width / aspect));
  } else {
    height = long;
    width = Math.max(1, Math.round(height * aspect));
  }
  return { width, height, aspectClose: false };
}

export function coverPlacement(srcW, srcH, dstW, dstH) {
  const scale = Math.max(dstW / srcW, dstH / srcH);
  const drawW = srcW * scale;
  const drawH = srcH * scale;
  return {
    x: (dstW - drawW) / 2,
    y: (dstH - drawH) / 2,
    width: drawW,
    height: drawH,
    scale,
  };
}

export function sourceCropRect(srcW, srcH, dstW, dstH) {
  const placed = coverPlacement(srcW, srcH, dstW, dstH);
  return {
    x: Math.max(0, -placed.x / placed.scale),
    y: Math.max(0, -placed.y / placed.scale),
    width: dstW / placed.scale,
    height: dstH / placed.scale,
  };
}

export function wasCropped(src, crop) {
  return (
    crop.width + CROP_EPSILON < src.width ||
    crop.height + CROP_EPSILON < src.height
  );
}

export function containLayout(boxW, boxH, imgW, imgH) {
  const scale = Math.min(boxW / imgW, boxH / imgH);
  const width = imgW * scale;
  const height = imgH * scale;
  return {
    x: (boxW - width) / 2,
    y: (boxH - height) / 2,
    width,
    height,
    scale,
  };
}

export function cropOverlay(boxW, boxH, imgW, imgH, crop) {
  const laid = containLayout(boxW, boxH, imgW, imgH);
  return {
    x: laid.x + crop.x * laid.scale,
    y: laid.y + crop.y * laid.scale,
    width: crop.width * laid.scale,
    height: crop.height * laid.scale,
  };
}

function readPixel(img, x, y) {
  const xi = clamp(Math.floor(x), 0, img.width - 1);
  const yi = clamp(Math.floor(y), 0, img.height - 1);
  const i = (yi * img.width + xi) * 4;
  return [img.data[i], img.data[i + 1], img.data[i + 2], img.data[i + 3]];
}

export function sampleBilinear(img, x, y) {
  const x0 = Math.floor(x);
  const y0 = Math.floor(y);
  const tx = x - x0;
  const ty = y - y0;
  const p00 = readPixel(img, x0, y0);
  const p10 = readPixel(img, x0 + 1, y0);
  const p01 = readPixel(img, x0, y0 + 1);
  const p11 = readPixel(img, x0 + 1, y0 + 1);
  const out = [0, 0, 0, 0];
  for (let c = 0; c < 4; c += 1) {
    const top = p00[c] * (1 - tx) + p10[c] * tx;
    const bot = p01[c] * (1 - tx) + p11[c] * tx;
    out[c] = top * (1 - ty) + bot * ty;
  }
  return out;
}

export function sampleCover(src, dstW, dstH) {
  const placed = coverPlacement(src.width, src.height, dstW, dstH);
  const out = createImage(dstW, dstH);
  for (let y = 0; y < dstH; y += 1) {
    for (let x = 0; x < dstW; x += 1) {
      const sx = (x + 0.5 - placed.x) / placed.scale - 0.5;
      const sy = (y + 0.5 - placed.y) / placed.scale - 0.5;
      const [r, g, b, a] = sampleBilinear(src, sx, sy);
      const i = (y * dstW + x) * 4;
      out.data[i] = r;
      out.data[i + 1] = g;
      out.data[i + 2] = b;
      out.data[i + 3] = a;
    }
  }
  return out;
}

export function diffAligned(a, b) {
  if (a.width !== b.width || a.height !== b.height) {
    throw new Error("diffAligned expects matching sizes");
  }
  const { width, height } = a;
  const out = createImage(width, height);
  let sum = 0;
  let maxDiff = 0;
  let differingPixels = 0;
  const totalPixels = width * height;

  for (let i = 0; i < a.data.length; i += 4) {
    const t = pixelDistance(
      a.data[i],
      a.data[i + 1],
      a.data[i + 2],
      a.data[i + 3],
      b.data[i],
      b.data[i + 1],
      b.data[i + 2],
      b.data[i + 3],
    );
    sum += t;
    if (t > maxDiff) {
      maxDiff = t;
    }
    if (t > DIFFERS_AT) {
      differingPixels += 1;
    }
    const avgR = (a.data[i] + b.data[i]) / 2;
    const avgG = (a.data[i + 1] + b.data[i + 1]) / 2;
    const avgB = (a.data[i + 2] + b.data[i + 2]) / 2;
    const avgA = (a.data[i + 3] + b.data[i + 3]) / 2;
    const [r, g, bl] = tintPixel(avgR, avgG, avgB, t);
    out.data[i] = r;
    out.data[i + 1] = g;
    out.data[i + 2] = bl;
    out.data[i + 3] = avgA;
  }

  return {
    image: out,
    meanDiff: sum / totalPixels,
    maxDiff,
    differingPixels,
    totalPixels,
    differingFraction: differingPixels / totalPixels,
  };
}

export function compareImages(a, b, maxEdge = MAX_EDGE) {
  const size = comparisonSize(a, b, maxEdge);
  const alignedA = sampleCover(a, size.width, size.height);
  const alignedB = sampleCover(b, size.width, size.height);
  const diff = diffAligned(alignedA, alignedB);
  const cropA = sourceCropRect(a.width, a.height, size.width, size.height);
  const cropB = sourceCropRect(b.width, b.height, size.width, size.height);
  return {
    ...diff,
    width: size.width,
    height: size.height,
    aspectClose: size.aspectClose,
    cropA,
    cropB,
    croppedA: wasCropped(a, cropA),
    croppedB: wasCropped(b, cropB),
    scaledA: a.width !== size.width || a.height !== size.height,
    scaledB: b.width !== size.width || b.height !== size.height,
  };
}

function formatPercent(fraction) {
  if (fraction <= 0) {
    return "0%";
  }
  if (fraction < 0.001) {
    return "<0.1%";
  }
  if (fraction < 0.1) {
    return `${(fraction * 100).toFixed(1)}%`;
  }
  return `${Math.round(fraction * 100)}%`;
}

export function formatDimensions(width, height) {
  return `${width}\u00d7${height}`;
}

export function describeCompare(result, a, b) {
  const sizes = `A ${formatDimensions(a.width, a.height)} \u00b7 B ${formatDimensions(b.width, b.height)}`;
  const compared = `Compared ${formatDimensions(result.width, result.height)}`;

  let fit = compared;
  if (result.croppedA && result.croppedB) {
    fit = `${compared} after center-cropping both images`;
  } else if (result.croppedA) {
    fit = `${compared} after center-cropping A`;
  } else if (result.croppedB) {
    fit = `${compared} after center-cropping B`;
  } else if (result.scaledA || result.scaledB) {
    fit = `${compared}, scaled to match`;
  }

  let verdict;
  if (result.differingPixels === 0) {
    verdict = "Images match.";
  } else {
    verdict = `${formatPercent(result.differingFraction)} of pixels differ.`;
  }

  return `${sizes}. ${fit}. ${verdict}`;
}
