/**
 * Lightweight canvas confetti — no dependencies.
 * Paper-palette spray for when a spiral is solved.
 */

const COLORS = ["#c01818", "#111111", "#f7f4ef", "#8b1a1a", "#d4a017", "#444444"];

/**
 * @typedef {{
 *   x: number,
 *   y: number,
 *   vx: number,
 *   vy: number,
 *   w: number,
 *   h: number,
 *   rot: number,
 *   vr: number,
 *   color: string,
 *   life: number,
 * }} Particle
 */

/** @type {HTMLCanvasElement | null} */
let canvas = null;
/** @type {CanvasRenderingContext2D | null} */
let ctx = null;
/** @type {Particle[]} */
let particles = [];
/** @type {number | null} */
let raf = null;

function prefersReducedMotion() {
  return (
    typeof matchMedia === "function" &&
    matchMedia("(prefers-reduced-motion: reduce)").matches
  );
}

function ensureCanvas() {
  if (canvas) return;
  canvas = document.createElement("canvas");
  canvas.className = "confetti-layer";
  canvas.setAttribute("aria-hidden", "true");
  Object.assign(canvas.style, {
    position: "fixed",
    inset: "0",
    width: "100%",
    height: "100%",
    pointerEvents: "none",
    zIndex: "9999",
  });
  document.body.appendChild(canvas);
  ctx = canvas.getContext("2d");
  resize();
  window.addEventListener("resize", resize);
}

function resize() {
  if (!canvas) return;
  const dpr = Math.min(window.devicePixelRatio || 1, 2);
  canvas.width = Math.floor(window.innerWidth * dpr);
  canvas.height = Math.floor(window.innerHeight * dpr);
  if (ctx) ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
}

function stop() {
  if (raf != null) {
    cancelAnimationFrame(raf);
    raf = null;
  }
  particles = [];
  if (ctx && canvas) {
    ctx.clearRect(0, 0, window.innerWidth, window.innerHeight);
  }
  if (canvas) {
    canvas.remove();
    canvas = null;
    ctx = null;
    window.removeEventListener("resize", resize);
  }
}

/**
 * @param {number} originX
 * @param {number} originY
 * @param {number} count
 */
function spawn(originX, originY, count) {
  for (let i = 0; i < count; i += 1) {
    const angle = -Math.PI / 2 + (Math.random() - 0.5) * Math.PI * 1.35;
    const speed = 6 + Math.random() * 11;
    particles.push({
      x: originX + (Math.random() - 0.5) * 24,
      y: originY + (Math.random() - 0.5) * 16,
      vx: Math.cos(angle) * speed,
      vy: Math.sin(angle) * speed - (2 + Math.random() * 4),
      w: 4 + Math.random() * 5,
      h: 6 + Math.random() * 8,
      rot: Math.random() * Math.PI * 2,
      vr: (Math.random() - 0.5) * 0.45,
      color: COLORS[(Math.random() * COLORS.length) | 0],
      life: 1,
    });
  }
}

function tick() {
  if (!ctx || !canvas) return;
  const w = window.innerWidth;
  const h = window.innerHeight;
  ctx.clearRect(0, 0, w, h);

  const next = [];
  for (const p of particles) {
    p.vy += 0.22;
    p.vx *= 0.992;
    p.x += p.vx;
    p.y += p.vy;
    p.rot += p.vr;
    p.life -= 0.006;
    if (p.life <= 0 || p.y > h + 40) continue;

    ctx.save();
    ctx.translate(p.x, p.y);
    ctx.rotate(p.rot);
    ctx.globalAlpha = Math.max(0, Math.min(1, p.life * 1.2));
    ctx.fillStyle = p.color;
    ctx.fillRect(-p.w / 2, -p.h / 2, p.w, p.h);
    ctx.restore();
    next.push(p);
  }
  particles = next;

  if (particles.length === 0) {
    stop();
    return;
  }
  raf = requestAnimationFrame(tick);
}

/**
 * Spray confetti from the center of `originEl`, or the viewport center.
 * No-ops when the user prefers reduced motion.
 * @param {Element | null} [originEl]
 */
export function celebrate(originEl = null) {
  if (typeof document === "undefined") return;
  if (prefersReducedMotion()) return;

  ensureCanvas();
  let originX = window.innerWidth / 2;
  let originY = window.innerHeight * 0.32;
  if (originEl) {
    const box = originEl.getBoundingClientRect();
    originX = box.left + box.width / 2;
    originY = box.top + box.height / 2;
  }

  // Fresh burst; if one is already running, pile on.
  spawn(originX, originY, 180);
  // Second delayed pop for a fuller spray.
  window.setTimeout(() => {
    if (!canvas) return;
    spawn(originX, originY, 120);
  }, 160);
  window.setTimeout(() => {
    if (!canvas) return;
    spawn(originX + (Math.random() - 0.5) * 80, originY - 20, 70);
  }, 320);

  if (raf == null) raf = requestAnimationFrame(tick);
}

/** Stop and tear down any running celebration (e.g. on new puzzle). */
export function clearCelebration() {
  stop();
}
