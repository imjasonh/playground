import { raw as honoRaw } from "hono/html";

export const POST_MAX_CHARS = 260;

export function escapeHtml(s: string): string {
  return s
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;")
    .replace(/'/g, "&#39;");
}

export function escapeXml(s: string): string {
  return escapeHtml(s);
}

export function truncate(s: string, n: number): string {
  if (s.length <= n) return s;
  return s.slice(0, Math.max(0, n - 1)) + "…";
}

export function formatDate(unixSeconds: number): string {
  return new Date(unixSeconds * 1000).toISOString();
}

export function formatHuman(unixSeconds: number): string {
  const d = new Date(unixSeconds * 1000);
  return d.toUTCString();
}

export function imgUrl(siteUrl: string, key: string): string {
  const base = siteUrl.endsWith("/") ? siteUrl.slice(0, -1) : siteUrl;
  return `${base}/img/${key}`;
}

const VALID_IMAGE_TYPES = new Set([
  "image/jpeg",
  "image/png",
  "image/gif",
  "image/webp",
  "image/avif",
]);

export function imageExtFor(contentType: string): string | null {
  switch (contentType) {
    case "image/jpeg":
      return "jpg";
    case "image/png":
      return "png";
    case "image/gif":
      return "gif";
    case "image/webp":
      return "webp";
    case "image/avif":
      return "avif";
    default:
      return null;
  }
}

export function isAllowedImageType(t: string): boolean {
  return VALID_IMAGE_TYPES.has(t);
}

// Loose RFC-5322 sanity check; defer real validation to the confirm flow.
export function isValidEmail(s: string): boolean {
  if (s.length > 254) return false;
  return /^[^\s@]+@[^\s@.]+\.[^\s@]+$/.test(s);
}

export interface YouTubeRef {
  id: string;
  start?: number; // seconds
}

const YT_ID_RE = /^[A-Za-z0-9_-]{6,15}$/;
const URL_RE = /https?:\/\/[^\s<>"'`]+/g;

// Find the first parseable YouTube URL in `text` and extract its video id
// + optional start time. Supports youtu.be/<id>, youtube.com/watch?v=<id>,
// /shorts/<id>, /embed/<id>, and the youtube-nocookie variants.
export function extractYouTubeRef(text: string): YouTubeRef | null {
  URL_RE.lastIndex = 0;
  let m: RegExpExecArray | null;
  while ((m = URL_RE.exec(text)) !== null) {
    let u: URL;
    try {
      u = new URL(m[0]);
    } catch {
      continue;
    }
    const ref = parseYouTubeUrl(u);
    if (ref) return ref;
  }
  return null;
}

function parseYouTubeUrl(u: URL): YouTubeRef | null {
  const host = u.hostname.replace(/^(www\.|m\.)/, "");
  let id: string | null = null;

  if (host === "youtu.be") {
    id = u.pathname.slice(1).split("/")[0] || null;
  } else if (host === "youtube.com" || host === "youtube-nocookie.com") {
    if (u.pathname === "/watch") {
      id = u.searchParams.get("v");
    } else if (
      u.pathname.startsWith("/shorts/") ||
      u.pathname.startsWith("/embed/") ||
      u.pathname.startsWith("/v/")
    ) {
      id = u.pathname.split("/")[2] ?? null;
    }
  }

  if (!id || !YT_ID_RE.test(id)) return null;

  const startStr = u.searchParams.get("t") ?? u.searchParams.get("start");
  let start: number | undefined;
  if (startStr) {
    // Allow "30", "30s", "1m30s" — strip non-digits as a forgiving cap.
    const seconds = parseTimestamp(startStr);
    if (seconds && seconds > 0) start = seconds;
  }
  return start === undefined ? { id } : { id, start };
}

function parseTimestamp(s: string): number | null {
  if (/^\d+$/.test(s)) return parseInt(s, 10);
  // 1h2m3s / 2m3s / 3s
  const re = /^(?:(\d+)h)?(?:(\d+)m)?(?:(\d+)s)?$/;
  const m = re.exec(s);
  if (!m) return null;
  const h = parseInt(m[1] ?? "0", 10);
  const min = parseInt(m[2] ?? "0", 10);
  const sec = parseInt(m[3] ?? "0", 10);
  const total = h * 3600 + min * 60 + sec;
  return total > 0 ? total : null;
}

export function youtubeEmbedSrc(ref: YouTubeRef): string {
  const base = `https://www.youtube-nocookie.com/embed/${ref.id}`;
  return ref.start ? `${base}?start=${ref.start}` : base;
}

export function youtubeThumbnailUrl(ref: YouTubeRef): string {
  return `https://img.youtube.com/vi/${ref.id}/hqdefault.jpg`;
}

// Trailing chars commonly mistaken for part of a URL ("see https://x.com.").
const TRAILING_PUNCT_RE = /[.,;:!?)\]}>'"`]+$/;

// Match, in priority order: a ``` fenced block ```, a `code span`, a
// bare http(s) URL. Fences first so ``` isn't taken as inline code;
// inline code before URLs so a URL in backticks stays code, not a link.
const SPAN_RE = /(```[\s\S]*?```)|(`[^`]+`)|(https?:\/\/[^\s<>"'`]+)/g;

// Render a post body: ```fenced blocks``` become <pre><code>, `inline
// code` becomes <code>, bare http(s) URLs become <a>, everything else
// is HTML-escaped. Returned as HtmlEscapedString so it survives html``
// interpolation. Note: the result may contain block-level <pre>, so
// callers must put it in a <div>, not a <p>.
export function linkifyBody(body: string) {
  SPAN_RE.lastIndex = 0;
  const out: string[] = [];
  let lastIndex = 0;
  let m: RegExpExecArray | null;
  while ((m = SPAN_RE.exec(body)) !== null) {
    if (m.index > lastIndex) {
      out.push(escapeHtml(body.slice(lastIndex, m.index)));
    }
    if (m[1] !== undefined) {
      const inner = m[1]
        .slice(3, -3)
        .replace(/^[ \t]*\r?\n/, "")
        .replace(/\r?\n[ \t]*$/, "");
      out.push(`<pre><code>${escapeHtml(inner)}</code></pre>`);
    } else if (m[2] !== undefined) {
      out.push(`<code>${escapeHtml(m[2].slice(1, -1))}</code>`);
    } else {
      let url = m[3];
      const tm = TRAILING_PUNCT_RE.exec(url);
      let trailing = "";
      if (tm) {
        trailing = tm[0];
        url = url.slice(0, -trailing.length);
      }
      const escaped = escapeHtml(url);
      out.push(`<a href="${escaped}" rel="noopener noreferrer">${escaped}</a>`);
      if (trailing) out.push(escapeHtml(trailing));
    }
    lastIndex = m.index + m[0].length;
  }
  if (lastIndex < body.length) out.push(escapeHtml(body.slice(lastIndex)));
  return honoRaw(out.join(""));
}
