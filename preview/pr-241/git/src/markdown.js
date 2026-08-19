/**
 * A small, dependency-free, fully-offline Markdown -> HTML renderer for the
 * viewer's preview mode.
 *
 * Safety is the priority: the source is treated as untrusted, so all text is
 * HTML-escaped and only a fixed set of tags is ever emitted. Raw HTML embedded
 * in the Markdown is escaped (shown literally), never passed through, and link
 * and image URLs are filtered to safe schemes — `javascript:`, `data:`, and the
 * like are dropped. The output is therefore safe to assign via `innerHTML`.
 *
 * Coverage is intentionally pragmatic (the common README subset): ATX headings,
 * bold/italic, inline and fenced/indented code, links, images, autolinks,
 * unordered/ordered lists, blockquotes, GitHub-style pipe tables, horizontal
 * rules, and paragraphs. It is not a full CommonMark implementation.
 *
 * Pure and dependency-free so it can be unit-tested without a DOM.
 */

const HTML_ESCAPES = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };

/** Escape the five HTML-significant characters. */
function escapeHtml(value) {
  return String(value).replace(/[&<>"']/g, (c) => HTML_ESCAPES[c]);
}

/**
 * Filter a URL to a safe scheme. Returns the URL for http(s)/mailto, relative
 * paths, and anchors; returns null for any other explicit scheme (so
 * `javascript:`, `data:`, `vbscript:`, … never reach an href/src).
 */
function safeUrl(url) {
  const u = String(url || '').trim();
  if (!u) return null;
  if (/^(https?:|mailto:)/i.test(u)) return u;
  if (/^[a-z][a-z0-9+.-]*:/i.test(u)) return null; // some other scheme — reject
  return u; // relative path, absolute path, anchor, or protocol-relative
}

// Private-use sentinels wrapping a store index, used to shield finished inline
// HTML (code/links/images) from the later escape + emphasis passes.
const PH_OPEN = '\u0000';
const PH_CLOSE = '\u0001';
const PH_RE = /\u0000(\d+)\u0001/g;

/** Render inline Markdown (within a single block) to safe HTML. */
function parseInline(input) {
  const store = [];
  const hold = (html) => {
    store.push(html);
    return `${PH_OPEN}${store.length - 1}${PH_CLOSE}`;
  };

  let s = String(input);

  // 1. Inline code spans (their contents are not further formatted).
  s = s.replace(/(`+)([\s\S]+?)\1/g, (_, _ticks, code) => hold(`<code>${escapeHtml(code.trim())}</code>`));

  // 2. Angle autolinks: <https://…> / <mailto:…>.
  s = s.replace(/<((?:https?|mailto):[^>\s]+)>/gi, (m, url) => {
    const safe = safeUrl(url);
    return safe ? hold(anchor(safe, escapeHtml(url))) : escapeHtml(m);
  });

  // 3. Images: ![alt](url "title").
  s = s.replace(/!\[([^\]]*)\]\(\s*([^)\s]+)(?:\s+"([^"]*)")?\s*\)/g, (m, alt, url, title) => {
    const safe = safeUrl(url);
    if (!safe) return hold(escapeHtml(alt));
    const t = title ? ` title="${escapeHtml(title)}"` : '';
    return hold(`<img src="${escapeHtml(safe)}" alt="${escapeHtml(alt)}"${t}>`);
  });

  // 4. Links: [text](url "title"). The text is parsed for emphasis/code.
  s = s.replace(/\[([^\]]+)\]\(\s*([^)\s]+)(?:\s+"([^"]*)")?\s*\)/g, (m, label, url, title) => {
    const safe = safeUrl(url);
    const inner = parseInline(label);
    if (!safe) return hold(inner); // drop the unsafe URL, keep the text
    const t = title ? ` title="${escapeHtml(title)}"` : '';
    return hold(anchor(safe, inner, t));
  });

  // 5. Escape everything that's left (placeholders survive — they're sentinels).
  s = escapeHtml(s);

  // 6. Emphasis. Bold before italic; require non-space at the delimiters so a
  //    lone `*` or snake_case identifier isn't mistaken for emphasis.
  s = s.replace(/\*\*(\S(?:[\s\S]*?\S)?)\*\*/g, '<strong>$1</strong>');
  s = s.replace(/__(\S(?:[\s\S]*?\S)?)__/g, '<strong>$1</strong>');
  s = s.replace(/\*(\S(?:[\s\S]*?\S)?)\*/g, '<em>$1</em>');
  s = s.replace(/(^|[^\w])_(\S(?:[\s\S]*?\S)?)_(?=[^\w]|$)/g, '$1<em>$2</em>');

  // 7. Restore the held inline HTML.
  return s.replace(PH_RE, (_, n) => store[Number(n)] ?? '');
}

function anchor(href, innerHtml, extraAttrs = '') {
  return `<a href="${escapeHtml(href)}" target="_blank" rel="noreferrer noopener"${extraAttrs}>${innerHtml}</a>`;
}

const FENCE_RE = /^(\s*)(`{3,}|~{3,})\s*([^`]*)$/;
const HEADING_RE = /^(#{1,6})\s+(.*?)\s*#*\s*$/;
const HR_RE = /^\s*([-*_])(\s*\1){2,}\s*$/;
const LIST_RE = /^\s*([-*+]|\d+[.)])\s+/;
const BLOCKQUOTE_RE = /^\s*>/;
const INDENT_CODE_RE = /^( {4}|\t)/;

function isBlank(line) {
  return /^\s*$/.test(line);
}

/** True when a line starts a new block (so paragraphs don't absorb it). */
function startsBlock(line) {
  return (
    FENCE_RE.test(line) ||
    HEADING_RE.test(line) ||
    HR_RE.test(line) ||
    BLOCKQUOTE_RE.test(line) ||
    LIST_RE.test(line)
  );
}

function isClosingFence(line, marker, len) {
  const re = marker === '`' ? /^\s*(`{3,})\s*$/ : /^\s*(~{3,})\s*$/;
  const m = re.exec(line);
  return Boolean(m && m[1].length >= len);
}

/** Split a table row into trimmed cells, tolerating optional edge pipes. */
function splitTableRow(row) {
  return row
    .trim()
    .replace(/^\|/, '')
    .replace(/\|$/, '')
    .split('|')
    .map((c) => c.trim());
}

function isTableDelimiter(line) {
  if (!line || line.indexOf('-') === -1) return false;
  const cells = splitTableRow(line);
  return cells.length > 0 && cells.every((c) => /^:?-+:?$/.test(c));
}

function alignmentOf(cell) {
  const left = cell.startsWith(':');
  const right = cell.endsWith(':');
  if (left && right) return 'center';
  if (right) return 'right';
  if (left) return 'left';
  return '';
}

function renderTable(headerLine, delimiterLine, bodyLines) {
  const aligns = splitTableRow(delimiterLine).map(alignmentOf);
  const cell = (tag, value, i) => {
    const align = aligns[i] ? ` style="text-align:${aligns[i]}"` : '';
    return `<${tag}${align}>${parseInline(value)}</${tag}>`;
  };
  const head = splitTableRow(headerLine).map((c, i) => cell('th', c, i)).join('');
  const rows = bodyLines
    .map((line) => `<tr>${splitTableRow(line).map((c, i) => cell('td', c, i)).join('')}</tr>`)
    .join('');
  return `<table><thead><tr>${head}</tr></thead><tbody>${rows}</tbody></table>`;
}

/** Join paragraph lines, honoring hard breaks (two trailing spaces -> <br>). */
function renderParagraph(lines) {
  let html = '';
  lines.forEach((line, idx) => {
    const hardBreak = /\s{2,}$/.test(line);
    html += parseInline(line.trim());
    if (idx < lines.length - 1) html += hardBreak ? '<br>' : ' ';
  });
  return `<p>${html}</p>`;
}

/**
 * Render a Markdown string to a safe HTML string.
 *
 * @param {string} src
 * @returns {string}
 */
export function renderMarkdown(src) {
  const lines = String(src == null ? '' : src).replace(/\r\n?/g, '\n').split('\n');
  const out = [];
  let i = 0;

  while (i < lines.length) {
    const line = lines[i];

    if (isBlank(line)) {
      i += 1;
      continue;
    }

    // Fenced code block.
    const fence = FENCE_RE.exec(line);
    if (fence) {
      const marker = fence[2][0];
      const len = fence[2].length;
      const lang = fence[3].trim().split(/\s+/)[0].replace(/[^\w.+-]/g, '');
      const buf = [];
      i += 1;
      while (i < lines.length && !isClosingFence(lines[i], marker, len)) {
        buf.push(lines[i]);
        i += 1;
      }
      i += 1; // consume the closing fence (if present)
      const cls = lang ? ` class="language-${lang}"` : '';
      out.push(`<pre><code${cls}>${escapeHtml(buf.join('\n'))}</code></pre>`);
      continue;
    }

    // ATX heading.
    const heading = HEADING_RE.exec(line);
    if (heading) {
      const level = heading[1].length;
      out.push(`<h${level}>${parseInline(heading[2])}</h${level}>`);
      i += 1;
      continue;
    }

    // Horizontal rule.
    if (HR_RE.test(line)) {
      out.push('<hr>');
      i += 1;
      continue;
    }

    // Blockquote (recursively rendered).
    if (BLOCKQUOTE_RE.test(line)) {
      const buf = [];
      while (i < lines.length && BLOCKQUOTE_RE.test(lines[i])) {
        buf.push(lines[i].replace(/^\s*>\s?/, ''));
        i += 1;
      }
      out.push(`<blockquote>${renderMarkdown(buf.join('\n'))}</blockquote>`);
      continue;
    }

    // GitHub-style pipe table (header row + delimiter row + body).
    if (line.indexOf('|') !== -1 && i + 1 < lines.length && isTableDelimiter(lines[i + 1])) {
      const header = line;
      const delimiter = lines[i + 1];
      i += 2;
      const body = [];
      while (i < lines.length && !isBlank(lines[i]) && lines[i].indexOf('|') !== -1) {
        body.push(lines[i]);
        i += 1;
      }
      out.push(renderTable(header, delimiter, body));
      continue;
    }

    // List (unordered or ordered); consecutive items, with indented
    // continuation lines folded into the preceding item.
    if (LIST_RE.test(line)) {
      const ordered = /^\s*\d+[.)]\s+/.test(line);
      const tag = ordered ? 'ol' : 'ul';
      const items = [];
      while (i < lines.length && LIST_RE.test(lines[i])) {
        let item = lines[i].replace(LIST_RE, '');
        i += 1;
        while (
          i < lines.length &&
          !isBlank(lines[i]) &&
          !LIST_RE.test(lines[i]) &&
          /^\s+\S/.test(lines[i])
        ) {
          item += ` ${lines[i].trim()}`;
          i += 1;
        }
        items.push(`<li>${parseInline(item)}</li>`);
      }
      out.push(`<${tag}>${items.join('')}</${tag}>`);
      continue;
    }

    // Indented code block (4 spaces / a tab).
    if (INDENT_CODE_RE.test(line)) {
      const buf = [];
      while (i < lines.length && (INDENT_CODE_RE.test(lines[i]) || isBlank(lines[i]))) {
        if (isBlank(lines[i])) {
          if (i + 1 < lines.length && INDENT_CODE_RE.test(lines[i + 1])) {
            buf.push('');
            i += 1;
            continue;
          }
          break;
        }
        buf.push(lines[i].replace(INDENT_CODE_RE, ''));
        i += 1;
      }
      out.push(`<pre><code>${escapeHtml(buf.join('\n'))}</code></pre>`);
      continue;
    }

    // Paragraph: gather until a blank line or the start of another block.
    const buf = [];
    while (i < lines.length && !isBlank(lines[i]) && !startsBlock(lines[i])) {
      buf.push(lines[i]);
      i += 1;
    }
    out.push(renderParagraph(buf));
  }

  return out.join('\n');
}
