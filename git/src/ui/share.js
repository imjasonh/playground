/**
 * Share panel: turns the current deep-link URL into something you can hand to
 * another device — a scannable QR code plus a one-tap "copy link".
 *
 * The link is just `location.href`. The controller keeps the hash in sync with
 * the open repo / ref / file / line selection (see syncHash), so whatever the
 * URL says is exactly what a scanner will reopen. The QR itself is drawn on the
 * client with the dependency-free encoder in ../qrcode.js — no network, no
 * third-party image service (which matters for a tool that can browse private
 * repos).
 */
import { encodeQr } from '../qrcode.js';

const SVG_NS = 'http://www.w3.org/2000/svg';
// Quiet zone: the mandatory 4-module light border scanners rely on.
const QUIET = 4;

/**
 * Render a QR matrix into a crisp, scalable SVG element.
 *
 * @param {import('../qrcode.js').QrCode} qr
 * @returns {SVGElement}
 */
function buildQrSvg(qr) {
  const dim = qr.size + QUIET * 2;
  const svg = document.createElementNS(SVG_NS, 'svg');
  svg.setAttribute('viewBox', `0 0 ${dim} ${dim}`);
  svg.setAttribute('width', '100%');
  svg.setAttribute('height', '100%');
  svg.setAttribute('shape-rendering', 'crispEdges');
  svg.setAttribute('aria-hidden', 'true'); // the container carries the label

  const bg = document.createElementNS(SVG_NS, 'rect');
  bg.setAttribute('width', String(dim));
  bg.setAttribute('height', String(dim));
  bg.setAttribute('fill', '#ffffff');
  svg.appendChild(bg);

  // One path for every dark module keeps the DOM tiny even at higher versions.
  let d = '';
  for (let y = 0; y < qr.size; y += 1) {
    for (let x = 0; x < qr.size; x += 1) {
      if (qr.modules[y][x]) d += `M${x + QUIET} ${y + QUIET}h1v1h-1z`;
    }
  }
  const path = document.createElementNS(SVG_NS, 'path');
  path.setAttribute('d', d);
  path.setAttribute('fill', '#0d1117');
  svg.appendChild(path);
  return svg;
}

/**
 * @param {{dom: Record<string, HTMLElement>, toast: Function}} ctx
 */
export function createShare(ctx) {
  const { dom } = ctx;
  let returnFocus = null;

  function isOpen() {
    return !dom.shareOverlay.hidden;
  }

  function open() {
    const url = window.location.href;
    returnFocus = document.activeElement;
    dom.shareUrl.value = url;
    renderQr(url);
    dom.shareOverlay.hidden = false;
    dom.shareUrl.focus();
    dom.shareUrl.select();
  }

  function close() {
    if (!isOpen()) return;
    dom.shareOverlay.hidden = true;
    dom.shareQr.replaceChildren();
    if (returnFocus && typeof returnFocus.focus === 'function' && document.contains(returnFocus)) {
      returnFocus.focus();
    }
    returnFocus = null;
  }

  /** Draw (or, for an over-long link, gracefully skip) the QR code. */
  function renderQr(url) {
    // Prefer level M; fall back to L (more capacity) before giving up, so long
    // deep links still render when they can.
    let qr = null;
    for (const ecLevel of ['M', 'L']) {
      try {
        qr = encodeQr(url, { ecLevel });
        break;
      } catch {
        qr = null;
      }
    }
    if (!qr) {
      dom.shareQr.replaceChildren();
      dom.shareQr.removeAttribute('role');
      dom.shareQr.setAttribute('aria-hidden', 'true');
      dom.shareQr.classList.add('is-empty');
      dom.shareHint.textContent = 'This link is too long to show as a QR code — copy it instead.';
      return;
    }
    dom.shareQr.classList.remove('is-empty');
    dom.shareQr.setAttribute('role', 'img');
    dom.shareQr.setAttribute('aria-label', 'QR code linking to this view');
    dom.shareQr.replaceChildren(buildQrSvg(qr));
    dom.shareHint.textContent = 'Scan to open this repository, branch, and file on another device.';
  }

  async function copyLink() {
    const url = dom.shareUrl.value;
    try {
      await navigator.clipboard.writeText(url);
      ctx.toast('Link copied to clipboard', 'success');
    } catch {
      // Clipboard API can be unavailable (older browsers, insecure contexts).
      dom.shareUrl.focus();
      dom.shareUrl.select();
      let copied = false;
      try {
        copied = document.execCommand && document.execCommand('copy');
      } catch {
        copied = false;
      }
      ctx.toast(copied ? 'Link copied to clipboard' : 'Press Ctrl/Cmd + C to copy the link');
    }
  }

  dom.shareCopyBtn.addEventListener('click', copyLink);
  dom.shareCloseBtn.addEventListener('click', close);
  dom.shareOverlay.addEventListener('click', (e) => {
    if (e.target === dom.shareOverlay) close();
  });

  return { open, close, isOpen };
}
