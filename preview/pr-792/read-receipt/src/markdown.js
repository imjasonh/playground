// Renders pasted Markdown as sanitized HTML.

import DOMPurify from '../vendor/purify.es.mjs';
import {Marked} from '../vendor/marked.esm.js';

/**
 * Escapes text for use in HTML text and double-quoted attribute values.
 * @param {string} text
 * @return {string}
 */
function escapeHtml(text) {
  return text.replace(/[&<>"']/g, (c) => `&#${c.charCodeAt(0)};`);
}

// A shared link renders someone else's Markdown, and an image would load from
// a host they chose as soon as the page opens, which tells that host who read
// the doc. Images render as links to the image instead.
const marked = new Marked({
  gfm: true,
  async: false,
  renderer: {
    image({href, text}) {
      return `<a href="${escapeHtml(href)}">${escapeHtml(text || href)}</a>`;
    },
  },
});

// The native Sanitizer already drops scripts, event handlers, and `style`.
// These lists also remove anything that loads a URL, takes input, or restyles
// the page. `id` and `name` go too, so the doc can't shadow the app's own
// elements.
const REMOVE_ELEMENTS = Object.freeze([
  'audio', 'button', 'form', 'iframe', 'img', 'input', 'picture', 'select',
  'source', 'style', 'textarea', 'track', 'video',
]);
const REMOVE_ATTRIBUTES = Object.freeze([
  'action', 'background', 'formaction', 'id', 'name', 'poster', 'srcset',
  'style',
]);

// Fallback for browsers without the Sanitizer API; the same denylist.
const SANITIZE = Object.freeze({
  USE_PROFILES: {html: true},
  FORBID_TAGS: REMOVE_ELEMENTS,
  FORBID_ATTR: REMOVE_ATTRIBUTES,
});

// Guarded for the Node test runner, where there is no `Element`.
const SUPPORTS_SET_HTML =
  typeof Element !== 'undefined' && 'setHTML' in Element.prototype;

/**
 * Converts Markdown to unsanitized HTML.
 * @param {string} text
 * @return {string}
 */
export function markdownToHtml(text) {
  return marked.parse(text);
}

/**
 * Renders `text` as Markdown into `target`, replacing its contents. The HTML
 * goes through the native Sanitizer API where available, otherwise DOMPurify.
 * Where neither can run, `target` gets plain text.
 * @param {!Element} target
 * @param {string} text
 */
export function renderMarkdown(target, text) {
  const html = markdownToHtml(text);
  if (SUPPORTS_SET_HTML) {
    // The default sanitizer is XSS-safe and can only be made stricter, so this
    // never widens what renders.
    target.setHTML(html, {
      sanitizer: {
        removeElements: REMOVE_ELEMENTS,
        removeAttributes: REMOVE_ATTRIBUTES,
      },
    });
  } else if (DOMPurify.isSupported) {
    target.innerHTML = DOMPurify.sanitize(html, SANITIZE);
  } else {
    target.textContent = text;
    return;
  }
  for (const link of target.querySelectorAll('a[href]')) {
    link.setAttribute('target', '_blank');
    link.setAttribute('rel', 'noopener noreferrer');
  }
  // Every word has to be on screen to be clicked.
  for (const details of target.querySelectorAll('details')) {
    details.open = true;
  }
}
