// Renders the model's Markdown replies as sanitized HTML.

import DOMPurify from '../vendor/purify.es.mjs';
import {Marked} from '../vendor/marked.esm.js';

const marked = new Marked({gfm: true, async: false});

// A reply could otherwise send chat text off the device in a URL that loads as
// soon as it renders (an image, a CSS background), restyle the page, or show a
// form. index.html's Content-Security-Policy blocks the loads too. The native
// Sanitizer already drops scripts, event handlers, and `style`; these lists
// remove the extra elements and attributes this chat never renders.
const REMOVE_ELEMENTS = Object.freeze([
  'audio', 'button', 'form', 'img', 'input', 'picture', 'select', 'source',
  'style', 'textarea', 'track', 'video',
]);
const REMOVE_ATTRIBUTES = Object.freeze([
  'action', 'background', 'formaction', 'poster', 'srcset', 'style',
]);

// Fallback for browsers without the Sanitizer API; expresses the same denylist.
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
 * Renders `text` as Markdown into `target`, replacing its contents. The model's
 * output can repeat HTML from the prompt, so the HTML is sanitized first — with
 * the native Sanitizer API where available, otherwise DOMPurify. Where neither
 * can run, `target` gets plain text.
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
  hardenLinks(target);
}

/**
 * Opens rendered links in a new tab without handing the opener to the target.
 * @param {!Element} target
 */
function hardenLinks(target) {
  for (const link of target.querySelectorAll('a[href]')) {
    link.setAttribute('target', '_blank');
    link.setAttribute('rel', 'noopener noreferrer');
  }
}
