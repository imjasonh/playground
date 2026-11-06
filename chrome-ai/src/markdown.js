// Renders the model's Markdown replies as sanitized HTML.

import DOMPurify from '../vendor/purify.es.mjs';
import {Marked} from '../vendor/marked.esm.js';

const marked = new Marked({gfm: true, async: false});

// Tags that load a URL as soon as they render. A reply could otherwise send
// chat text off the device in an image URL.
const FORBID_TAGS = ['img', 'picture', 'source', 'video', 'audio', 'track'];

let linksHooked = false;

/**
 * Converts Markdown to unsanitized HTML.
 * @param {string} text
 * @return {string}
 */
export function markdownToHtml(text) {
  return marked.parse(text);
}

/**
 * Renders `text` as Markdown into `target`, replacing its contents. The
 * model's output can repeat HTML from the prompt, so the HTML goes through
 * DOMPurify first. Where DOMPurify can't run, `target` gets plain text.
 * @param {!Element} target
 * @param {string} text
 */
export function renderMarkdown(target, text) {
  if (!DOMPurify.isSupported) {
    target.textContent = text;
    return;
  }
  if (!linksHooked) {
    DOMPurify.addHook('afterSanitizeAttributes', (node) => {
      if (node.tagName === 'A' && node.hasAttribute('href')) {
        node.setAttribute('target', '_blank');
        node.setAttribute('rel', 'noopener noreferrer');
      }
    });
    linksHooked = true;
  }
  target.innerHTML = DOMPurify.sanitize(markdownToHtml(text), {FORBID_TAGS});
}
