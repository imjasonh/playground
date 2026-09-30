/**
 * Shared DOM primitives and user-feedback helpers.
 *
 * Everything here is intentionally free of app state so every UI module can
 * depend on it without creating cycles. The feedback factory binds the toast,
 * clone-progress, and clone-error helpers to their elements once, so the rest
 * of the app shares a single implementation.
 */

/** Element by id. */
export const $ = (id) => document.getElementById(id);

/** Create an element with an optional class name and text content. */
export function el(tag, className, text) {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text != null) node.textContent = text;
  return node;
}

/** kebab-case id -> camelCase property key. */
export function camel(id) {
  return id.replace(/-([a-z])/g, (_, c) => c.toUpperCase());
}

/** Build a cache of elements keyed by the camelCased form of each id. */
export function cacheDom(ids) {
  const dom = {};
  for (const id of ids) dom[camel(id)] = $(id);
  return dom;
}

/** Trailing-edge debounce. */
export function debounce(fn, ms) {
  let timer = null;
  return (...args) => {
    clearTimeout(timer);
    timer = setTimeout(() => fn(...args), ms);
  };
}

/**
 * Toast / clone-progress / clone-error helpers, bound to their elements.
 *
 * @param {Record<string, HTMLElement>} dom  the cached element map
 */
export function createFeedback(dom) {
  let toastTimer = null;

  function toast(message, type) {
    dom.toast.textContent = message;
    dom.toast.className = `toast${type ? ` ${type}` : ''}`;
    dom.toast.hidden = false;
    clearTimeout(toastTimer);
    toastTimer = setTimeout(hideToast, 3200);
  }
  function hideToast() {
    dom.toast.hidden = true;
  }

  function showProgress(label, pct) {
    dom.cloneProgress.hidden = false;
    if (typeof pct === 'number') {
      dom.progressFill.style.width = `${pct}%`;
    }
    dom.progressLabel.textContent = pct != null ? `${label} ${pct}%` : label;
  }
  function hideProgress() {
    dom.cloneProgress.hidden = true;
    dom.progressFill.style.width = '0%';
  }

  function showError(message) {
    dom.cloneError.textContent = message;
    dom.cloneError.hidden = false;
  }
  function hideError() {
    dom.cloneError.hidden = true;
  }

  return { toast, hideToast, showProgress, hideProgress, showError, hideError };
}
