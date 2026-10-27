import { writeClipboard } from "./clipboard.js";

export function handleOffscreenMessage(message, doc) {
  if (!message || message.target !== "offscreen-clipboard" || message.type !== "copy") {
    return false;
  }
  if (typeof message.text !== "string") {
    return false;
  }
  writeClipboard(doc, message.text);
  return true;
}

const extension = globalThis.chrome;
if (extension && extension.runtime && extension.runtime.onMessage) {
  extension.runtime.onMessage.addListener((message, sender, sendResponse) => {
    if (!handleOffscreenMessage(message, document)) {
      return;
    }
    sendResponse({ ok: true });
    queueMicrotask(() => {
      globalThis.close();
    });
  });
}
