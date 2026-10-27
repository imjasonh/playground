// Standard base64 is the RFC 4648 alphabet with padding. Leading and
// trailing whitespace is ignored. Whitespace in the middle is not.
const STANDARD_BASE64 =
  /^(?:[A-Za-z0-9+/]{4})*(?:[A-Za-z0-9+/]{2}==|[A-Za-z0-9+/]{3}=)?$/;

// decodeBase64 returns UTF-8 text, or null when the input is not base64
// the selection menu can show. An empty or whitespace-only decode is null
// because that menu item would have no label.
export function decodeBase64(raw) {
  if (typeof raw !== "string") {
    return null;
  }
  const encoded = raw.trim();
  if (encoded.length === 0 || !STANDARD_BASE64.test(encoded)) {
    return null;
  }
  let binary;
  try {
    binary = atob(encoded);
  } catch {
    return null;
  }
  const bytes = Uint8Array.from(binary, (char) => char.charCodeAt(0));
  try {
    const decoded = new TextDecoder("utf-8", { fatal: true }).decode(bytes);
    if (decoded.trim() === "") {
      return null;
    }
    return decoded;
  } catch {
    return null;
  }
}

// Chrome replaces %s in a context menu title with the selected text. A
// zero-width space keeps those characters visible. Newlines become spaces
// so the title stays one line. The copied text keeps the original decode.
export function menuTitle(decoded) {
  const oneLine = decoded.replaceAll("\r\n", " ").replaceAll("\n", " ").replaceAll("\r", " ");
  const title = oneLine.replaceAll("%s", "%\u200bs");
  if (title.trim() === "") {
    return null;
  }
  return title;
}

// The click copies the decode the menu is showing. After the service
// worker restarts, that string is gone and the selection is decoded again.
export function textToCopy(selectionText, pending) {
  if (typeof pending === "string") {
    return pending;
  }
  if (typeof selectionText !== "string") {
    return null;
  }
  return decodeBase64(selectionText);
}
