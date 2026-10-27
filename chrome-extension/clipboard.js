// Offscreen documents cannot use navigator.clipboard. execCommand("copy")
// writes the system clipboard from an extension page that has clipboardWrite.
export function writeClipboard(doc, text) {
  const field = doc.createElement("textarea");
  field.value = text;
  doc.body.appendChild(field);
  field.select();
  const copied = doc.execCommand("copy");
  field.remove();
  return copied;
}
