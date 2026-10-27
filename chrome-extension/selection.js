// Reports the highlighted text so the service worker can update the
// selection menu before the right-click. Chrome builds that menu from
// the item that already exists. It does not include the selection.

let hadSelection = false;
let scheduled = false;

function inputSelection(active) {
  if (!active || (active.tagName !== "INPUT" && active.tagName !== "TEXTAREA")) {
    return "";
  }
  try {
    const start = active.selectionStart;
    const end = active.selectionEnd;
    if (typeof start !== "number" || typeof end !== "number" || end <= start) {
      return "";
    }
    return active.value.slice(start, end);
  } catch {
    return "";
  }
}

function readSelection() {
  const fromField = inputSelection(document.activeElement);
  if (fromField !== "") {
    return fromField;
  }
  if (typeof document.getSelection !== "function") {
    return "";
  }
  const selection = document.getSelection();
  if (!selection) {
    return "";
  }
  return selection.toString();
}

function noteIgnored(error) {
  const message = error && typeof error.message === "string" ? error.message : String(error);
  if (message.includes("Receiving end does not exist")) {
    return;
  }
  if (message.includes("Extension context invalidated")) {
    return;
  }
  console.error(error);
}

function publishSelection(text) {
  let pending;
  try {
    pending = chrome.runtime.sendMessage({ type: "selection", text });
  } catch (error) {
    noteIgnored(error);
    return;
  }
  if (!pending || typeof pending.then !== "function") {
    return;
  }
  pending.then(
    () => {},
    (error) => {
      noteIgnored(error);
    },
  );
}

function reportSelection() {
  const text = readSelection();
  const nonempty = text.trim() !== "";
  if (!nonempty && !hadSelection) {
    return;
  }
  hadSelection = nonempty;
  publishSelection(text);
}

function scheduleReport() {
  if (scheduled) {
    return;
  }
  scheduled = true;
  queueMicrotask(() => {
    scheduled = false;
    try {
      reportSelection();
    } catch (error) {
      console.error(error);
    }
  });
}

document.addEventListener("selectionchange", scheduleReport);
