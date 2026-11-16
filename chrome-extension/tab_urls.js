import { tabUrl } from "./duplicates.js";

export function copyTitle(count) {
  if (count <= 1) {
    return "Copy tab URL";
  }
  return `Copy ${count} tab URLs`;
}

// Chrome's own tab menu acts on the selection only when the right-clicked
// tab is part of it. A right-click on any other tab acts on that tab alone,
// even though the title still counts the selection.
export function urlsText(clicked, highlighted) {
  let tabs = [clicked];
  if (clicked.highlighted === true && highlighted.length > 0) {
    tabs = [...highlighted].sort((left, right) => left.index - right.index);
  }
  return tabs
    .map((tab) => tabUrl(tab))
    .filter((url) => url !== "")
    .join("\n");
}
