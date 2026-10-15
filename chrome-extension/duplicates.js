// Tabs that share a URL are duplicates. duplicateTabIds returns the ids a
// click closes. The keeper is the pinned tab, then the active tab, then the
// tab used most recently. A lower id wins a tie. An empty URL is not a group.

export const BADGE_COLOR = "#174ea6";
export const BADGE_TEXT_COLOR = "#ffffff";

export function tabUrl(tab) {
  if (tab === null || typeof tab !== "object") {
    return "";
  }
  const url = typeof tab.url === "string" ? tab.url : "";
  const pending = typeof tab.pendingUrl === "string" ? tab.pendingUrl : "";
  if (url !== "" && url !== "about:blank") {
    return url;
  }
  return pending;
}

function prefer(candidate, keeper) {
  const candidatePinned = candidate.pinned === true ? 1 : 0;
  const keeperPinned = keeper.pinned === true ? 1 : 0;
  if (candidatePinned !== keeperPinned) {
    return candidatePinned > keeperPinned;
  }
  const candidateActive = candidate.active === true ? 1 : 0;
  const keeperActive = keeper.active === true ? 1 : 0;
  if (candidateActive !== keeperActive) {
    return candidateActive > keeperActive;
  }
  const candidateUsed = Number(candidate.lastAccessed) || 0;
  const keeperUsed = Number(keeper.lastAccessed) || 0;
  if (candidateUsed !== keeperUsed) {
    return candidateUsed > keeperUsed;
  }
  const candidateId = Number(candidate.id) || 0;
  const keeperId = Number(keeper.id) || 0;
  return candidateId < keeperId;
}

export function duplicateTabIds(tabs) {
  const groups = new Map();
  for (const tab of tabs) {
    const url = tabUrl(tab);
    const idOk = tab !== null && typeof tab === "object" && typeof tab.id === "number";
    if (url !== "" && idOk) {
      const list = groups.get(url);
      if (list) {
        list.push(tab);
      } else {
        groups.set(url, [tab]);
      }
    }
  }
  const close = [];
  for (const group of groups.values()) {
    if (group.length >= 2) {
      let keeper = group[0];
      for (let index = 1; index < group.length; index += 1) {
        if (prefer(group[index], keeper)) {
          keeper = group[index];
        }
      }
      for (const tab of group) {
        if (tab.id !== keeper.id) {
          close.push(tab.id);
        }
      }
    }
  }
  close.sort((left, right) => left - right);
  return close;
}

export function badgeText(count) {
  if (count <= 0) {
    return "";
  }
  if (count > 999) {
    return "999+";
  }
  return String(count);
}

export function actionTitle(count) {
  if (count <= 0) {
    return "No duplicate tabs";
  }
  if (count === 1) {
    return "Close 1 duplicate tab";
  }
  return `Close ${count} duplicate tabs`;
}
