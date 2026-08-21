"use strict";

function nonemptyLines(text) {
  return text.split("\n").map(trimLine).filter(isNonempty);
}

function trimLine(line) {
  return line.trim();
}

function isNonempty(line) {
  return line.length > 0;
}

function hasDigit(line) {
  return /\d/.test(line);
}

function leadingNames(lines) {
  let i = 0;
  let foundDigit = false;
  while (i < lines.length) {
    if (hasDigit(lines[i])) {
      foundDigit = true;
      break;
    }
    i += 1;
  }
  if (foundDigit) {
    return lines.slice(0, i);
  }
  if (lines.length >= 2) {
    return lines.slice(0, lines.length - 1);
  }
  return [];
}

function locationQuery(text) {
  const lines = nonemptyLines(text);
  const names = leadingNames(lines);
  if (names.length < lines.length) {
    return lines.slice(names.length).join(" ");
  }
  return lines.join(" ");
}

function hideList(list) {
  list.hidden = true;
  list.replaceChildren();
}

function selectedButton(list) {
  return list.querySelector('button[aria-selected="true"]');
}

function moveSelection(list, delta) {
  const buttons = list.querySelectorAll("button");
  if (buttons.length === 0) {
    return;
  }
  let index = -1;
  let i = 0;
  while (i < buttons.length) {
    if (buttons[i].getAttribute("aria-selected") === "true") {
      index = i;
    }
    i += 1;
  }
  let next = index + delta;
  if (next < 0) {
    next = 0;
  }
  if (next >= buttons.length) {
    next = buttons.length - 1;
  }
  i = 0;
  while (i < buttons.length) {
    if (i === next) {
      buttons[i].setAttribute("aria-selected", "true");
    } else {
      buttons[i].setAttribute("aria-selected", "false");
    }
    i += 1;
  }
  buttons[next].scrollIntoView({ block: "nearest" });
}

function applyLines(textarea, postalLines) {
  const names = leadingNames(nonemptyLines(textarea.value));
  textarea.value = names.concat(postalLines).join("\n");
}

function pickPlace(textarea, list, placeId) {
  hideList(list);
  fetch("place?id=" + encodeURIComponent(placeId))
    .then(function readPlace(resp) {
      return resp.json();
    })
    .then(function fillPlace(data) {
      if (!data || !data.lines || data.lines.length === 0) {
        return;
      }
      applyLines(textarea, data.lines);
    })
    .catch(function ignorePlaceError() {});
}

function renderSuggestions(textarea, list, suggestions) {
  list.replaceChildren();
  if (!suggestions || suggestions.length === 0) {
    hideList(list);
    return;
  }
  let i = 0;
  while (i < suggestions.length) {
    const item = suggestions[i];
    const li = document.createElement("li");
    const button = document.createElement("button");
    button.type = "button";
    button.textContent = item.label;
    button.setAttribute("aria-selected", "false");
    button.dataset.placeId = item.place_id;
    button.addEventListener("mousedown", function preventBlur(ev) {
      ev.preventDefault();
    });
    button.addEventListener("click", function onPick() {
      pickPlace(textarea, list, item.place_id);
    });
    li.appendChild(button);
    list.appendChild(li);
    i += 1;
  }
  list.hidden = false;
}

function bindAddressField(textarea) {
  const listId = textarea.id + "-suggest";
  const list = document.getElementById(listId);
  if (!list) {
    return;
  }
  let timer = 0;
  let seq = 0;

  function scheduleSuggest() {
    window.clearTimeout(timer);
    timer = window.setTimeout(runSuggest, 220);
  }

  function runSuggest() {
    const q = locationQuery(textarea.value);
    if (q.length < 3) {
      hideList(list);
      return;
    }
    seq += 1;
    const mine = seq;
    fetch("suggest?q=" + encodeURIComponent(q))
      .then(function readSuggest(resp) {
        return resp.json();
      })
      .then(function showSuggest(data) {
        if (mine !== seq) {
          return;
        }
        let suggestions = [];
        if (data && data.suggestions) {
          suggestions = data.suggestions;
        }
        renderSuggestions(textarea, list, suggestions);
      })
      .catch(function ignoreSuggestError() {
        if (mine === seq) {
          hideList(list);
        }
      });
  }

  textarea.addEventListener("input", scheduleSuggest);
  textarea.addEventListener("blur", function onBlur() {
    window.setTimeout(function hideLater() {
      hideList(list);
    }, 120);
  });
  textarea.addEventListener("keydown", function onKey(ev) {
    if (list.hidden) {
      return;
    }
    if (ev.key === "Escape") {
      hideList(list);
      ev.preventDefault();
      return;
    }
    if (ev.key === "ArrowDown") {
      moveSelection(list, 1);
      ev.preventDefault();
      return;
    }
    if (ev.key === "ArrowUp") {
      moveSelection(list, -1);
      ev.preventDefault();
      return;
    }
    if (ev.key === "Enter") {
      const chosen = selectedButton(list);
      if (chosen && chosen.dataset.placeId) {
        pickPlace(textarea, list, chosen.dataset.placeId);
        ev.preventDefault();
      }
    }
  });
}

function ready() {
  const fields = document.querySelectorAll("textarea[name='from'], textarea[name='to']");
  let i = 0;
  while (i < fields.length) {
    bindAddressField(fields[i]);
    i += 1;
  }
}

if (document.readyState === "loading") {
  document.addEventListener("DOMContentLoaded", ready);
} else {
  ready();
}
