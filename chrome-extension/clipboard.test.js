import assert from "node:assert/strict";
import test from "node:test";

import { writeClipboard } from "./clipboard.js";
import { handleOffscreenMessage } from "./offscreen.js";

function fakeDocument() {
  const steps = [];
  const field = {
    value: "",
    select() {
      steps.push("select");
    },
    remove() {
      steps.push("remove");
    },
  };
  return {
    steps,
    field,
    doc: {
      body: {
        appendChild(node) {
          steps.push(["append", node]);
        },
      },
      createElement(tag) {
        steps.push(["create", tag]);
        return field;
      },
      execCommand(command) {
        steps.push(["command", command, field.value]);
        return true;
      },
    },
  };
}

test("writeClipboard selects the decoded text and copies it", () => {
  const { doc, steps, field } = fakeDocument();
  assert.equal(writeClipboard(doc, "a\nb"), true);
  assert.equal(field.value, "a\nb");
  assert.deepEqual(steps, [
    ["create", "textarea"],
    ["append", field],
    "select",
    ["command", "copy", "a\nb"],
    "remove",
  ]);
});

test("the offscreen document copies only a clipboard message", () => {
  const page = fakeDocument();
  assert.equal(handleOffscreenMessage({ type: "selection", text: "YQ==" }, page.doc), false);
  assert.deepEqual(page.steps, []);
  assert.equal(
    handleOffscreenMessage({ target: "offscreen-clipboard", type: "copy", text: "a" }, page.doc),
    true,
  );
  assert.equal(page.field.value, "a");
  assert.equal(
    handleOffscreenMessage({ target: "offscreen-clipboard", type: "copy", text: 1 }, page.doc),
    false,
  );
});
