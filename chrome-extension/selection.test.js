import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import path from "node:path";
import test from "node:test";
import vm from "node:vm";

const root = path.dirname(new URL(import.meta.url).pathname);

function loadPage() {
  const sent = [];
  const errors = [];
  let selected = "";
  let active = null;
  let rejected = null;
  const listeners = new Map();
  const document = {
    get activeElement() {
      return active;
    },
    getSelection() {
      return {
        toString() {
          return selected;
        },
      };
    },
    addEventListener(type, fn) {
      listeners.set(type, fn);
    },
  };
  const chrome = {
    runtime: {
      sendMessage(message) {
        if (rejected) {
          return Promise.reject(rejected);
        }
        sent.push(message);
        return Promise.resolve({ ok: true });
      },
    },
  };
  const context = vm.createContext({
    document,
    chrome,
    queueMicrotask,
    Promise,
    console: {
      error(...args) {
        errors.push(args);
      },
    },
  });
  vm.runInContext(readFileSync(path.join(root, "selection.js"), "utf8"), context);
  return {
    sent,
    errors,
    select() {
      const report = listeners.get("selectionchange");
      assert.equal(typeof report, "function");
      report();
    },
    setSelected(value) {
      selected = value;
    },
    setActive(value) {
      active = value;
    },
    rejectNext(error) {
      rejected = error;
    },
  };
}

function flush() {
  return new Promise((resolve) => {
    setImmediate(resolve);
  });
}

function plain(value) {
  return JSON.parse(JSON.stringify(value));
}

test("an empty selection does not message, and a later selection does", async () => {
  const page = loadPage();
  page.select();
  await flush();
  assert.deepEqual(plain(page.sent), []);
  page.setSelected("  aGVsbG8=  ");
  page.select();
  page.setSelected("YQ==");
  page.select();
  await flush();
  assert.deepEqual(plain(page.sent), [{ type: "selection", text: "YQ==" }]);
  page.setSelected("");
  page.select();
  await flush();
  assert.deepEqual(plain(page.sent), [
    { type: "selection", text: "YQ==" },
    { type: "selection", text: "" },
  ]);
  page.select();
  await flush();
  assert.equal(page.sent.length, 2);
});

test("a text field selection is reported, including when the page selection is empty", async () => {
  const page = loadPage();
  page.setActive({
    tagName: "TEXTAREA",
    value: "aGVsbG8=",
    selectionStart: 0,
    selectionEnd: 8,
  });
  page.select();
  await flush();
  assert.deepEqual(plain(page.sent), [{ type: "selection", text: "aGVsbG8=" }]);
});

test("a collapsed text field falls through to the page selection", async () => {
  const page = loadPage();
  page.setActive({
    tagName: "INPUT",
    value: "aGVsbG8=",
    selectionStart: 2,
    selectionEnd: 2,
  });
  page.setSelected("YQ==");
  page.select();
  await flush();
  assert.deepEqual(plain(page.sent), [{ type: "selection", text: "YQ==" }]);
});

test("a missing extension receiver is ignored", async () => {
  const page = loadPage();
  page.rejectNext(new Error("Could not establish connection. Receiving end does not exist."));
  page.setSelected("YQ==");
  page.select();
  await flush();
  assert.deepEqual(plain(page.sent), []);
  assert.deepEqual(plain(page.errors), []);
});
