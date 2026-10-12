import test from "node:test";
import assert from "node:assert/strict";

import {
  infoRefsUrl,
  normalizeRepoUrl,
  proxied,
  uploadPackUrl,
} from "../src/proxy.js";

test("normalizeRepoUrl accepts owner/repo, hosts, and .git suffixes", () => {
  assert.equal(normalizeRepoUrl("octocat/Hello-World"), "https://github.com/octocat/Hello-World.git");
  assert.equal(normalizeRepoUrl("github.com/a/b"), "https://github.com/a/b.git");
  assert.equal(normalizeRepoUrl("https://example.com/a/b.git"), "https://example.com/a/b.git");
  assert.equal(normalizeRepoUrl("https://github.com/a/b/"), "https://github.com/a/b.git");
});

test("normalizeRepoUrl rejects empty input", () => {
  assert.throws(() => normalizeRepoUrl("   "));
});

test("endpoint helpers build smart-HTTP URLs", () => {
  const base = "https://github.com/a/b.git";
  assert.equal(infoRefsUrl(base), "https://github.com/a/b.git/info/refs?service=git-upload-pack");
  assert.equal(uploadPackUrl(base), "https://github.com/a/b.git/git-upload-pack");
});

test("proxied wraps the target and encodes it", () => {
  const url = proxied("https://proxy.example", "https://github.com/a/b.git/info/refs?service=git-upload-pack");
  assert.equal(
    url,
    "https://proxy.example/?url=https%3A%2F%2Fgithub.com%2Fa%2Fb.git%2Finfo%2Frefs%3Fservice%3Dgit-upload-pack",
  );
  assert.equal(proxied("", "https://x"), "https://x");
});
