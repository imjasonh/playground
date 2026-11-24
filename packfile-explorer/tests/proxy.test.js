import test from "node:test";
import assert from "node:assert/strict";

import {
  DEFAULT_PROXY,
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

test("proxied uses the isomorphic-git path form", () => {
  const target = "https://github.com/a/b.git/info/refs?service=git-upload-pack";
  assert.equal(
    proxied("https://proxy.example", target),
    "https://proxy.example/github.com/a/b.git/info/refs?service=git-upload-pack",
  );
  assert.equal(
    proxied(DEFAULT_PROXY, infoRefsUrl("https://github.com/a/b.git")),
    "https://cors.isomorphic-git.org/github.com/a/b.git/info/refs?service=git-upload-pack",
  );
  assert.equal(proxied("https://example.com/proxy.php?", target), `https://example.com/proxy.php?${target}`);
  assert.equal(proxied("", "https://x"), "https://x");
});
