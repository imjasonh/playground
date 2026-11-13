import assert from 'node:assert/strict';
import test from 'node:test';

import {markdownToHtml, renderMarkdown} from '../src/markdown.js';

test('markdownToHtml renders common Markdown', () => {
  const html = markdownToHtml(
    '# Title\n\nSome **bold** and `code`.\n\n- one\n- two\n',
  );
  assert.match(html, /<h1>Title<\/h1>/);
  assert.match(html, /<strong>bold<\/strong>/);
  assert.match(html, /<code>code<\/code>/);
  assert.match(html, /<ul>\s*<li>one<\/li>\s*<li>two<\/li>\s*<\/ul>/);
});

test('markdownToHtml renders GitHub-flavored tables and fences', () => {
  const html = markdownToHtml(
    '| a | b |\n| - | - |\n| 1 | 2 |\n\n```js\nlet x = 1;\n```\n',
  );
  assert.match(html, /<table>/);
  assert.match(html, /<td>1<\/td>/);
  assert.match(html, /<pre><code class="language-js">let x = 1;/);
});

test('markdownToHtml tolerates an unclosed fence mid-stream', () => {
  assert.match(markdownToHtml('```\nlet x'), /<pre><code>let x/);
});

test('renderMarkdown falls back to plain text without a DOM', () => {
  const target = {textContent: '', innerHTML: ''};
  renderMarkdown(target, '<img src=x onerror=alert(1)> **hi**');
  assert.equal(target.textContent, '<img src=x onerror=alert(1)> **hi**');
  assert.equal(target.innerHTML, '');
});
