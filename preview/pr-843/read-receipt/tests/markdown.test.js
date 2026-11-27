import assert from 'node:assert/strict';
import {test} from 'node:test';

import {markdownToHtml} from '../src/markdown.js';

test('markdownToHtml renders GitHub-flavored Markdown', () => {
  const html = markdownToHtml('# Title\n\n- [x] done\n\n| a |\n|---|\n| b |');
  assert.match(html, /<h1>Title<\/h1>/);
  assert.match(html, /<input checked="" disabled="" type="checkbox">/);
  assert.match(html, /<table>/);
});

test('markdownToHtml renders images as links so nothing loads', () => {
  const html = markdownToHtml('![a "cat"](https://example.com/cat.png)');
  assert.doesNotMatch(html, /<img/);
  assert.match(
    html,
    /<a href="https:\/\/example.com\/cat.png">a &#34;cat&#34;<\/a>/,
  );
});

test('markdownToHtml image links fall back to the URL', () => {
  assert.match(
    markdownToHtml('![](https://example.com/x.png)'),
    /<a href="https:\/\/example.com\/x.png">https:\/\/example.com\/x.png<\/a>/,
  );
});
