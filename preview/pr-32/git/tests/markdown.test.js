import { renderMarkdown } from '../src/markdown.js';

describe('renderMarkdown — blocks', () => {
  test('headings at each level', () => {
    expect(renderMarkdown('# Title')).toBe('<h1>Title</h1>');
    expect(renderMarkdown('### Sub')).toBe('<h3>Sub</h3>');
    expect(renderMarkdown('###### Deep ###')).toBe('<h6>Deep</h6>');
  });

  test('paragraphs join soft-wrapped lines and honor hard breaks', () => {
    expect(renderMarkdown('one\ntwo')).toBe('<p>one two</p>');
    expect(renderMarkdown('one  \ntwo')).toBe('<p>one<br>two</p>');
  });

  test('separates paragraphs on blank lines', () => {
    expect(renderMarkdown('a\n\nb')).toBe('<p>a</p>\n<p>b</p>');
  });

  test('unordered and ordered lists', () => {
    expect(renderMarkdown('- a\n- b')).toBe('<ul><li>a</li><li>b</li></ul>');
    expect(renderMarkdown('1. a\n2. b')).toBe('<ol><li>a</li><li>b</li></ol>');
  });

  test('fenced code is escaped and not formatted, with a language class', () => {
    const html = renderMarkdown('```js\nconst x = 1 < 2 && *y*;\n```');
    expect(html).toBe('<pre><code class="language-js">const x = 1 &lt; 2 &amp;&amp; *y*;</code></pre>');
  });

  test('blockquotes render their inner Markdown', () => {
    expect(renderMarkdown('> **hi**')).toBe('<blockquote><p><strong>hi</strong></p></blockquote>');
  });

  test('horizontal rules', () => {
    expect(renderMarkdown('---')).toBe('<hr>');
    expect(renderMarkdown('***')).toBe('<hr>');
  });

  test('GitHub pipe tables with alignment', () => {
    const html = renderMarkdown('| A | B |\n| :- | -: |\n| 1 | 2 |');
    expect(html).toContain('<table>');
    expect(html).toContain('<th style="text-align:left">A</th>');
    expect(html).toContain('<th style="text-align:right">B</th>');
    expect(html).toContain('<td style="text-align:left">1</td>');
    expect(html).toContain('</tbody></table>');
  });
});

describe('renderMarkdown — inline', () => {
  test('bold, italic, and inline code', () => {
    expect(renderMarkdown('**b** and *i* and `c`')).toBe(
      '<p><strong>b</strong> and <em>i</em> and <code>c</code></p>'
    );
  });

  test('does not treat snake_case as emphasis', () => {
    expect(renderMarkdown('load_tasks_now')).toBe('<p>load_tasks_now</p>');
  });

  test('links and images with safe URLs', () => {
    expect(renderMarkdown('[t](https://example.com)')).toBe(
      '<p><a href="https://example.com" target="_blank" rel="noreferrer noopener">t</a></p>'
    );
    expect(renderMarkdown('![alt](img.png)')).toBe('<p><img src="img.png" alt="alt"></p>');
  });

  test('angle autolinks', () => {
    expect(renderMarkdown('<https://example.com>')).toBe(
      '<p><a href="https://example.com" target="_blank" rel="noreferrer noopener">https://example.com</a></p>'
    );
  });
});

describe('renderMarkdown — safety', () => {
  test('escapes raw HTML in the source', () => {
    expect(renderMarkdown('<script>alert(1)</script>')).toBe(
      '<p>&lt;script&gt;alert(1)&lt;/script&gt;</p>'
    );
    expect(renderMarkdown('a < b & c > d')).toBe('<p>a &lt; b &amp; c &gt; d</p>');
  });

  test('drops javascript: and data: URLs from links (keeping the text)', () => {
    const link = renderMarkdown('[click](javascript:alert(1))');
    expect(link).not.toContain('href');
    expect(link).not.toContain('javascript');
    expect(link).toContain('click');

    const dataLink = renderMarkdown('[x](data:text/html,<script>1</script>)');
    expect(dataLink).not.toContain('href');
    expect(dataLink).not.toContain('<script');
  });

  test('drops unsafe image URLs but keeps the alt text', () => {
    const img = renderMarkdown('![x](javascript:alert(1))');
    expect(img).not.toContain('src=');
    expect(img).not.toContain('javascript');
    expect(img).toContain('x');
  });

  test('neutralizes attribute-breakout attempts in URLs', () => {
    // A malformed URL with embedded HTML must never produce a live element or
    // attribute; it is escaped to inert text instead.
    const html = renderMarkdown('[t](https://e.com/"><img src=x onerror=alert(1)>)');
    expect(html).not.toContain('<img');
    expect(html).not.toContain('href=');
    expect(html).toContain('&lt;img');
  });

  test('escapes HTML inside link text and code spans', () => {
    expect(renderMarkdown('[<b>x</b>](https://e.com)')).toContain('&lt;b&gt;x&lt;/b&gt;');
    expect(renderMarkdown('`<b>`')).toBe('<p><code>&lt;b&gt;</code></p>');
  });

  test('allows relative links and anchors', () => {
    expect(renderMarkdown('[a](./docs/readme.md)')).toContain('href="./docs/readme.md"');
    expect(renderMarkdown('[a](#section)')).toContain('href="#section"');
  });

  test('handles empty / nullish input', () => {
    expect(renderMarkdown('')).toBe('');
    expect(renderMarkdown(null)).toBe('');
    expect(renderMarkdown(undefined)).toBe('');
  });
});
