import {
  highlight,
  tokenize,
  grammarForPath,
  canHighlight,
  GRAMMAR_KEYS,
} from '../src/highlightCode.js';

/** Convenience: the set of token types produced for a snippet. */
function typesFor(code, grammar) {
  return new Set(highlight(code, grammar).map((t) => t.type).filter(Boolean));
}

/** The plain-text reconstruction of a token list. */
function reassemble(tokens) {
  return tokens.map((t) => t.text).join('');
}

describe('grammarForPath / canHighlight', () => {
  test('maps known extensions', () => {
    expect(grammarForPath('src/app.js')).toBe('js');
    expect(grammarForPath('a/b.tsx')).toBe('js');
    expect(grammarForPath('package.json')).toBe('json');
    expect(grammarForPath('styles/main.css')).toBe('css');
    expect(grammarForPath('index.html')).toBe('markup');
    expect(grammarForPath('README.md')).toBe('markdown');
    expect(grammarForPath('script.py')).toBe('python');
    expect(grammarForPath('run.sh')).toBe('shell');
    expect(grammarForPath('config.yaml')).toBe('yaml');
    expect(grammarForPath('main.go')).toBe('clike');
    expect(grammarForPath('Dockerfile')).toBe('shell');
  });

  test('falls back to plain for unknown / extensionless', () => {
    expect(grammarForPath('LICENSE')).toBe('plain');
    expect(grammarForPath('data.bin')).toBe('plain');
    expect(canHighlight('src/app.js')).toBe(true);
    expect(canHighlight('LICENSE')).toBe(false);
  });
});

describe('text preservation (never corrupts the file)', () => {
  const samples = {
    js: `// a comment\nconst x = "hi";\nfunction foo(a) { return a + 1; }\nlet t = \`tpl \${x}\`;\n`,
    json: `{\n  "name": "demo",\n  "count": 3,\n  "ok": true,\n  "nested": null\n}\n`,
    css: `:root { --x: #fff; }\n.a { color: red; width: 10px; } /* c */\n`,
    markup: `<!-- c -->\n<div class="x" id='y'>text &amp; more</div>\n`,
    markdown: `# Title\n\n- item with \`code\`\n> quote\n\n**bold** and *em* [l](http://x)\n`,
    python: `# c\ndef f(x):\n    return "s" + 'q'\nclass A: pass\n`,
    shell: `#!/bin/bash\necho "$HOME/x" # note\nfor i in 1 2; do done\n`,
    yaml: `# c\nname: demo\nlist:\n  - a\n  - b\nflag: true\n`,
    clike: `#include <stdio.h>\nint main(void) { /* x */ return 0; }\n`,
  };

  test.each(Object.entries(samples))('round-trips %s', (grammar, code) => {
    expect(reassemble(highlight(code, grammar))).toBe(code);
  });

  test('round-trips pathological / unterminated input without throwing', () => {
    const nasties = [
      '"unterminated string',
      '/* unterminated block comment',
      '`unterminated template',
      '###\n```\nunclosed fence',
      '\u0000\u0001<<<>>>***```',
      '',
    ];
    for (const grammar of GRAMMAR_KEYS) {
      for (const code of nasties) {
        const tokens = highlight(code, grammar);
        expect(reassemble(tokens)).toBe(code);
      }
    }
  });
});

describe('token classification', () => {
  test('javascript', () => {
    const types = typesFor('const n = 42; // hi\nclass Foo {}', 'js');
    expect(types).toContain('keyword'); // const / class
    expect(types).toContain('number'); // 42
    expect(types).toContain('comment'); // // hi
    expect(types).toContain('type'); // Foo
  });

  test('strings beat keywords inside them', () => {
    const tokens = highlight('const s = "if for while";', 'js');
    const str = tokens.find((t) => t.text === '"if for while"');
    expect(str).toBeDefined();
    expect(str.type).toBe('string');
  });

  test('json highlights keys as properties distinct from string values', () => {
    const tokens = highlight('{"k": "v"}', 'json');
    expect(tokens.find((t) => t.text === '"k"').type).toBe('property');
    expect(tokens.find((t) => t.text === '"v"').type).toBe('string');
  });

  test('markdown headings and inline code', () => {
    const types = typesFor('# Heading\n\nsome `code` here\n', 'markdown');
    expect(types).toContain('heading');
    expect(types).toContain('string'); // `code`
  });
});

describe('highlight() fallbacks', () => {
  test('unknown grammar yields a single plain token', () => {
    expect(highlight('anything at all', 'plain')).toEqual([
      { text: 'anything at all', type: null },
    ]);
    expect(highlight('x', 'nope')).toEqual([{ text: 'x', type: null }]);
  });
});

describe('tokenize guards against zero-width rules', () => {
  test('a rule that can match empty does not loop forever', () => {
    const rules = [{ type: 'maybe', re: /a*/y }]; // matches empty at non-'a'
    const tokens = tokenize('bab', rules);
    expect(reassemble(tokens)).toBe('bab');
    expect(tokens.find((t) => t.text === 'a').type).toBe('maybe');
  });
});
