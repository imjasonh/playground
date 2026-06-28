/**
 * A tiny, dependency-free syntax highlighter.
 *
 * The viewer is plain text + line numbers; this adds token coloring for the
 * common languages without pulling in a multi-hundred-KB CDN/vendor bundle. It
 * trades exhaustive grammar accuracy for being small, fully offline, and
 * unit-testable — exactly matching the rest of this app's hand-rolled,
 * pure-function style (see fuzzy.js, diff.js).
 *
 * Each grammar is an ordered list of `{type, re}` rules. The tokenizer scans
 * left to right; at each position it tries the rules in order and takes the
 * first that matches *at that position* (the regexes are sticky). Anything no
 * rule claims is emitted as an untyped (plain) run. Because every character is
 * either part of a matched token or appended verbatim to the plain run, the
 * concatenation of all token texts is always exactly the input — highlighting
 * can never corrupt the file or shift line numbers.
 *
 * @typedef {Object} Token
 * @property {string} text
 * @property {?string} type  a token class suffix (e.g. 'string'), or null for plain
 */

import { basename, extname } from './pathUtils.js';

/**
 * Tokenize `code` with an ordered rule list. Pure; never throws on valid input.
 *
 * @param {string} code
 * @param {{type: string, re: RegExp}[]} rules  each `re` MUST use the 'y' flag
 * @returns {Token[]}
 */
export function tokenize(code, rules) {
  const out = [];
  let plain = '';
  let i = 0;
  const n = code.length;

  const flushPlain = () => {
    if (plain) {
      out.push({ text: plain, type: null });
      plain = '';
    }
  };

  while (i < n) {
    let text = null;
    let type = null;
    for (const rule of rules) {
      rule.re.lastIndex = i;
      const m = rule.re.exec(code);
      // Sticky ('y') guarantees a match starts exactly at lastIndex. Guard
      // against zero-width matches so the scan always makes progress.
      if (m && m[0].length > 0) {
        text = m[0];
        type = rule.type;
        break;
      }
    }
    if (text !== null) {
      flushPlain();
      out.push({ text, type });
      i += text.length;
    } else {
      plain += code[i];
      i += 1;
    }
  }
  flushPlain();
  return out;
}

/* ------------------------------------------------------------------ */
/* Shared rule fragments                                               */
/* ------------------------------------------------------------------ */

const blockComment = { type: 'comment', re: /\/\*[\s\S]*?\*\//y };
const blockCommentOpen = { type: 'comment', re: /\/\*[\s\S]*/y }; // unterminated → to EOF
const lineCommentSlash = { type: 'comment', re: /\/\/[^\n]*/y };
const lineCommentHash = { type: 'comment', re: /#[^\n]*/y };
const dquote = { type: 'string', re: /"(?:\\.|[^"\\\n])*"/y };
const squote = { type: 'string', re: /'(?:\\.|[^'\\\n])*'/y };
const template = { type: 'string', re: /`(?:\\.|[^`\\])*`/y };
const number = {
  type: 'number',
  re: /\b0[xX][0-9a-fA-F]+\b|\b\d[\d_]*(?:\.\d+)?(?:[eE][+-]?\d+)?\b/y,
};
const funcCall = { type: 'function', re: /[A-Za-z_$][\w$]*(?=\s*\()/y };
const typeName = { type: 'type', re: /\b[A-Z][A-Za-z0-9_]*\b/y };

const kw = (words) => ({
  type: 'keyword',
  re: new RegExp(`\\b(?:${words.join('|')})\\b`, 'y'),
});
const lit = (words) => ({
  type: 'literal',
  re: new RegExp(`\\b(?:${words.join('|')})\\b`, 'y'),
});

/* ------------------------------------------------------------------ */
/* Grammars                                                            */
/* ------------------------------------------------------------------ */

const JS_KEYWORDS = [
  'abstract', 'as', 'async', 'await', 'break', 'case', 'catch', 'class', 'const',
  'continue', 'debugger', 'declare', 'default', 'delete', 'do', 'else', 'enum',
  'export', 'extends', 'finally', 'for', 'from', 'function', 'get', 'if',
  'implements', 'import', 'in', 'instanceof', 'interface', 'let', 'namespace',
  'new', 'of', 'package', 'private', 'protected', 'public', 'readonly', 'return',
  'set', 'static', 'super', 'switch', 'this', 'throw', 'try', 'type', 'typeof',
  'var', 'void', 'while', 'with', 'yield',
];

const js = [
  blockComment, blockCommentOpen, lineCommentSlash,
  template, dquote, squote,
  lit(['true', 'false', 'null', 'undefined', 'NaN', 'Infinity']),
  kw(JS_KEYWORDS),
  number,
  funcCall,
  typeName,
];

const json = [
  { type: 'property', re: /"(?:\\.|[^"\\])*"(?=\s*:)/y },
  { type: 'string', re: /"(?:\\.|[^"\\])*"/y },
  lit(['true', 'false', 'null']),
  number,
];

const css = [
  blockComment, blockCommentOpen,
  dquote, squote,
  { type: 'keyword', re: /@[\w-]+/y }, // at-rules: @media, @import…
  { type: 'number', re: /#[0-9a-fA-F]{3,8}\b/y }, // hex colors
  {
    type: 'number',
    re: /\b\d[\d.]*(?:px|r?em|%|vh|vw|vmin|vmax|s|ms|fr|deg|pt|ch|ex)?\b/y,
  },
  { type: 'literal', re: /!important\b/y },
  { type: 'property', re: /[A-Za-z-]+(?=\s*:)/y },
];

const markup = [
  { type: 'comment', re: /<!--[\s\S]*?-->/y },
  { type: 'comment', re: /<!\[CDATA\[[\s\S]*?\]\]>/y },
  { type: 'meta', re: /<[!?][^>]*>/y }, // doctype / processing instructions
  { type: 'tag', re: /<\/?[A-Za-z][\w:.-]*/y },
  { type: 'attr', re: /[A-Za-z_:][\w:.-]*(?=\s*=)/y },
  dquote, squote,
  { type: 'literal', re: /&[a-zA-Z#0-9]+;/y }, // entities
];

const markdown = [
  { type: 'string', re: /```[\s\S]*?```/y },
  { type: 'string', re: /~~~[\s\S]*?~~~/y },
  { type: 'heading', re: /^#{1,6}[^\n]*/ym },
  { type: 'comment', re: /^>[^\n]*/ym }, // blockquote
  { type: 'keyword', re: /^[ \t]*(?:[-*+]|\d+\.)(?=\s)/ym }, // list markers
  { type: 'string', re: /`[^`\n]+`/y }, // inline code
  { type: 'link', re: /\[[^\]\n]*\]\([^)\n]*\)/y },
  { type: 'strong', re: /\*\*[^\n]+?\*\*/y },
  { type: 'strong', re: /__[^\n]+?__/y },
  { type: 'em', re: /\*[^\n*]+?\*/y },
  { type: 'em', re: /_[^\n_]+?_/y },
];

const PY_KEYWORDS = [
  'and', 'as', 'assert', 'async', 'await', 'break', 'class', 'continue', 'def',
  'del', 'elif', 'else', 'except', 'finally', 'for', 'from', 'global', 'if',
  'import', 'in', 'is', 'lambda', 'nonlocal', 'not', 'or', 'pass', 'raise',
  'return', 'try', 'while', 'with', 'yield',
];

const python = [
  { type: 'comment', re: /#[^\n]*/y },
  { type: 'string', re: /[rbfRBF]{0,2}"""[\s\S]*?"""/y },
  { type: 'string', re: /[rbfRBF]{0,2}'''[\s\S]*?'''/y },
  { type: 'string', re: /[rbfRBF]{0,2}"(?:\\.|[^"\\\n])*"/y },
  { type: 'string', re: /[rbfRBF]{0,2}'(?:\\.|[^'\\\n])*'/y },
  { type: 'meta', re: /@[\w.]+/y }, // decorators
  lit(['True', 'False', 'None']),
  kw(PY_KEYWORDS),
  number,
  funcCall,
  typeName,
];

const SHELL_KEYWORDS = [
  'if', 'then', 'else', 'elif', 'fi', 'for', 'while', 'until', 'do', 'done',
  'case', 'esac', 'function', 'in', 'select', 'return', 'break', 'continue',
  'local', 'export', 'readonly', 'declare',
];

const shell = [
  lineCommentHash,
  dquote, squote,
  { type: 'variable', re: /\$\{[^}]*\}|\$[\w@*#?]+/y },
  kw(SHELL_KEYWORDS),
  number,
];

const yaml = [
  lineCommentHash,
  { type: 'property', re: /^[ \t]*-?\s*[\w.$-]+(?=\s*:(?:\s|$))/ym },
  dquote, squote,
  { type: 'meta', re: /[&*][\w-]+/y }, // anchors / aliases
  lit(['true', 'false', 'null', 'yes', 'no', 'on', 'off']),
  number,
];

const CLIKE_KEYWORDS = [
  'auto', 'bool', 'break', 'case', 'catch', 'char', 'class', 'const', 'constexpr',
  'continue', 'def', 'default', 'defer', 'delete', 'do', 'double', 'else', 'enum',
  'extends', 'extern', 'final', 'finally', 'float', 'fn', 'for', 'func', 'go',
  'goto', 'if', 'impl', 'implements', 'import', 'in', 'int', 'interface', 'let',
  'long', 'match', 'mut', 'namespace', 'new', 'override', 'package', 'private',
  'protected', 'pub', 'public', 'return', 'short', 'signed', 'sizeof', 'static',
  'struct', 'switch', 'template', 'this', 'throw', 'throws', 'trait', 'try',
  'type', 'typedef', 'typename', 'union', 'unsigned', 'using', 'val', 'var',
  'virtual', 'void', 'volatile', 'where', 'while',
];

const clike = [
  blockComment, blockCommentOpen, lineCommentSlash,
  { type: 'meta', re: /^[ \t]*#\s*\w+/ym }, // C preprocessor
  dquote, squote, template,
  lit(['true', 'false', 'null', 'nil', 'nullptr', 'None']),
  kw(CLIKE_KEYWORDS),
  number,
  funcCall,
  typeName,
];

const GRAMMARS = {
  js,
  json,
  css,
  markup,
  markdown,
  python,
  shell,
  yaml,
  clike,
};

/** Extension (with dot) -> grammar key. */
const EXT_GRAMMARS = {
  '.js': 'js', '.mjs': 'js', '.cjs': 'js', '.jsx': 'js',
  '.ts': 'js', '.tsx': 'js',
  '.json': 'json', '.jsonc': 'json',
  '.css': 'css', '.scss': 'css', '.less': 'css', '.sass': 'css',
  '.html': 'markup', '.htm': 'markup', '.xml': 'markup', '.svg': 'markup',
  '.vue': 'markup', '.svelte': 'markup',
  '.md': 'markdown', '.markdown': 'markdown',
  '.py': 'python',
  '.sh': 'shell', '.bash': 'shell', '.zsh': 'shell',
  '.yml': 'yaml', '.yaml': 'yaml',
  '.c': 'clike', '.h': 'clike', '.cpp': 'clike', '.cc': 'clike', '.hpp': 'clike',
  '.cs': 'clike', '.java': 'clike', '.go': 'clike', '.rs': 'clike',
  '.kt': 'clike', '.swift': 'clike', '.php': 'clike',
};

const FILENAME_GRAMMARS = {
  dockerfile: 'shell',
  makefile: 'shell',
};

/** Pick a grammar key for a path, or 'plain' when none applies. */
export function grammarForPath(path) {
  const name = basename(path).toLowerCase();
  if (FILENAME_GRAMMARS[name]) return FILENAME_GRAMMARS[name];
  return EXT_GRAMMARS[extname(path)] || 'plain';
}

/** True when there's a real grammar for this path (i.e. highlighting applies). */
export function canHighlight(path) {
  return grammarForPath(path) !== 'plain';
}

/**
 * Tokenize `code` under the named grammar. Unknown grammars (and any internal
 * error) fall back to a single plain token, so callers can render the result
 * unconditionally.
 *
 * @param {string} code
 * @param {string} grammarKey
 * @returns {Token[]}
 */
export function highlight(code, grammarKey) {
  const rules = GRAMMARS[grammarKey];
  if (!rules) return [{ text: code, type: null }];
  try {
    return tokenize(code, rules);
  } catch {
    return [{ text: code, type: null }];
  }
}

// Exposed for tests.
export const GRAMMAR_KEYS = Object.keys(GRAMMARS);
