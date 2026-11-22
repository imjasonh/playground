// Splits rendered text into the words a reader clicks through.

/**
 * Elements that end a word: a word never continues into, out of, or across
 * one of these. Every other element is inline, so `<b>end</b>.` is one word.
 */
const BLOCKS = new Set([
  'ADDRESS', 'ARTICLE', 'ASIDE', 'BLOCKQUOTE', 'BR', 'CAPTION', 'DD',
  'DETAILS', 'DIV', 'DL', 'DT', 'FIGCAPTION', 'FIGURE', 'FOOTER', 'H1', 'H2',
  'H3', 'H4', 'H5', 'H6', 'HEADER', 'HR', 'LI', 'MAIN', 'NAV', 'OL', 'P',
  'PRE', 'SECTION', 'SUMMARY', 'TABLE', 'TBODY', 'TD', 'TFOOT', 'TH', 'THEAD',
  'TR', 'UL',
]);

/**
 * Finds the words in `pieces` of text, such as DOM text nodes in reading
 * order. A word is a run of characters that aren't whitespace, so punctuation
 * stays with the word it touches. A word continues from one piece into the
 * next when nothing separates them: no whitespace, and no `breakBefore` on
 * the second piece.
 * @param {!Array<{text: string, breakBefore: boolean}>} pieces
 * @return {!Array<!Array<{piece: number, start: number, end: number}>>} Each
 *     word as the slices of the pieces it covers, in reading order.
 */
export function findWords(pieces) {
  const words = [];
  // The word that the next piece continues if that piece starts with one.
  let open = null;
  pieces.forEach((piece, i) => {
    if (piece.breakBefore) open = null;
    if (!piece.text) return;
    for (const match of piece.text.matchAll(/\S+/g)) {
      const slice = {
        piece: i,
        start: match.index,
        end: match.index + match[0].length,
      };
      if (open && match.index === 0) {
        open.push(slice);
      } else {
        open = [slice];
        words.push(open);
      }
    }
    if (/\s$/.test(piece.text)) open = null;
  });
  return words;
}

/**
 * @param {!Node} node
 * @param {!Element} root
 * @return {!Element} The nearest block element around `node`, or `root`.
 */
function blockOf(node, root) {
  let element = node.parentElement;
  while (element && element !== root && !BLOCKS.has(element.tagName)) {
    element = element.parentElement;
  }
  return element ?? root;
}

/**
 * Wraps each word under `root` in `<span class="word">` elements. A word that
 * crosses inline elements, like `<a>Friday</a>.`, gets a span in each.
 * @param {!Element} root
 * @return {!Array<!Array<!HTMLSpanElement>>} Each word's spans, in reading
 *     order.
 */
export function wrapWords(root) {
  const doc = root.ownerDocument;
  const walker = doc.createTreeWalker(
    root,
    NodeFilter.SHOW_ELEMENT | NodeFilter.SHOW_TEXT,
  );
  /** @type {!Array<!Text>} */
  const nodes = [];
  const pieces = [];
  let pendingBreak = false;
  let lastBlock = null;
  for (let node = walker.nextNode(); node; node = walker.nextNode()) {
    if (node instanceof Element) {
      if (BLOCKS.has(node.tagName)) pendingBreak = true;
      continue;
    }
    const text = /** @type {!Text} */ (node);
    const block = blockOf(text, root);
    nodes.push(text);
    pieces.push({
      text: text.data,
      breakBefore: pendingBreak || block !== lastBlock,
    });
    pendingBreak = false;
    lastBlock = block;
  }

  const words = findWords(pieces);
  /** @type {!Array<!Array<{start: number, end: number, word: number}>>} */
  const slicesByNode = nodes.map(() => []);
  words.forEach((slices, word) => {
    for (const {piece, start, end} of slices) {
      slicesByNode[piece].push({start, end, word});
    }
  });

  /** @type {!Array<!Array<!HTMLSpanElement>>} */
  const spans = words.map(() => []);
  nodes.forEach((node, i) => {
    const slices = slicesByNode[i];
    if (!slices.length) return;
    const text = node.data;
    const fragment = doc.createDocumentFragment();
    let at = 0;
    for (const {start, end, word} of slices) {
      if (start > at) fragment.append(text.slice(at, start));
      const span = doc.createElement('span');
      span.className = 'word';
      span.textContent = text.slice(start, end);
      fragment.append(span);
      spans[word].push(span);
      at = end;
    }
    if (at < text.length) fragment.append(text.slice(at));
    node.replaceWith(fragment);
  });
  return spans;
}
