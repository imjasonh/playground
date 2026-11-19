# Read receipt

Paste a Markdown doc and read it one word at a time. Each word stays muted
until you click it, or press Right Arrow or Space, and the highlight moves to
the next word. Holding a key down does nothing: each word takes its own press.

After the last word, you get a receipt link to share. The link holds the doc
and a proof that someone clicked through every word of it, how long that
took, and when they finished. Opening the link shows the doc under a banner
that says whether the proof checks out.

## The proof isn't secure

The proof is a SHA-256 hash of a secret, the doc, the reading time, and the
finish time. The secret is a constant in [`src/receipt.js`](src/receipt.js),
so anyone who reads the source can make a receipt for a doc they never
opened. The receipt shows that someone clicked through the doc, or went to
some trouble to fake it. Changing the doc or either time in a link makes the
check fail. Version 1 links, made before receipts held the finish time, still
check out, without a finish time.

## Privacy

The doc lives in the link's fragment (the part after `#`), compressed with
`deflate-raw`. Browsers don't send the fragment to the server, so the doc
never leaves your browser unless you share the link. Long docs make long
links.

## Safe rendering

[marked](https://marked.js.org/) turns the Markdown into HTML, and the
browser's [Sanitizer API](https://developer.mozilla.org/docs/Web/API/HTML_Sanitizer_API)
cleans it. Browsers without `Element.setHTML()` use
[DOMPurify](https://github.com/cure53/DOMPurify) instead. Scripts, event
handlers, forms, frames, media, and inline styles are removed. Images become
links, so a doc can't load a tracking pixel. The page's Content Security
Policy also blocks inline scripts and images from other origins.

Both libraries are copied into `vendor/` by `npm run vendor`, so the page has
no build step.

## Run locally

```bash
cd read-receipt
npm install
npm start
```

Then open <http://localhost:3000>.

## Test

```bash
npm test
```

The tests cover word splitting, the reader's key rules and timing, receipt
encoding and verification, and turning images into links. Sanitizing needs a
browser, so the tests don't cover it.

## Update the vendored libraries

```bash
npm install
npm run vendor
```
