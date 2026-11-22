# QR quine

This symbol encodes a `data:` URL. Opening that URL runs a script that reads
`location.href` and draws the same symbol.

The payload is a version 40 QR code, error correction L, mask 0, byte mode.
That symbol holds 2953 bytes. `src/encode.js` is the page that gets copied
into the URL, with comments and spare whitespace removed. In a `data:text/html`
URL, Chrome percent-encodes `%`, `?`, `#`, `<`, `>`, and backticks, and the
page can read that encoded address back unchanged.

## Run locally

```bash
npm install
npm test
npm start
```

Open <http://localhost:3000>. Copy the data URL and paste it into the address
bar. Chrome blocks a link to a `data:` URL.
`src/quine.js` is that URL. Rebuild it, after changing `src/encode.js`, with:

```bash
npm run build
```

`npm test` checks the committed URL against that build.
