# QR quine

The symbol on the page encodes that page's address. Scanning it opens the
page, which draws the same symbol. The iPhone Camera app opens that address.

The data URL is the same page with no server. Opening it runs a script that
reads `location.href` and draws the same symbol. The Camera app reads that
symbol and shows "No usable data found". It does not open a `data:` URL.
Paste the URL into the address bar.

The data URL is a version 40 QR code, error correction L, mask 0, byte mode.
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
