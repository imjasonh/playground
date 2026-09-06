# Packfile explorer

A browser app that fetches a git repository's packfile through the playground
CORS proxy, stores it locally, and lets you click through the objects: commits,
trees, blobs, tags, and the delta chains that produced them.

Point it at `owner/repo` (or any smart-HTTP URL). It runs a shallow
`git-upload-pack`, parses the resulting pack in the browser, resolves ofs- and
ref-deltas, and indexes everything so you can filter by type, delta kind, size,
and delta depth. Resolved blob and commit contents open in place.

## Why

Git's pack format is what actually ships over the wire and sits on disk after a
clone, but it's opaque: zlib-framed entries, ofs/ref deltas, and a SHA-1 trailer.
This app is a microscope for that format. Useful when you're profiling pack
size, checking how aggressively git deltified a file, or just wanting to see
what a shallow clone of a public repo actually contains.

## Run

```bash
cd packfile-explorer
npm install
npm run vendor   # copies pako into vendor/ for the browser
npm start        # http://localhost:3000
```

Production is the GitHub Pages deploy of this directory. The CORS proxy it calls
(`cors-proxy-worker.imjasonh.workers.dev`) only allows
`https://imjasonh.github.io`, so local `npm start` can fetch only if you point
at a proxy that allows `http://localhost:3000`. Use **Open .pack** to load a
local packfile (for example from `.git/objects/pack/`) without the network, or
reopen a previously saved pack from IndexedDB.

## Fetch flow

1. Normalize the typed URL to a smart-HTTP base (`…/repo.git`).
2. `GET …/info/refs?service=git-upload-pack` through the CORS proxy.
3. `POST …/git-upload-pack` with a `want` for HEAD (or the first heads ref) and
   `deepen N` (default 1) so the pack stays small enough to explore.
4. Demultiplex the side-band-64k response into raw pack bytes.
5. Parse every entry, inflate zlib members (recording compressed length),
   resolve ofs- and ref-delta chains, and compute each object's SHA-1 oid.
6. Persist the raw pack + refs in IndexedDB under the repo URL so you can reopen
   it without another fetch.

## Explore

- Object list: filter by type / delta kind, sort by offset / packed size /
  inflated size / depth, search by oid prefix.
- Stats: object count, packed vs inflated size, compression ratio, max delta
  depth, ofs/ref counts.
- Detail pane: metadata, delta instruction list (copy/insert), and for resolved
  objects the structured commit/tree/tag view or the full blob text.
- Delta objects also get hex-editor views of the raw pack entry (header, base
  pointer, zlib) and the inflated delta stream (size headers, copy pointers,
  literal inserts). Resolved blobs color copied bytes by source copy instruction
  and show literal inserts in white.
- Tap any oid link (parent, tree entry, delta base) to jump.

## Test

```bash
npm test
```

Coverage includes pkt-line framing, the upload-pack request body, delta
apply/parse, synthetic pack round-trips (ofs- and ref-delta), oid computation
against git's known empty-blob hash, and a live `git repack` fixture when `git`
is on `PATH`.

## Notes

- IndexedDB, not WebSQL. WebSQL is gone from current browsers; IndexedDB is the
  supported local store. The raw pack is saved and re-parsed on open rather than
  persisting the resolved object graph.
- Thin packs (ref-deltas whose base isn't in the pack) show up as unresolved
  entries. A normal shallow fetch from a public host usually isn't thin.
- Depth defaults to 1. Bump it only when you want more history; response size is
  capped by the CORS proxy (25 MiB by default).
