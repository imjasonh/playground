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
3. Pick which refs to fetch — HEAD is preselected; check more branches or tags,
   or **Select all**. Set the depth (default 1) so the pack stays small.
4. `POST …/git-upload-pack` with a `want` per chosen ref. Side-band progress
   from the server streams into a live log as the pack arrives.
5. Demultiplex the side-band-64k response into raw pack bytes.
6. Parse every entry (in a Web Worker when available, so the tab stays
   responsive), inflate zlib members (recording compressed length), resolve
   ofs- and ref-delta chains, and compute each object's SHA-1 oid.
7. Persist the raw pack + refs in IndexedDB under the repo URL so you can reopen
   it without another fetch.

## Explore

The sidebar has four tabs.

- **Objects**: filter by type / delta kind / reachability, sort by offset /
  packed size / inflated size / depth, search by oid prefix.
- **Insights**: a leaderboard of the largest objects (rank by packed size,
  inflated size, delta savings, or depth), a per-type size breakdown, a delta
  depth histogram, a reachability summary (with a jump to unreachable objects),
  and the pack version / object count / verified trailer checksum.
- **Refs**: the advertised refs; click one to open the object it points at.
- **Paths**: the HEAD tree flattened to file paths; search by substring or a
  `*` glob and click a path to open its blob.

The detail pane shows object metadata plus:

- The **delta chain** (root base → … → this object) as jump links.
- Hex-editor views of the raw pack entry (header, base pointer, zlib) and the
  inflated delta stream (size headers, copy pointers, literal inserts). Hex
  bodies are keyboard-scrollable when focused.
- A **delta base** hex view coloring the bytes this delta reuses and greying the
  ones it dropped, with a reuse percentage.
- For resolved blobs, the structured commit/tree/tag view, the full blob text
  (copied bytes colored by source copy instruction, inserts in white), or an
  inline image preview for PNG/JPEG/GIF/WebP/BMP/SVG blobs.
- **Download loose object** writes the selected object as a zlib loose file you
  can drop into `.git/objects/`.

The detail toolbar carries **back/forward** through the objects you've viewed, a
**jump to full oid** box, and **Copy link** for the current `?pack=#oid` URL.
From Insights, **Compare with another pack** diffs two saved packs (added,
removed, and the size deltas).

- Tap any oid link (parent, tree entry, delta base, chain link) to jump.

## Shareable links

After a pack is saved in IndexedDB, the address bar carries its id in the
`pack` query parameter (the repo base URL, or `file://…` for a local open). The
selected object's oid is in the hash (`#…`). Copy the URL to share, or refresh
to reopen the same pack and selection in this browser.

## Test

```bash
npm test
```

Coverage includes pkt-line framing and the streaming side-band reader, the
upload-pack request body, delta apply/parse, base/result segment mapping, delta
chains, reachability and tree-path walking, leaderboards, pack-trailer
verification, two-pack diff, loose-object export, image sniffing, synthetic pack
round-trips (ofs- and ref-delta), oid computation against git's known empty-blob
hash, and a live `git repack` fixture when `git` is on `PATH`.

## Notes

- IndexedDB, not WebSQL. WebSQL is gone from current browsers; IndexedDB is the
  supported local store. The raw pack is saved and re-parsed on open rather than
  persisting the resolved object graph.
- Thin packs (ref-deltas whose base isn't in the pack) show up as unresolved
  entries. A normal shallow fetch from a public host usually isn't thin.
- Depth defaults to 1. Bump it only when you want more history; response size is
  capped by the CORS proxy (25 MiB by default).
