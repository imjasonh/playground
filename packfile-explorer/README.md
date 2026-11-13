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

Production is the GitHub Pages deploy of this directory. Fetches use the same
public CORS proxy as the git browser, `https://cors.isomorphic-git.org`. That
proxy streams the pack. It is a third party, so it can see the repository URL
and the bytes it relays. `npm start` can fetch a public repository through it.
Use **Open .pack** to load a local packfile (for example from
`.git/objects/pack/`) without the network, or reopen a previously saved pack
from IndexedDB.

## Fetch flow

1. Normalize the typed URL to a smart-HTTP base (`…/repo.git`). The repo field
   starts as `imjasonh/playground`.
2. `GET …/info/refs?service=git-upload-pack` through the CORS proxy.
3. Set the depth, which defaults to 1, then choose **Only default branch** or
   **All N branches**. Tags are not fetched.
4. `POST …/git-upload-pack` with a `want` per chosen branch. The status line
   follows the server while it enumerates, counts, and compresses, then the
   bytes received (and the rate, when the body streams), then parsing and
   resolving. A bar fills in when the total is known.
5. Demultiplex the side-band-64k response into raw pack bytes.
6. Parse every entry (in a Web Worker when available, so the tab stays
   responsive), inflate zlib members (recording compressed length), resolve
   ofs- and ref-delta chains, and compute each object's SHA-1 oid.
7. Persist the raw pack + refs in IndexedDB under the repo URL so you can reopen
   it without another fetch.

## Explore

The window has two panes that scroll on their own: a navigator on the left and
an inspector on the right. On a narrow screen they stack and the page scrolls.

The navigator has three tabs:

- **Objects**: every object in the pack, labeled by its path in the HEAD tree
  (or a commit's subject, or a tag's name). Search by oid prefix or path, filter
  by type and storage (whole, ofs-delta, ref-delta), and sort by pack order,
  size, depth, or type. **More filters** adds reachability and blob author. The
  list shows the first 500 matches; narrow the filters to reach the rest.
- **Paths**: the HEAD tree flattened to file paths. Search by substring or a
  `*` glob, then click a path to open its blob.
- **Refs**: the advertised refs. Click one to open the object it points at.

The inspector has two views:

- **Overview**: headline numbers (object count, packed and inflated size,
  delta share, maximum delta depth), then cards for object types, the largest
  objects (rank by packed size, inflated size, delta savings, or depth), blobs
  by author, the delta depth histogram, reachability from the fetched refs, and
  the pack version and trailer checksum. Click a type to list its objects, an
  author to list their blobs, or the unreachable count to list those objects.
  With more than one saved pack, **Compare with another saved pack** diffs two
  packs (added, removed, and the size changes).
- **Object**: the selected object's type, path or subject, oid, and storage
  facts (offset, packed and inflated size, delta base, reachability). Its
  content comes first: a commit's message, author, tree, and parents; a tree's
  entries; a tag; or a blob as text, an image preview (PNG, JPEG, GIF, WebP,
  BMP, or SVG), or a hex dump. A deltified blob colors each byte by the copy
  instruction that produced it, with inserts in white. Below that, the delta
  chain (root base to this object), the delta's copy and insert totals, and
  collapsed sections for the delta instructions, the inflated delta stream, the
  base bytes the delta reuses, and the raw pack entry (header, base pointer,
  zlib). **Download loose object** writes the object as a zlib loose file you
  can drop into `.git/objects/`.

Blob authorship credits each blob to the author of the commit that introduced
it. Blobs in trees at a shallow-fetch boundary go under `(shallow boundary)`;
blobs no commit points at go under `(no commit)`.

The toolbar carries **back** and **forward** through the objects you've viewed,
a **jump to full oid** box, and **Copy link** for the current `?pack=#oid` URL.
Any oid link (parent, tree entry, delta base, chain link) opens that object.

## Shareable links

After a pack is saved in IndexedDB, the address bar carries its id in the
`pack` query parameter (the repo base URL, or `file://…` for a local open). The
selected object's oid is in the hash (`#…`). Copy the URL to share, or refresh
to reopen the same pack and selection in this browser.

## Size limits

**Fetching over the network is capped by the CORS proxy.** The public proxy
(`https://cors.isomorphic-git.org`) relays the `git-upload-pack` response, and
the playground proxy worker stops relaying at **25 MiB**, returning HTTP 413
above that. A depth-1 fetch of a busy repository can already exceed it. To stay
under the cap, lower the depth, fetch fewer refs, or point at a smaller
repository. For anything larger, download the pack and use **Open .pack** — a
local pack has no proxy and no size cap.

**Opening a local `.pack` takes one of two paths by size:**

- **Under 256 MiB**: the whole file is read into memory and parsed, the same
  path as a fetched pack, and saved to IndexedDB so you can reopen it.
- **256 MiB and larger**: the pack is streamed. The app indexes it by reading
  windows from the file, keeps only each object's metadata and the
  commit/tree/tag contents resident, and re-reads a blob's bytes from the file
  when you open that blob. This path is not saved to IndexedDB (it's too large)
  and skips the trailer checksum (it doesn't hash the whole file). Resident
  memory tracks the object count rather than the pack size, so a multi-gigabyte
  pack with a few million objects stays explorable; the content and hex views
  for a single object over 64 MiB show its metadata only.

## Test

```bash
npm test
```

Coverage includes pkt-line framing and the streaming side-band reader, the
upload-pack request body, delta apply/parse, base/result segment mapping, delta
chains, reachability and tree-path walking, leaderboards, per-author blob
attribution, pack-trailer verification, two-pack diff, loose-object export,
image sniffing, synthetic pack round-trips (ofs- and ref-delta), oid
computation against git's known empty-blob hash, the streaming index matching
the in-memory parser object-for-object, and a live `git repack` fixture when
`git` is on `PATH`.

## Notes

- IndexedDB, not WebSQL. WebSQL is gone from current browsers; IndexedDB is the
  supported local store. The raw pack is saved and re-parsed on open rather than
  persisting the resolved object graph.
- Thin packs (ref-deltas whose base isn't in the pack) show up as unresolved
  entries. A normal shallow fetch from a public host usually isn't thin.
- Depth defaults to 1. Raise it when you want more history. A fetched pack is
  held in memory while it is parsed; a large local pack is streamed instead (see
  [Size limits](#size-limits)).
- **Open .pack** handles both modest and large packs. A pack under 256 MiB is
  read whole and parsed in memory, the same path as a fetched pack. A pack of
  256 MiB or more is streamed: it's indexed by reading windows from the file,
  only object metadata and commit/tree/tag content stay resident, and a blob's
  bytes are re-read from the file when you open it, so a multi-gigabyte pack
  stays explorable. See [Size limits](#size-limits) for what that trades off.
