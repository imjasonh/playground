# ocidb — explore OCI container images with SQL

`ocidb` turns a container registry (Docker Hub by default) into a set of
read-only **SQLite virtual tables**, so you can explore image manifests, layers,
configs, build history, environment variables and more with plain SQL.

```console
$ ocidb query "SELECT os, architecture, variant FROM platforms WHERE reference = 'alpine'"
os     architecture  variant
-----  ------------  -------
linux  386
linux  amd64
linux  arm           v6
linux  arm           v7
linux  arm64         v8
linux  ppc64le
linux  riscv64
linux  s390x
(8 rows)
```

## How it works

Three pieces fit together:

- **[go-containerregistry](https://github.com/google/go-containerregistry)** reads
  manifests, indexes and config blobs from any OCI/Docker registry.
- **[go-sqlite-fdw](https://pkg.go.dev/github.com/values-conflict/go-sqlite-fdw/modernc)**
  is a framework for writing SQLite virtual tables in Go. We use the pure-Go
  `modernc` backend (`modernc.org/sqlite`), so there is **no CGo** and nothing to
  compile against libsqlite3.
- An on-disk **cache** sits in front of the registry so repeated and overlapping
  lookups don't burn through registry rate limits (see [Caching](#caching)).

Each `ocidb` table implements the `fdw.Source`/`fdw.Cursor` interface. A small
generic layer turns equality constraints on `HIDDEN` columns into the registry
coordinates a query needs (which image, which platform), pushes those down in
`BestIndex`, and materializes the resulting rows.

## Build & run

Requires Go 1.25+ (the `modernc` backend's minimum). From this directory:

```console
$ go build -o ocidb .
$ ./ocidb demo                 # a guided tour of fun Docker Hub queries
$ ./ocidb query "SELECT ..."   # run one query
$ ./ocidb shell                # interactive SQL prompt
$ ./ocidb schema [table]       # print virtual-table schema(s)
```

Common flags (for `query`, `shell`, `demo`):

| Flag | Default | Meaning |
|------|---------|---------|
| `--cache DIR` | `<user-cache>/ocidb` (or `$OCIDB_CACHE`) | where to cache registry data |
| `--ttl DUR` | `6h` | freshness window for tag lists & tag→digest resolution |
| `--format F` | `table` | `table`, `csv`, or `json` |

## Tables

Every table takes its target through **`HIDDEN` columns** that must be
constrained with `=` (just like SQLite's own table-valued functions). This keeps
us from ever trying to enumerate an entire registry, and makes the required
inputs explicit.

| Table | Required input | Optional input | Each row is… |
|-------|----------------|----------------|--------------|
| `tags` | `repository` | | one published tag |
| `manifest` | `reference` | | the manifest/index summary (one row) |
| `platforms` | `reference` | | one platform a multi-arch image supports |
| `layers` | `reference` | `platform` | one layer (digest + size) |
| `image` | `reference` | `platform` | the resolved image config (one row) |
| `history` | `reference` | `platform` | one build step (≈ a Dockerfile line) |
| `env` | `reference` | `platform` | one environment variable |
| `labels` | `reference` | `platform` | one label |
| `files` | `reference` | `platform`, `path` | one file/dir/symlink inside the image, optionally with its `content` |

- `reference` is any image reference: `nginx`, `python:3.12-slim`,
  `bitnami/redis`, `ghcr.io/owner/img@sha256:…` — short Docker Hub names are
  expanded to `index.docker.io/library/…:latest`.
- `repository` (for `tags`) is the repo without a tag, e.g. `library/nginx`.
- `platform` is optional and defaults to `linux/amd64`; set it like
  `WHERE platform = 'linux/arm64'`.

See full column lists with `ocidb schema`. For example:

```console
$ ocidb schema image
CREATE TABLE image(
  reference TEXT HIDDEN,
  platform TEXT HIDDEN,
  digest TEXT,
  config_digest TEXT,
  os TEXT,
  architecture TEXT,
  variant TEXT,
  created TEXT,
  author TEXT,
  docker_version TEXT,
  num_layers INTEGER,
  total_size INTEGER,
  user TEXT,
  working_dir TEXT,
  entrypoint TEXT,
  cmd TEXT,
  num_env INTEGER,
  num_labels INTEGER,
  num_exposed_ports INTEGER
);
```

### Constraint push-down & joins

Because the `reference`/`platform` constraints are pushed down in `BestIndex`,
you can drive a table from a list and it will fetch one image per row. Use a CTE
with a column list (SQLite doesn't support `(VALUES …) AS t(col)`):

```sql
WITH refs(ref) AS (VALUES ('alpine'), ('busybox'), ('debian'), ('ubuntu'))
SELECT refs.ref AS image,
       i.num_layers,
       printf('%.2f MB', i.total_size / 1048576.0) AS download_size
FROM refs
JOIN image i ON i.reference = refs.ref
ORDER BY i.total_size;
```

```
image    num_layers  download_size
-----    ----------  -------------
busybox  1           2.12 MB
alpine   1           3.67 MB
ubuntu   2           39.64 MB
debian   1           47.03 MB
(4 rows)
```

Both the constant `reference` and a per-row `platform` are pushed down, so this
fans out across architectures in one query:

```sql
WITH plats(platform) AS (VALUES ('linux/amd64'), ('linux/arm64'), ('linux/arm/v7'))
SELECT plats.platform,
       count(*) AS layers,
       printf('%.2f MB', sum(l.size) / 1048576.0) AS download_size
FROM plats
JOIN layers l ON l.reference = 'redis' AND l.platform = plats.platform
GROUP BY plats.platform;
```

```
platform      layers  download_size
--------      ------  -------------
linux/amd64   7       51.76 MB
linux/arm/v7  7       38.22 MB
linux/arm64   7       51.63 MB
(3 rows)
```

## Reading files inside images

The `files` table exposes the **filesystem inside an image**: one row per tar
member (file, directory, symlink, …) across all of the resolved platform's
layers, with an optional `content` column holding the file's bytes.

```console
$ ocidb schema files
CREATE TABLE files(
  reference TEXT HIDDEN,
  platform TEXT HIDDEN,
  layer INTEGER,
  layer_digest TEXT,
  path TEXT,
  type TEXT,
  size INTEGER,
  mode TEXT,
  linkname TEXT,
  uid INTEGER,
  gid INTEGER,
  modtime TEXT,
  content TEXT
);
```

- `path` is the absolute path (`/etc/os-release`); `type` is one of `file`,
  `dir`, `symlink`, `hardlink`, `char`, `block`, `fifo`.
- `mode` is the octal permission string (`0644`, `4755` for setuid, …).
- `content` is the file body **as text**, and only for regular files that are
  valid UTF-8 and at most 1 MiB; larger or binary files report their `size` but
  a `NULL` content. Rows are **per layer**, so a path edited by a later layer
  appears once per layer that touches it (overlay/whiteout semantics are not
  merged).

This follows the approach described in dagdotdev's
[registry explorer](https://github.com/jonjohnsonjr/dagdotdev/blob/main/pkg/explore/README.md):
walk a layer's tar exactly once to build a **table of contents** (the tar
headers), and lean on content-addressability to cache aggressively. Because a
layer is named by digest and never changes, both its blob and its derived TOC
are cached **forever** — listing files for an already-seen layer costs zero
network and zero decompression.

### Searching files efficiently

Two things keep file search cheap:

1. **Content is only read when you ask for it.** `BestIndex` inspects which
   columns the query references; file *bodies* are decompressed only when the
   `content` column is selected. Metadata-only searches (by `path`, `size`,
   `mode`, `type`, …) read just the cached tables of contents.
2. **`path =` is pushed down.** An equality on `path` is bound at the source, so
   `WHERE path = '/etc/passwd'` reads a single file rather than every body in
   the layer.

Find which images ship a binary (metadata only — reads just the TOCs):

```sql
WITH refs(ref) AS (VALUES ('alpine'), ('busybox'), ('debian'), ('ubuntu'))
SELECT ref AS image,
       CASE WHEN EXISTS (
         SELECT 1 FROM files WHERE reference = refs.ref AND path = '/usr/bin/bash'
       ) THEN 'yes' ELSE 'no' END AS has_bash
FROM refs ORDER BY ref;
```

```
image    has_bash
-----    --------
alpine   no
busybox  no
debian   yes
ubuntu   yes
(4 rows)
```

Read a file's contents across several images at once (path push-down means only
that one file is cracked open per image):

```sql
WITH refs(ref) AS (VALUES ('alpine'), ('debian'), ('ubuntu'))
SELECT refs.ref AS image,
       replace(trim(f.content), char(10), ' | ') AS os_release
FROM refs
JOIN files f ON f.reference = refs.ref AND f.path = '/usr/lib/os-release';
```

Hunt for setuid/setgid binaries (a leading octal digit of 1–7 means a special
permission bit is set):

```sql
SELECT path, mode, size FROM files
WHERE reference = 'debian' AND type = 'file'
  AND substr(mode, 1, 1) IN ('1','2','3','4','5','6','7')
ORDER BY mode DESC, path;
```

```
path              mode  size
----              ----  ----
/usr/bin/chfn     4755  70888
/usr/bin/passwd   4755  118168
/usr/bin/su       4755  84360
…
/usr/bin/chage    2755  113848
```

> The first time you touch a layer, its (compressed) blob is downloaded and
> cached on disk; subsequent file reads come straight from that cache. This is
> the one place `ocidb` may pull whole layers — the explorer instead serves
> single files with HTTP Range requests over a gzip seek index, an optimization
> that matters for a hosted service but less so for a local cache.

## Caching

Everything fetched is written under the cache directory:

- **Content addressed by digest** — manifests (`manifests/`), config + layer
  blobs (`blobs/`) and the per-layer tables of contents (`toc/`) — is immutable
  and cached **forever**.
- **Mutable lookups** — tag lists (`tags/`) and tag→digest resolution (`refs/`) —
  are cached with a **TTL** (default 6h, `--ttl`).

Every command prints a one-line cache summary to stderr, e.g.
`[cache] 42 hit(s), 0 network fetch(es)`. Re-running a query is served entirely
from disk; delete the cache directory (or lower `--ttl`) to force a refresh.

This is what keeps `ocidb` friendly to Docker Hub's anonymous pull-rate limits:
resolving the same image, or joining several queries that touch overlapping
blobs, hits the network at most once per unique digest.

## A few more fun queries

Reverse-engineer the build steps of an image (its "Dockerfile"):

```sql
SELECT ordinal, created_by FROM history WHERE reference = 'alpine' AND empty_layer = 0;
```

What environment does the official Postgres image bake in?

```sql
SELECT key, value FROM env WHERE reference = 'postgres' ORDER BY key;
```

```
key           value
---           -----
GOSU_VERSION  1.19
LANG          en_US.utf8
PATH          /usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/lib/postgresql/18/bin
PGDATA        /var/lib/postgresql/18/docker
PG_MAJOR      18
PG_VERSION    18.4-1.pgdg13+1
(6 rows)
```

The five largest layers in an image:

```sql
SELECT ordinal, printf('%.1f MB', size / 1048576.0) AS size_mb
FROM layers WHERE reference = 'python:3.12-slim'
ORDER BY size DESC LIMIT 5;
```

All of these (and more) ship as `ocidb demo`. The query files live in
[`queries/`](queries/); `ocidb demo --list` prints them without running.

## Authentication & rate limits

By default `ocidb` uses go-containerregistry's default keychain: if you've run
`docker login`, those credentials (and their higher rate limits) are used;
otherwise it falls back to anonymous access. Anonymous Docker Hub pulls are
limited (currently ~100 manifest pulls / 6h per IP), which is exactly why the
cache exists.

## Testing

```console
$ go test ./...
```

Tests never touch the network: `internal/registrytest` provides an in-memory
`registry.Backend` with a deterministic multi-arch fixture, and the table tests
run real SQL against it through an in-memory SQLite database.

## Note on the playground

Unlike the other entries in this repo, `ocidb` is a command-line Go tool, not a
static browser app — it has no `index.html`, so the deploy/preview/test
workflows intentionally don't pick it up.
