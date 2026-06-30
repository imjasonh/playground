# gitsql — query a git repo with SQL

`gitsql` exposes a git repository as a set of read-only **SQLite virtual tables**
and lets you explore its history, files, authors, tags, and line-by-line blame
with plain SQL.

It wires three pieces together:

- **[go-git](https://github.com/go-git/go-git)** — all git access (clone, log,
  trees, diffs, blame), in pure Go.
- **[go-sqlite-fdw/modernc](https://pkg.go.dev/github.com/values-conflict/go-sqlite-fdw/modernc)**
  — a framework for writing SQLite virtual tables (the SQLite equivalent of a
  foreign data wrapper). You implement one small `Source`/`Cursor` interface and
  it wires your data into SQLite.
- **[modernc.org/sqlite](https://pkg.go.dev/modernc.org/sqlite)** — a pure-Go
  SQLite engine, so there's **no CGo** and no dependency on a system SQLite.

Remote repositories are cloned **once** (bare) into a local cache and reused on
later runs, so re-querying the same repo is fast and works offline.

> This is a CLI tool, not a browser app — the [`index.html`](index.html) in this
> directory is a static showcase page (with real example output) for the
> playground's GitHub Pages site.

## Build

Requires Go 1.25+ (the toolchain auto-downloads via `GOTOOLCHAIN=auto` if your
`go` is older):

```bash
cd gitsql
go build -o gitsql .
```

## Usage

```
gitsql [flags] [repo] [sql]
```

- `repo` is a local path, a clone URL, or an `owner/repo` GitHub shorthand
  (default `.`).
- `sql`, if given, is run and the results printed; otherwise gitsql reads SQL
  from stdin (when piped) or opens an interactive prompt.
- **Flags must come before the positional `repo`/`sql`.**

```bash
# run a bundled example against a public repo (clones + caches on first run)
gitsql --example top-authors BurntSushi/ripgrep

# your own SQL, positional form
gitsql BurntSushi/ripgrep "SELECT count(*) FROM commits WHERE is_merge"

# pipe a multi-statement script
echo "SELECT name FROM refs WHERE is_branch;" | gitsql .

# interactive prompt over the current repo
gitsql .
```

### Flags

| Flag | Description |
|------|-------------|
| `-q`, `-query <sql>` | SQL to run |
| `-file <path>` | read SQL from a file (`-` for stdin) |
| `-example <name>` | run a built-in example (see `-list-examples`) |
| `-list-examples` | list the built-in examples and exit |
| `-schema` | print every table's schema and exit |
| `-format <fmt>` | `table` (default), `csv`, `tsv`, `json`, `md` |
| `-max-width <n>` | truncate table cells (0 = unlimited; default 60) |
| `-cache <dir>` | cache directory (default `<user cache>/gitsql`) |
| `-update` | fetch new commits for a cached repo before querying |
| `-offline` | never hit the network; require a cached clone |
| `-quiet` | suppress clone/fetch progress |

### Interactive prompt

Statements end with `;`. Dot-commands: `.tables`, `.schema [table]`,
`.examples`, `.example <name>`, `.format <fmt>`, `.help`, `.quit`.

## Tables

| Table | One row per… | Notable columns |
|-------|--------------|-----------------|
| `commits` | commit reachable from a ref (HEAD by default) | `hash, author_name, author_email, author_when, author_unix, committer_*, message, summary, parents, parent_hashes, tree_hash, is_merge` |
| `refs` | branch / tag / remote / HEAD ref | `name, short_name, type, target, hash, is_branch, is_tag, is_remote, is_head` |
| `tags` | tag (annotated or lightweight) | `name, full_name, type, target, tagger_name, tagger_email, tagger_when, message, tag_hash` |
| `files` | file in the tree at a ref | `path, name, mode, type, size, blob_hash, is_binary, lines` |
| `commit_files` | file changed by a commit (`--numstat`) | `commit_hash, path, old_path, change, additions, deletions, binary` |
| `blame` | line of a file (**requires** `WHERE path = '…'`) | `path, line_no, content, commit_hash, author_name, author_email, author_when, author_unix` |

Run `gitsql -schema` to see the exact `CREATE TABLE` for each.

### Hidden `ref` column

`commits`, `files`, `commit_files`, and `blame` accept a hidden `ref` column to
pick the ref/revision to read (branch, tag, short or full hash). It defaults to
HEAD:

```sql
SELECT path, lines FROM files WHERE ref = 'v13.0.0' ORDER BY lines DESC LIMIT 5;
SELECT count(*) FROM commits WHERE ref = 'origin/feature-branch';
```

### Timestamps

Each `*_when` column is the author's/committer's **wall-clock** time with no
zone, so SQLite date functions report their *local* clock:

```sql
SELECT strftime('%H', author_when) AS hour, count(*) FROM commits GROUP BY hour;
```

The matching `*_unix` column is the true epoch (UTC) for ordering and interval
math.

### Querying more than one repo

Each table is also a SQLite module you can bind to an explicit repo, which lets
you JOIN or UNION across repositories in one session:

```sql
CREATE VIRTUAL TABLE rg  USING git_commits('BurntSushi/ripgrep');
CREATE VIRTUAL TABLE fd  USING git_commits('sharkdp/fd');
SELECT 'ripgrep' AS repo, count(*) FROM rg
UNION ALL
SELECT 'fd', count(*) FROM fd;
```

Modules: `git_commits`, `git_refs`, `git_tags`, `git_files`, `git_commit_files`,
`git_blame`. The first `USING(...)` argument is the repo spec.

## Examples

The [`queries/`](queries) directory holds the bundled examples (embedded into
the binary). List them with `gitsql -list-examples` and run one with
`gitsql --example <name> <repo>`:

| Name | What it shows |
|------|---------------|
| `summary` | commits / branches / tags / files and the active span |
| `top-authors` | most prolific authors by commit count |
| `commits-by-hour` | commit activity by hour of the author's local clock |
| `commits-by-weekday` | commit activity by weekday |
| `lines-by-author` | net lines per author (a JOIN of `commit_files` + `commits`) |
| `churn` | files with the most churn across all history |
| `biggest-files` | largest text files tracked at HEAD |
| `code-by-dir` | lines of code by top-level directory |
| `recent-tags` | most recent tags (releases) |
| `blame-readme` | who owns the most lines of `README.md` |

## Caching

- Remote repos are bare-cloned to `<cache>/gitsql/repos/<host>/<owner>/<repo>`
  and reused. `--update` fetches; `--offline` requires an existing clone.
- Local paths are opened in place (never copied).
- Expensive derived data (per-commit numstat diffs) is memoized in memory for
  the life of the process, so a full-history `commit_files` scan followed by a
  `JOIN` doesn't recompute diffs.

## Architecture

```
internal/gitrepo/   repo spec → opened go-git repository; local clone cache;
                    memoized per-commit file-change stats
internal/tables/    one fdw.Source per table (commits, refs, tags, files,
                    commit_files, blame); BestIndex pushes down equality on
                    hash / commit_hash / path / ref
main.go             CLI: flags, register modules, create tables, run SQL / REPL
printer.go          table / csv / tsv / json / markdown output
queries/*.sql       embedded example queries
```

## Tests

```bash
go test ./...
```

Tests are hermetic and need no network: they build a small repository on the fly
with go-git (two commits by different authors, a binary file, lightweight and
annotated tags, a branch) and run real SQL against every table, including the
hash/path/ref pushdowns and a cross-table JOIN.

## Limitations

- Read-only. The tables never write to the repo.
- `blame` and full-history `commit_files` scans are O(history) and can be slow on
  very large repositories; prefer pushing down `commit_hash`/`path`, or scope
  with `WHERE ref = …`.
- Rename detection in `commit_files` follows go-git's default diff behavior.
