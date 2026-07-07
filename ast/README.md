# ast

`ast` is a cross-language, structural **search-and-rewrite** command-line tool
built on [tree-sitter](https://tree-sitter.github.io/tree-sitter/). It parses
source code in any of its 31 supported languages, selects AST nodes using
tree-sitter's own **query language**, and can rewrite the matched nodes and
write the result back to disk.

Because it operates on the syntax tree rather than on lines of text, `ast` can
express edits like "rename every call to `foo`", "delete this import", or "add a
doc comment before each function" precisely, without brittle regexes.

- **Native Go, no external tools.** Every grammar is compiled into the binary
  via cgo (through [`go-tree-sitter`](https://github.com/smacker/go-tree-sitter)).
  There is no runtime download and no separate parser process — one `ast` binary
  parses every language below.
- **One selector language for every language.** The selector is a tree-sitter
  query, the same S-expression pattern language used by editors and the
  `tree-sitter` CLI.
- **Faithful rewrites.** Edits are applied as text splices at node byte ranges,
  so formatting, comments, and whitespace outside the edited spans are preserved
  exactly.

## Build

```bash
cd ast
go build -o ast .      # requires a C compiler (cgo)
go test ./...
```

`ast` is a Go command-line app; it is not deployed to GitHub Pages.

## Usage

```
ast languages                                     list supported languages and extensions
ast kinds     [-l lang]                           list normalized node kinds (--kind vocabulary)
ast tree      [-l lang] <file>                    print the syntax tree (S-expression)
ast query     -q QUERY [-l lang] <file>...        print AST nodes matching a selector
ast query     --kind KIND [-l lang] <file>...     print AST nodes by normalized kind
ast rewrite   -q QUERY [ops] [-w] <file>...       rewrite matched nodes
ast rename    --to NEW (--at L:C | --name OLD) [-w] <file>   scope-aware rename
```

The language is inferred from the file extension; override it with `-l/--lang`.
Pass `-` as the file to read from stdin (requires `-l`).

### `ast tree` — explore the syntax tree

Use this to discover the node types and field names you need for a query.

```bash
$ ast tree main.go
source_file [1:1-12:1]
  package_clause [1:1-1:13]
    package_identifier [1:9-1:13]  "main"
  function_declaration [5:1-7:2]
    name: identifier [5:6-5:11]  "greet"
    parameters: parameter_list [5:11-5:24]
    ...
```

`--sexp` prints the raw one-line S-expression; `-a/--all` includes anonymous
(unnamed) nodes such as punctuation and keywords.

### `ast query` — find nodes (the selector)

The selector is a tree-sitter query. Add one or more `@captures` to name the
nodes you care about:

```bash
# Every Go function name
$ ast query -q '(function_declaration name: (identifier) @name)' main.go
main.go:5:6: @name (identifier) "greet"
main.go:9:6: @name (identifier) "main"

2 node(s) matched
```

Queries support tree-sitter **predicates**:

```bash
# Every identifier literally equal to "foo"
$ ast query -q '((identifier) @id (#eq? @id "foo"))' main.go

# Function names matching a regex
$ ast query -q '((function_declaration name: (identifier) @n) (#match? @n "^Test"))' main_test.go
```

Flags: `-c/--capture NAME` shows only one capture; `--json` emits structured
results (with byte offsets and row/column ranges) for scripting.

#### Selecting by normalized kind (`--kind`)

Writing a raw query means knowing each grammar's node names
(`function_declaration` in Go, `function_item` in Rust, `function_definition`
in Python…). Instead you can select by a **normalized, cross-language kind** —
an idea borrowed from LSP's `SymbolKind` vocabulary:

```bash
# Every function definition, regardless of language
$ ast query --kind function main.go
$ ast query --kind function app.py
$ ast query --kind function lib.rs

# Multiple kinds at once
$ ast query --kind function --kind call app.py
app.py:1:5: @function (identifier) "helper"
app.py:2:12: @call (identifier) "compute"
```

Run `ast kinds` to see the full vocabulary (`function`, `method`, `class`,
`struct`, `interface`, `enum`, `type`, `constant`, `variable`, `field`,
`module`, `import`, `call`, `comment`, `string`, `number`, `keyword`,
`parameter`), and `ast kinds -l <language>` to see which are available for a
language.

`--kind` is powered by curated `tags.scm` / `highlights.scm` queries and is
available for **go, python, javascript, typescript, tsx, and rust**. Other
languages fall back to raw `-q` queries. `--kind` and `-q` are mutually
exclusive.

### `ast rewrite` — change nodes

`rewrite` runs the same selector, then applies one or more operations to the
captured nodes. Each operation targets a `@capture` from the query and may be
repeated:

| Operation | Meaning |
|-----------|---------|
| `--replace @cap=TEXT` | replace the captured node's text with `TEXT` |
| `--delete @cap` | delete the captured node |
| `--insert-before @cap=TEXT` | insert `TEXT` immediately before the node |
| `--insert-after @cap=TEXT` | insert `TEXT` immediately after the node |

`TEXT` may interpolate other captures **from the same match** with `{{name}}`
and understands the escapes `\n`, `\t`, `\r`, and `\\`.

By default the rewritten source is printed to stdout. The output mode is chosen
with these mutually-exclusive flags:

| Flag | Effect |
|------|--------|
| *(none)* | print the rewritten source to stdout |
| `-w`, `--write` | apply the edits and write them back to the files in place |
| `--diff` | print a unified diff to stdout **without applying** anything |
| `--patch=FILE` | write a unified diff to `FILE` **without applying** anything |

`--diff` and `--patch` are preview-only, so they never modify the source files;
combining either with `-w` is an error. The emitted diff is a standard unified
diff (with `a/`…`b/` headers) that `git apply -p1` or `patch -p1` can consume,
and `--patch` aggregates the diffs for all files into one patch file.

```bash
# Rename foo -> bar everywhere, in place
$ ast rewrite -q '((identifier) @id (#eq? @id "foo"))' --replace '@id=bar' -w *.go

# Preview: add a doc comment before every function, using its name
$ ast rewrite \
    -q '(function_declaration name: (identifier) @name) @fn' \
    --insert-before '@fn=// {{name}} ...\n' \
    --diff main.go

# Delete an import declaration
$ ast rewrite -q '(import_declaration) @imp' --delete '@imp' -w main.go

# Write a patch without applying it, then apply it with git
$ ast rewrite -q '((identifier) @id (#eq? @id "foo"))' --replace '@id=bar' --patch=rename.patch *.go
$ git apply -p1 rename.patch
```

Edits may be supplied in any order and are applied end-to-start so byte offsets
stay valid; overlapping edits are rejected.

### `ast rename` — scope-aware rename

`rewrite` is purely textual: `--replace @id=bar` renames *every* matching
identifier. `rename` is **scope-aware** — it renames a local binding and only
the references that resolve to it, like an editor's rename refactor. This is
modeled on LSP's semantic rename and is powered by curated `locals.scm`
scope/definition/reference queries.

Target the binding either by position (`--at LINE:COL`, 1-based, like clicking
an identifier) or by name (`--name OLD`, every local binding of that name):

```bash
# Rename the x in f() to n — the unrelated x in g() is left alone
$ ast rename --at 4:2 --to n --diff scope.go
--- a/scope.go
+++ b/scope.go
@@ -1,8 +1,8 @@
 func f() {
-	x := 1
-	println(x)
+	n := 1
+	println(n)
 }
 func g() {
 	x := 2      # untouched

# Rename a parameter and its uses (but not same-named locals in other scopes)
$ ast rename --name name --to label -w handler.py
```

Because it resolves references to definitions, `rename` renames recursive calls
(the function name is a binding), skips member accesses that merely share a name
(e.g. Python `obj.name`), and refuses to rename free symbols:

```bash
$ ast rename --at 5:2 --to nope scope.go
ast: scope.go: "println" ... does not resolve to a local binding
    (it may be a package-level, imported, or built-in symbol); use `ast rewrite` instead
```

`rename` takes exactly one file (locals are resolved per file), supports the
same `-w` / `--diff` / `--patch` output modes as `rewrite`, and is available for
**go, python, javascript, typescript, tsx, and rust**. For package-level or
cross-file symbols, use `ast rewrite` with an `#eq?` predicate.

## Supported languages

31 languages, each parsed by a grammar compiled into the binary:

```
bash  c  cpp  csharp  css  cue  dockerfile  elixir  elm  go  groovy  hcl  html
java  javascript  kotlin  lua  ocaml  php  protobuf  python  ruby  rust  scala
sql  svelte  swift  toml  tsx  typescript  yaml
```

Run `ast languages` (or `ast languages --json`) for the authoritative list with
file extensions and aliases (e.g. `js`, `ts`, `py`, `golang`, `c++`, `terraform`).

`query` (raw `-q`), `tree`, and `rewrite` (raw `-q`) work for **all** of these.
The higher-level features — `--kind` selectors and scope-aware `rename` — need
curated `tags.scm` / `highlights.scm` / `locals.scm` query files and currently
cover **go, python, javascript, typescript, tsx, and rust**. Adding a language
is just dropping new files into `internal/langs/queries/<lang>/` (no code
changes); see [`future-work.md`](future-work.md).

## How it works

1. **Parse.** The file's language is resolved (by extension or `-l`) and its
   grammar parses the bytes into a tree-sitter tree.
2. **Select.** The tree-sitter query runs against the tree; predicates
   (`#eq?`, `#match?`, …) are evaluated and each match's captures are collected.
3. **Rewrite.** Each operation turns a captured node's byte range into a text
   edit. Edits are sorted, checked for overlap, and spliced into the original
   bytes from the end backwards.

Rewrites deliberately splice source text rather than re-serialize a modified
tree: tree-sitter does not losslessly print trees back to source, and byte-range
splicing keeps every rewrite faithful to the original file.

`--kind` selection and `rename` add two more layers on top, both driven by
curated tree-sitter query files (the same convention editors use):

- **`--kind`** runs `tags.scm` (definitions/references) and `highlights.scm`
  (tokens) and maps their captures to a normalized cross-language vocabulary.
- **`rename`** runs `locals.scm` to build a scope tree with definitions and
  references, then resolves the target binding and rewrites only the
  occurrences that resolve to it.

## Testing

```bash
cd ast
go test ./...
```

The tests cover the language registry, the curated query files (each is
compiled against its grammar), the query engine and edit application, the
normalized-kind selectors and scope-aware rename (`internal/nav`), and the full
CLI, with a cross-language matrix that parses, queries, and rewrites Go, Python,
JavaScript/TypeScript/TSX, Rust, Java, C/C++, Ruby, C#, PHP, Bash, Lua, Scala,
Kotlin, Swift, YAML, TOML, CSS, SQL, HCL, and HTML.

### Golden CLI tests (testscript)

The CLI is also exercised end-to-end with
[`rogpeppe/go-internal/testscript`](https://pkg.go.dev/github.com/rogpeppe/go-internal/testscript).
Each script under `testdata/scripts/*.txtar` embeds source files in a given
language, runs `ast` against them exactly as a user would, and asserts the
output matches embedded **golden** files with `cmp`. `TestMain` registers the
`ast` binary as a command inside the scripts:

```go
func TestMain(m *testing.M) {
	os.Exit(testscript.RunMain(m, map[string]func() int{"ast": astMain}))
}

func TestScripts(t *testing.T) {
	testscript.Run(t, testscript.Params{Dir: "testdata/scripts", UpdateScripts: *update})
}
```

A script is a self-contained input + expected-output fixture. For example,
`testdata/scripts/query_go.txtar` selects Go function names and checks the
printed nodes:

```
# Select every Go function name with a tree-sitter query and compare the
# printed nodes against golden output.
ast query -q '(function_declaration name: (identifier) @name)' greet.go
cmp stdout query.golden

-- greet.go --
package main

import "fmt"

func greet(name string) string {
	return fmt.Sprintf("hello %s", name)
}

func main() {
	fmt.Println(greet("world"))
}
-- query.golden --
greet.go:5:6: @name (identifier) "greet"
greet.go:9:6: @name (identifier) "main"

2 node(s) matched
```

`testdata/scripts/rewrite_insert_js.txtar` inserts a JSDoc comment before every
JavaScript function, interpolating the captured name, and checks the rewritten
output:

```
ast rewrite -q '(function_declaration name: (identifier) @name) @fn' --insert-before '@fn=/** {{name}}() */\n' app.js
cmp stdout out.golden

-- app.js --
function add(a, b) {
  return a + b;
}

function sub(a, b) {
  return a - b;
}
-- out.golden --
/** add() */
function add(a, b) {
  return a + b;
}

/** sub() */
function sub(a, b) {
  return a - b;
}
```

And `testdata/scripts/rewrite_diff_rust.txtar` previews a Rust rename as a
unified diff and asserts the source file is left untouched:

```
# Preview a Rust rewrite as a unified diff (nothing is written to disk).
ast rewrite -q '((identifier) @id (#eq? @id "old_name"))' --replace '@id=new_name' --diff lib.rs
cmp stdout diff.golden

# The source file must be untouched by a --diff run.
grep 'fn old_name' lib.rs

-- lib.rs --
fn old_name() -> i32 {
    42
}

fn caller() -> i32 {
    old_name()
}
-- diff.golden --
--- a/lib.rs
+++ b/lib.rs
@@ -1,7 +1,7 @@
-fn old_name() -> i32 {
+fn new_name() -> i32 {
     42
 }
 
 fn caller() -> i32 {
-    old_name()
+    new_name()
 }
```

Other scripts cover Python (`#match?` predicate selection), a TypeScript syntax
tree, a raw-query in-place Go rename (`-w`), normalized `--kind` selection
(`query_kind.txtar`), scope-aware `rename` (`rename_scope.txtar`), writing a
patch file (`--patch`), and the `languages` command. `rewrite_patch_git_apply.txtar`
generates a patch and applies it with real `git` (via testscript's `exec`),
skipping itself with `[!exec:git] skip` when git is not installed. Regenerate the
golden output after intentional changes with:

```bash
go test -run TestScripts -update
```
