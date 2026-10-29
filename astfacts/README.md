# astfacts (prototype)

A multi-language code-facts tool that answers one question first: **which
function parameters does every call pass the same value?** Such a parameter is
a candidate for removal. The finding is only evidence — whether removing it is
right depends on facts the tool surfaces so an agent (or you) can judge.

This is a prototype to evaluate the idea, not a finished app. It parses with
tree-sitter, so it covers many languages out of the box rather than one.

## Why it exists

The headline finding is cheap to state and easy to get wrong:

- `applySyncExecutor(exec, notify)` is called 4 times, always with `notify=true`
  → drop the parameter and inline `true`. Safe: unexported, one definition.
- `Apply(obj=true)` is also "always true" at some position, but it is exported,
  **4 definitions share the name**, and the name is referenced as a value. That
  is not "remove it" — it is "the in-tree callers are uniform; the real callers
  or tests are elsewhere," exactly the public-API caveat.

So the tool reports, per candidate: the value and its **kind** (a literal like
`true`/`0`/`"x"` is a strong signal; a bare identifier like `t` is usually just
a shared variable name, not one value), whether the definition is in the tree,
export status, how many definitions share the name, and a used-as-value
estimate. A confidence tier folds those together.

## Two front-ends, one engine

- **CLI** (`astfacts.py`) — one-shot answers. Good when you just want the list.
- **MCP server** (`mcp_server.py`) — the same engine over newline-delimited
  JSON-RPC, which **parses the tree once and caches the index**, so an agent can
  ask many follow-up questions in a session (value distribution, call sites,
  symbol facts) without reparsing. That statefulness is the reason to prefer the
  server when the workflow is "explore the facts and decide," not "print once."

## Usage

Install the parsers once:

```bash
pip install --break-system-packages "tree-sitter>=0.21,<0.22" tree-sitter-languages
```

CLI:

```bash
python3 astfacts.py constants <path> --min-calls 3 --literals-only
python3 astfacts.py --lang go symbol <path> applySyncExecutor
python3 astfacts.py --lang go arg-values <path> applySyncExecutor 1
python3 astfacts.py --lang go call-sites <path> applySyncExecutor
```

MCP (stdio): run `python3 mcp_server.py` and speak JSON-RPC, or point an MCP
client at it. Tools: `constant_arguments`, `argument_values`, `call_sites`,
`symbol_info`.

## Languages

Call-site aggregation works for every language with a node mapping in
`analyzer.py` (`SPECS`): Go, Python, JavaScript, TypeScript, Rust, Java, C, C++,
Ruby. Adding a language is one `LangSpec` entry. tree-sitter links ~20 more
grammars, so coverage is cheap to extend.

## Honest limitations (what a production version must fix)

- **Values compare as normalized source text, not resolved values.** `true` and
  `1 == 1` look different; two different locals both named `t` look the same.
  This is why bare-identifier candidates are downranked and literals lead.
- **Binding is by callee name + arity, not resolved symbol.** Same-named
  functions in different scopes share a bucket. The `def_count` field flags when
  a bucket is contaminated; it does not de-contaminate it.
- **Export / used-as-value are heuristics**, not type-checked facts.
- **Keyword/named arguments are ignored** past the first one; positional only.
- Java/Ruby mappings are present but under-tested here (little such code in this
  repo).

## If this graduates

The natural home is `pasta/` (the repo's tree-sitter analyzer): add
value-aggregating facts plus an "all values equal" check to its engine, author
the call/def shapes as CUE per language, and expose results through the same MCP
surface. That reuses pasta's wasm-hosted grammars and cross-file fact store
instead of a second parser stack. This prototype stands alone only to evaluate
whether the finding and the explore-the-facts workflow are worth that.
