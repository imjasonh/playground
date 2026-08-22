# 🍝 pasta

`pasta` is a a polyglot static-analysis and structured edit tool.

Using `pasta`, you can express [AST](https://en.wikipedia.org/wiki/Abstract_syntax_tree) states that you want to flag to users. For example, an empty JS promise (`new Promise(() => {})`). Running `pasta js_empty_promise.cue index.js` would warn when this is found, highlighting this anti-pattern.

Rules can also define an automatix fix, in which case `pasta -fix` will make the edit directly.

`pasta` uses tree-sitter for parsing — the official C runtime and
grammars, compiled to WASM and driven from pure Go via
[wazero](https://github.com/tetratelabs/wazero) (so `go install` /
`CGO_ENABLED=0` still work) — and [CUE](https://cuelang.org/) for
rule schemas. It's heavily inspired by Go's
`golang.org/x/tools/go/analysis`.

The intention of `pasta` is to be able to declaratively describe rules for ASTs in any supported language, and quickly and reproducibly flag and fix findings. You can hook this up to your editor and/or CI to automatically flag and potentially fix violations of the rules you've specified.

## Status

Rules are defined in CUE files loaded at runtime. The framework ships generic predicates (parameterized over grammar specifics)
so semantic checks like "no later use" and "no named-result clash" are expressed in CUE.

The repo includes runnable **example analyzers** under [`analyzers/`](./analyzers/) —
style and correctness rules used to exercise the engine (and by the
[`e2e/`](./e2e/) smoke tests against real public repos). Single-language
rules use a `<lang>_` prefix; cross-language rules have no prefix.

Rules with a ✏️ include an automatic rewrite for `-fix`. Prefer the
diagnose-only examples when a rewrite would change runtime semantics
(for example `js_var_to_let` or `js_array_concat_spread`).

Run every example's testdata with:

```
go test ./...                 # includes analyzers/* via pasta_test.go
go run ./cmd/pasta test analyzers/js_double_equals
```

**Cross-language**

| Path | What it does |
|---|---|
| [todo_format](./analyzers/todo_format/todo_format.cue)                       | Flag `TODO`/`FIXME`/`XXX`/`HACK` comments without an owner: `TODO(name): ...` |
| [hardcoded_credentials](./analyzers/hardcoded_credentials/hardcoded_credentials.cue) | String literals that look like AWS access keys, GitHub tokens, Slack tokens, or PEM private keys |

**Go**

| Path | What it does |
|---|---|
| [go_iferr](./analyzers/go_iferr/go_iferr.cue) ✏️                              | Inline error assignment into the following `if err != nil` (port of [imjasonh/iferr-analyzer](https://github.com/imjasonh/iferr-analyzer); 20 positive + 18 negative test cases) |
| [go_negcmp](./analyzers/go_negcmp/go_negcmp.cue) ✏️                           | `!(a == b)` → `a != b`, `!(a != b)` → `a == b` |
| [go_errors_is_nil](./analyzers/go_errors_is_nil/go_errors_is_nil.cue) ✏️      | `errors.Is(err, nil)` → `err == nil` |
| [go_empty_else](./analyzers/go_empty_else/go_empty_else.cue) ✏️               | Drop `else { }` empty-else branches |
| [go_self_assignment](./analyzers/go_self_assignment/go_self_assignment.cue) ✏️ | Delete `x = x` self-assignments (vet [`assign`](https://pkg.go.dev/golang.org/x/tools/go/analysis/passes/assign)) |
| [go_panic_empty](./analyzers/go_panic_empty/go_panic_empty.cue)               | Flag `panic("")` with empty message |
| [go_test_context](./analyzers/go_test_context/go_test_context.cue) ✏️         | `context.Background()` / `context.TODO()` → `t.Context()` in `*_test.go` |
| [go_string_concat_empty](./analyzers/go_string_concat_empty/go_string_concat_empty.cue) ✏️ | Drop empty operand in `"" + x` / `x + ""` |
| [go_for_range_one_literal](./analyzers/go_for_range_one_literal/go_for_range_one_literal.cue) | Flag `for _, v := range []T{x} {...}` — equivalent to a plain assignment |
| [go_errcheck](./analyzers/go_errcheck/go_errcheck.cue) ✏️                     | Flag and rewrite `foo()` to `_ = foo()` when foo returns error (fact passing) |
| [go_deprecated_use](./analyzers/go_deprecated_use/go_deprecated_use.cue)      | Flag calls to functions whose doc comment contains `Deprecated:` (fact passing, works cross-file) |
| [go_taint](./analyzers/go_taint/go_taint.cue)                                  | Track taint from `os.Getenv` through assignments to `exec.Command` (fact passing + fixpoint) |
| [go_api_migration](./analyzers/go_api_migration/go_api_migration.cue) ✏️       | Worked example: ship a `.cue` adapter for breaking API changes -- added trailing arg (`widget.Render(x)` → `widget.Render(x, nil)`) and rename (`widget.OldName` → `widget.NewName`) |

Syntactic ports of [`golang.org/x/tools/go/analysis/passes`](https://pkg.go.dev/golang.org/x/tools/go/analysis/passes). Each rule matches trees, not types; the CUE file documents what the original analyzer does that Pasta cannot. `assign` is `go_self_assignment` earlier in this table. Passes that need types, SSA, sizes, or assembly are omitted, including `composite`, `errorsas`, `nilfunc`, and `unmarshal` (pointer vs value, or function vs another identifier of the same name, is not visible from the tree).

| Path | What it does |
|---|---|
| [go_appends](./analyzers/go_appends/go_appends.cue)                           | Flag `append(s)` with no values |
| [go_atomic](./analyzers/go_atomic/go_atomic.cue)                             | Flag `x = atomic.AddInt32(&x, 1)` (non-atomic store of the add) |
| [go_bools](./analyzers/go_bools/go_bools.cue)                                 | Flag redundant `x \|\| x` / `x && x` and suspect `x != a \|\| x != b` |
| [go_copylock](./analyzers/go_copylock/go_copylock.cue)                       | Flag `sync.Mutex` / `sync.RWMutex` passed by value |
| [go_deepequalerrors](./analyzers/go_deepequalerrors/go_deepequalerrors.cue)   | Flag `reflect.DeepEqual` on `errors.New` / `fmt.Errorf` |
| [go_defers](./analyzers/go_defers/go_defers.cue)                             | Flag `time.Since` evaluated as a deferred call argument |
| [go_hostport](./analyzers/go_hostport/go_hostport.cue)                       | Flag `fmt.Sprintf("%s:%d", host, port)`; use `net.JoinHostPort` |
| [go_httpresponse](./analyzers/go_httpresponse/go_httpresponse.cue)           | Flag `defer resp.Body.Close()` immediately after `http.Get` |
| [go_lostcancel](./analyzers/go_lostcancel/go_lostcancel.cue)                 | Flag discarding the cancel func from `context.WithCancel` |
| [go_printf](./analyzers/go_printf/go_printf.cue)                             | Flag `fmt.Printf`/`Sprintf`/`Errorf` with a verb and no operand |
| [go_shift](./analyzers/go_shift/go_shift.cue)                                 | Flag `x << 64` (and larger) integer-literal shift counts |
| [go_sigchanyzer](./analyzers/go_sigchanyzer/go_sigchanyzer.cue) ✏️             | `signal.Notify(make(chan T))` → buffer the channel with `, 1` |
| [go_slog](./analyzers/go_slog/go_slog.cue)                                   | Flag `slog.Info("msg", "key")` missing a value |
| [go_sortslice](./analyzers/go_sortslice/go_sortslice.cue)                     | Flag `sort.Slice` comparison funcs that do not take two parameters |
| [go_stdmethods](./analyzers/go_stdmethods/go_stdmethods.cue)                 | Flag `String`/`Error`/`ReadByte` methods with the wrong signature |
| [go_stringintconv](./analyzers/go_stringintconv/go_stringintconv.cue) ✏️       | `string(123)` → `string(rune(123))` |
| [go_structtag](./analyzers/go_structtag/go_structtag.cue)                     | Flag malformed struct tags and json/xml tags on unexported fields |
| [go_testinggoroutine](./analyzers/go_testinggoroutine/go_testinggoroutine.cue) | Flag `t.Fatal` from a goroutine started by the test |
| [go_tests](./analyzers/go_tests/go_tests.cue)                                 | Flag `Test`/`Benchmark`/`Fuzz` funcs in `*_test.go` with no testing parameter |
| [go_timeformat](./analyzers/go_timeformat/go_timeformat.cue) ✏️               | `2006-02-01` → `2006-01-02` in time layouts |
| [go_unreachable](./analyzers/go_unreachable/go_unreachable.cue)               | Flag the statement immediately after `return` or `panic` |
| [go_unsafeptr](./analyzers/go_unsafeptr/go_unsafeptr.cue)                     | Flag `unsafe.Pointer(uintptr(...))` |
| [go_unusedresult](./analyzers/go_unusedresult/go_unusedresult.cue) ✏️           | Flag unused `fmt.Sprintf`, `errors.New`, `context.With*`, `slices.*`, `sort.Reverse` |
| [go_waitgroup](./analyzers/go_waitgroup/go_waitgroup.cue)                     | Flag `WaitGroup.Add` as the first statement of a new goroutine |

**Python**

| Path | What it does |
|---|---|
| [python_eq_none](./analyzers/python_eq_none/python_eq_none.cue) ✏️                 | `x == None` → `x is None`, `x != None` → `x is not None` (PEP 8 E711, both orientations) |
| [python_bare_except](./analyzers/python_bare_except/python_bare_except.cue) ✏️     | `except:` → `except Exception:` |
| [python_isinstance_singleton](./analyzers/python_isinstance_singleton/python_isinstance_singleton.cue) ✏️ | `isinstance(x, (T,))` → `isinstance(x, T)` |
| [python_dict_get_redundant_none](./analyzers/python_dict_get_redundant_none/python_dict_get_redundant_none.cue) ✏️ | `d.get(k, None)` → `d.get(k)` |
| [python_assert_tuple](./analyzers/python_assert_tuple/python_assert_tuple.cue) ✏️  | `assert (cond, msg)` → `assert cond, msg` (real footgun -- tuple is always truthy) |
| [python_explicit_object_base](./analyzers/python_explicit_object_base/python_explicit_object_base.cue) ✏️ | `class Foo(object):` → `class Foo:` (Py3 inherits from object implicitly) |
| [python_redundant_else_after_return](./analyzers/python_redundant_else_after_return/python_redundant_else_after_return.cue) | Flag `if c: return x; else: y` — outdent the else (pylint R1705) |
| [python_mutable_default](./analyzers/python_mutable_default/python_mutable_default.cue) | Flag mutable default args (`def f(x=[])`) |
| [python_deprecated_use](./analyzers/python_deprecated_use/python_deprecated_use.cue) | Flag calls to `@deprecated`-decorated functions (fact passing) |
| [python_taint](./analyzers/python_taint/python_taint.cue)                              | Track taint from `input()` through assignments to `eval`/`exec`/`system` (fact passing + fixpoint propagation) |
| [python_method_no_self](./analyzers/python_method_no_self/python_method_no_self.cue)   | Flag class methods missing `self`/`cls` as first parameter (uses `ancestor_is`) |
| [python_eval_use](./analyzers/python_eval_use/python_eval_use.cue)                     | Flag `eval()` (code-injection hazard; Bandit B307) |

**Rust**

| Path | What it does |
|---|---|
| [rust_needless_bool](./analyzers/rust_needless_bool/rust_needless_bool.cue) ✏️ | `if cond { true } else { false }` → `cond`; `if cond { false } else { true }` → `!(cond)` (clippy `needless_bool`) |
| [rust_println_panic](./analyzers/rust_println_panic/rust_println_panic.cue) ✏️ | Drop redundant `println!()` immediately before `panic!()` |
| [rust_println_redundant_format](./analyzers/rust_println_redundant_format/rust_println_redundant_format.cue) ✏️ | `println!("{}", "hello")` → `println!("hello")` |
| [rust_dbg_macro](./analyzers/rust_dbg_macro/rust_dbg_macro.cue)               | Flag committed `dbg!()` invocations (no autofix — empty/multi-arg forms are unsafe) |
| [rust_deprecated_use](./analyzers/rust_deprecated_use/rust_deprecated_use.cue) | Flag calls to `#[deprecated]` functions (fact passing) |
| [rust_taint](./analyzers/rust_taint/rust_taint.cue)                            | Track taint from `env::var()` through let bindings to `Command::new` (fact passing + fixpoint) |
| [rust_almost_complete_range](./analyzers/rust_almost_complete_range/rust_almost_complete_range.cue) ✏️ | `'a'..'z'` → `'a'..='z'` (clippy `almost_complete_range`) |
| [rust_bool_assert_comparison](./analyzers/rust_bool_assert_comparison/rust_bool_assert_comparison.cue) | Flag `assert_eq!(x, true/false)` (clippy `bool_assert_comparison`) |

**JavaScript**

| Path | What it does |
|---|---|
| [js_object_assign_spread](./analyzers/js_object_assign_spread/js_object_assign_spread.cue) ✏️ | `Object.assign({}, x)` → `{...x}` |
| [js_array_concat_spread](./analyzers/js_array_concat_spread/js_array_concat_spread.cue)     | Flag `[].concat(x)` (prefer `[...x]` when iterable; no autofix — not always equivalent) |
| [js_template_no_subst](./analyzers/js_template_no_subst/js_template_no_subst.cue) ✏️         | `` `abc` `` → `'abc'` when no interpolation |
| [js_double_equals](./analyzers/js_double_equals/js_double_equals.cue) ✏️                     | `==` / `!=` → `===` / `!==` (skips `null` / `undefined` idioms) |
| [js_var_to_let](./analyzers/js_var_to_let/js_var_to_let.cue)                                 | Flag `var` (prefer `let`); report-only — naive rewrite breaks redeclarations / hoisting |
| [js_empty_promise](./analyzers/js_empty_promise/js_empty_promise.cue)                        | Flag `new Promise(() => {})` with empty executor |
| [js_taint](./analyzers/js_taint/js_taint.cue)                                                | Track taint from `req.query` / `req.body` / `req.params` to `eval` / `Function` (fact passing + fixpoint) |
| [js_debugger](./analyzers/js_debugger/js_debugger.cue)                                       | Flag `debugger;` statements |
| [js_useless_catch](./analyzers/js_useless_catch/js_useless_catch.cue)                         | Flag `catch (e) { throw e; }` — a no-op rethrow |

Structural ports of [ESLint built-in rules](https://eslint.org/docs/latest/rules/). Each available rule pasta can express as a tree-sitter pattern is its own analyzer named `js_<rule>` (hyphens become underscores).

A few ESLint ids already have a dedicated analyzer and keep that name: `js_debugger` (`no-debugger`), `js_double_equals` (`eqeqeq`), `js_var_to_let` (`no-var`), `js_useless_catch` (`no-useless-catch`), `js_object_assign_spread` (`prefer-object-spread`).

Omitted: rules that need a scope chain, CFG, or ESLint option object (`no-undef`, `no-unused-vars`, `prefer-const`, `no-const-assign`, `no-func-assign`, `no-class-assign`, `no-import-assign`, `no-param-reassign`, `complexity`, …). Pasta's by-name fact index is file-blind and scope-blind, so assignment-to-binding checks treat a `const x` in one file as the same `x` assigned in another. Also omitted: `no-await-in-loop` (sequential `await` in a loop is ordinary control flow); `no-constant-binary-expression` (a structural "both operands are literals" stand-in flags `1 / 120` and test arithmetic instead of ESLint's constant-folding bugs); `no-console` (`console.log` is ordinary stdout in Node CLIs, and pasta cannot tell those from leftover browser debug); config-only rules whose default reports nothing (`no-restricted-*`, `id-denylist`); deprecated/removed core rules; and layout rules that moved to `@stylistic/eslint-plugin`.

**TypeScript**

| Path | What it does |
|---|---|
| [ts_array_type_style](./analyzers/ts_array_type_style/ts_array_type_style.cue) ✏️ | `Array<T>` → `T[]` for simple `T` (skips unions / keyof) |
| [ts_any_type](./analyzers/ts_any_type/ts_any_type.cue)                            | Flag `: any` annotations (defeat TypeScript's type checking) |
| [ts_inferrable_types](./analyzers/ts_inferrable_types/ts_inferrable_types.cue) ✏️ | Drop `: string` / `: number` / `: boolean` when the initializer is a matching literal |

**YAML**

| Path | What it does |
|---|---|
| [yaml_truthy](./analyzers/yaml_truthy/yaml_truthy.cue) ✏️             | `Yes`/`On`/`True`/etc. → `true`; `No`/`Off`/`False`/etc. → `false` |
| [yaml_empty_value](./analyzers/yaml_empty_value/yaml_empty_value.cue) | Flag keys with no value (parses as null) |
| [gha_security](./analyzers/gha_security/gha_security.cue)             | GitHub Actions / Dependabot security checks inspired by [zizmor](https://docs.zizmor.sh/audits/) (unpinned uses, dangerous triggers, template injection, artipacked, …) |

**TOML**

| Path | What it does |
|---|---|
| [wrangler_observability](./analyzers/wrangler_observability/wrangler_observability.cue) | Require `[observability]` / `[observability.logs]` / `[observability.traces]` enabled (with `invocation_logs = true`) in every `wrangler.toml` |
| [toml_duplicate_key](./analyzers/toml_duplicate_key/toml_duplicate_key.cue) | Flag consecutive duplicate keys in a table |

**Bash**

| Path | What it does |
|---|---|
| [bash_eval_use](./analyzers/bash_eval_use/bash_eval_use.cue) | Flag `eval` invocations (code-injection hazard) |
| [bash_unquoted_expansion](./analyzers/bash_unquoted_expansion/bash_unquoted_expansion.cue) | Flag unquoted `$VAR` in `[ -z $VAR ]` tests (ShellCheck SC2086) |
| [bash_grep_glob](./analyzers/bash_grep_glob/bash_grep_glob.cue) | Flag `grep '*foo*'` patterns that look like globs (ShellCheck SC2063) |

**C**

| Path | What it does |
|---|---|
| [c_gets_unsafe](./analyzers/c_gets_unsafe/c_gets_unsafe.cue) | Flag `gets()` (CWE-242, removed in C11) — use `fgets()` |
| [c_unchecked_stdlib](./analyzers/c_unchecked_stdlib/c_unchecked_stdlib.cue) | Flag `system` / `strcpy` / `strcat` / `sprintf` / `ato*` (C and C++) |
| [c_empty_if](./analyzers/c_empty_if/c_empty_if.cue) | Flag `if (cond);` empty then-clauses (C and C++) |

**C++**

| Path | What it does |
|---|---|
| [cpp_using_namespace_std](./analyzers/cpp_using_namespace_std/cpp_using_namespace_std.cue) | Flag `using namespace std;` (pollutes the global namespace) |

**Java**

| Path | What it does |
|---|---|
| [java_string_equals_literal](./analyzers/java_string_equals_literal/java_string_equals_literal.cue) ✏️ | `x.equals("foo")` → `"foo".equals(x)` (NPE-safe; identifier receivers only) |
| [java_finalizer](./analyzers/java_finalizer/java_finalizer.cue) | Flag no-arg `void finalize()` overrides (deprecated since Java 9) |
| [java_finalize_overload](./analyzers/java_finalize_overload/java_finalize_overload.cue) | Flag `void finalize(…)` overloads that are not `Object.finalize` |
| [java_print_stack_trace](./analyzers/java_print_stack_trace/java_print_stack_trace.cue) | Flag `e.printStackTrace()` — prefer a logger |
| [java_system_out_println](./analyzers/java_system_out_println/java_system_out_println.cue) | Flag `System.out` / `System.err` print calls — prefer a logger |

**Swift**

| Path | What it does |
|---|---|
| [swift_force_unwrap](./analyzers/swift_force_unwrap/swift_force_unwrap.cue) | Flag `x!` force-unwrap operator (crashes on nil) |

**Ruby**

| Path | What it does |
|---|---|
| [ruby_unless_else](./analyzers/ruby_unless_else/ruby_unless_else.cue) | Flag `unless ... else ... end` — invert to `if` and swap branches |
| [ruby_double_negation](./analyzers/ruby_double_negation/ruby_double_negation.cue) | Flag `!!x` boolean conversion (RuboCop `Style/DoubleNegation`) |

**PHP**

| Path | What it does |
|---|---|
| [php_loose_equality](./analyzers/php_loose_equality/php_loose_equality.cue) ✏️ | `==` / `!=` → `===` / `!==` (skips `null` idioms) |
| [php_debug_output](./analyzers/php_debug_output/php_debug_output.cue) | Flag `var_dump` / `print_r` / `debug_zval_dump` |

**SQL**

| Path | What it does |
|---|---|
| [sql_select_star](./analyzers/sql_select_star/sql_select_star.cue) | Flag `SELECT *` (fragile under schema changes) |
| [sql_comma_join](./analyzers/sql_comma_join/sql_comma_join.cue) | Flag `FROM a, b` comma joins — prefer an explicit `JOIN` |

**Dockerfile**

| Path | What it does |
|---|---|
| [dockerfile_latest_tag](./analyzers/dockerfile_latest_tag/dockerfile_latest_tag.cue) | Flag `FROM image:latest` and implicit-latest `FROM image` |
| [dockerfile_apt_no_recommends](./analyzers/dockerfile_apt_no_recommends/dockerfile_apt_no_recommends.cue) | Flag `apt-get install` without `--no-install-recommends` |

**Terraform**

| Path | What it does |
|---|---|
| [terraform_security](./analyzers/terraform_security/terraform_security.cue) | Terraform and OpenTofu security checks inspired by [Checkov](https://github.com/bridgecrewio/checkov): unpinned modules, public RDS, S3, and security groups, missing encryption, IMDSv2, and IAM `*:*` |

**HTML**

| Path | What it does |
|---|---|
| [html_deprecated_tags](./analyzers/html_deprecated_tags/html_deprecated_tags.cue) | Flag `<center>`, `<font>`, `<marquee>`, `<blink>`, `<strike>`, `<big>`, `<tt>` (case-insensitive) |
| [html_img_alt](./analyzers/html_img_alt/html_img_alt.cue) | Flag `<img>` tags missing an `alt` attribute |
| [html_lang](./analyzers/html_lang/html_lang.cue) | Flag `<html>` tags missing a `lang` attribute |

**CSS**

| Path | What it does |
|---|---|
| [css_zero_unit](./analyzers/css_zero_unit/css_zero_unit.cue) ✏️ | Drop unit on length zero (`0px` → `0`; leaves `0%` alone) |
| [css_important](./analyzers/css_important/css_important.cue) | Flag `!important` declarations |
| [css_empty_block](./analyzers/css_empty_block/css_empty_block.cue) | Flag empty `{}` rule bodies |
| [css_duplicate_property](./analyzers/css_duplicate_property/css_duplicate_property.cue) | Flag consecutive duplicate properties in a block |

## Performance

Cold runs over large trees are tuned for sparse style rules:

1. **Content-sniff pre-filter** — before parsing, pasta checks cheap
   substrings inferred from each rule (`eq` / `token_eq` / a single
   simple `matches` alternation) plus optional `require_substring` on
   the rule. Rewrite `within` tokens are not inferred (diagnose can
   fire without them). Files that cannot match any applicable rule
   skip the parse.
2. **Per-file parse budget** — default 2s (`-parse-timeout`, or
   `parse_timeout_ms` in `pasta.cue`). Timed-out files are reported as
   `skipped (too complex to analyze)` instead of owning the run.
3. **ERROR-heavy vs degraded** — densely broken trees skip as
   `skipped (parse errors)`. Light `HasError` glitches (e.g. a trailing
   brace) still analyze (`parse_degraded` in `-stats`) and are not
   cached. Pass `-stats` for
   `walked` / `prefilter_skipped` / `parsed` / `parse_errors` /
   `parse_degraded` / `timed_out` / `memory_skipped` / `cache_hits`.
4. **Memory budget** — optional cumulative parsed-source byte cap
   (`-memory-budget`, or `memory_budget` in `pasta.cue`) across the
   whole CLI run (including multipass `-fix`). Admission is in source
   order so the skip set is deterministic. When exceeded, further files
   skip like a timeout; with `-fail-on` set, skips fail the process.
5. **Streamed reads** — the CLI passes paths into a worker pool; each
   worker reads its file on demand. Peak RSS stays O(workers × file)
   instead of O(all sources).
6. **Arena pool drain** — parser host pools are drained every ~100
   files so the Go GC can reclaim them on big cold runs.

## Autofix guardrails

- **Innermost nested edits** — when one rewrite fully contains another
  (e.g. layered `Array<…>` forms), pasta keeps the innermost edit.
  Pair with `-fix -fix-until-clean` (or `-fix-passes N`) to peel
  outer layers across passes — a single pass alone drops the outer edit.
- **Per-file continue** — a partial overlapping-edit conflict skips
  that file's write, sets exit status 1, and continues the rest of the
  tree (no empty-looking `-fix` run).
- **Spread interpolation** — `{...@cap}` / `[...@cap]` strips a leading
  `...` from the capture when it is already a spread, so
  `Object.assign({}, ...xs)` cannot become `{......xs}`.
- **Scope-sensitive rules** — `js_var_to_let` is diagnose-only; a
  structural `var`→`let` rewrite is unsafe without scope analysis.

E2E smoke tests under [`e2e/`](./e2e/) shallow-clone real repos across
Go, JavaScript, TypeScript, Python, Rust, YAML, Java, CSS, PHP, and HTML,
scan them with a multi-language style-rule set, and exercise autofix
on the more complex trees.

## Use

```
go install github.com/imjasonh/playground/pasta/cmd/pasta@latest

# Project-style: drop your rules in ./.pasta/ and just run pasta.
# Rules are loaded from ./.pasta/, sources default to ./...
mkdir -p .pasta && cp path/to/some-rule.cue .pasta/
pasta              # report (exit 0 even when findings are printed)
pasta -fail-on=error   # CI-friendly: exit 1 on error-severity findings
pasta -fail-on=warning # exit 1 on warning or error
pasta -fix         # apply fixes (atomic rewrite; skips symlinks)
pasta -fix -fix-until-clean   # multipass until no file changes (nested rewrites)
pasta -stats                     # also print walk / prefilter / parse / skip counters
# Every run ends with: scanned N files, R rules, X.Y MB/s

# Same, but pointing at a different rule directory.
pasta -rules path/to/rule-dir
pasta -rules path/to/rule-dir ./...
pasta -fix -rules path/to/rule-dir file.go

# Single-rule shortcut: first positional arg is a .cue file.
pasta path/to/rule.cue file.go [file.go ...]
pasta path/to/rule.cue ./...
pasta -fix path/to/rule.cue ./...

# `./...` recurses from the current dir; `pkg/...` is `pkg/` and below.
# Files whose extension doesn't map to a registered language are skipped.
# Vendored dependency trees are skipped by default (`vendor/`,
# `node_modules/`, Python venvs, CocoaPods, …) — pasta only looks at
# first-party source. Use `-skip` to add more (e.g. `dist,build`).
pasta -skip dist,build ./...

# Run rules in a directory against its testdata/. Defaults to ./.pasta/.
pasta test
pasta test path/to/rule-dir

# Fetch any remote rule modules declared in <rule-dir>/pasta.cue and
# write a pasta.lock with resolved commit SHAs (network access).
# Defaults to ./.pasta/.
pasta sync
pasta sync path/to/rule-dir
```

When more than one source file is supplied (directly or via `./...`
expansion) `pasta` analyzes them as a **single group**: a fact store is
shared across the files, so cross-file analyzers like
[`go_deprecated_use`](./analyzers/go_deprecated_use/go_deprecated_use.cue)
can answer "is this name called anywhere in this codebase?" in one
invocation. A single source path runs as a one-file group (fresh fact
store), matching the historical behavior. The
[`testdata/go_unused_export`](./testdata/go_unused_export/go_unused_export.cue)
demo walks the same grouping without shipping as a production lint
(selector calls and whole-repo `./...` groups produce too many
false positives).

A rule directory has shape:

```
my-rule/
  my-rule.cue
  testdata/
    foo.go                  # top-level files: each is its own
    foo.go.golden           # one-file group (fresh fact store)
    bar.py
    bar.py.golden
    cross_pkg/              # subdirectory: ONE multi-file group with
      api.go                # a shared fact store across its files
      caller.go             # (recursive)
      caller.go.golden
```

`pasta test` discovers `*.cue` rules in the directory, walks `testdata/`
for source files in any registered language, runs the rules, and verifies:

1. Every diagnostic emitted by a rule matches a `// want "substring"`
   marker on the same line of the source (literal substring match, not
   a regex). `// want:+N "substring"` shifts the expected line by N
   (useful when the rewrite itself deletes the marker line).
2. Every `// want` marker is satisfied by exactly one diagnostic.
3. If a `<file>.golden` exists, the `-fix` output matches it byte-for-byte.

Files directly under `testdata/` are run as independent single-file
groups. Each subdirectory of `testdata/` is run as one multi-file
group sharing a fact store — use subdirs to test cross-file analyzers
with realistic multi-file inputs.

## Remote rule imports

Rule directories can pull in rule modules published in other
repositories. Declare them in a `pasta.cue` manifest at the rule
directory root (typically `./.pasta/pasta.cue`):

```cue
// .pasta/pasta.cue
imports: {
    "github.com/alice/lint-rules": "v1.2.3"
}
```

The next `pasta` run resolves the version, fetches the module,
and writes `./.pasta/pasta.lock` pinning the commit SHA — sync is
implicit. Subsequent runs are offline as long as the lockfile is
in sync with the manifest. `pasta sync` still exists if you want
to refresh a moving ref (branch / tag) eagerly, and
`pasta sync --check` reports drift without writing files for CI
gating.

To upgrade pinned versions, run `pasta bump`:

```
$ pasta bump
bump github.com/alice/lint-rules v1.2.3 -> v1.4.0
ok   github.com/bob/security-rules already at v0.9.1
skip github.com/carol/experimental (no semver tags)
```

`pasta bump` walks each module's tag list, picks the highest
stable semver tag, rewrites `pasta.cue` in place (preserving
comments and formatting), and re-syncs the lockfile. Pass module
paths to narrow the bump (`pasta bump github.com/alice/lint-rules`).
Modules pinned to a branch, a non-semver tag, or a full SHA are
left alone — those have explicit "use the tip" or "stay pinned"
semantics that bump shouldn't second-guess. Prerelease tags
(`v2.0.0-rc1`) are deliberately ignored too.

**Every top-level analyzer the module exports is auto-enrolled**, so
listing the module is enough to start running its rules — no
per-rule stub in `.pasta/` needed. A `.pasta/` containing only a
manifest is valid; its rules come entirely from the imports.

```
my-project/
  .pasta/
    pasta.cue       # imports: { "github.com/alice/lint-rules": "v1.2.3" }
    pasta.lock      # written by `pasta sync`
  src/...
```

`pasta` (or `pasta -fix`) from the project root then runs alice's
rules over `./...`.

If you want to override a rule from a remote module, drop a local
analyzer with the same name into `.pasta/` — the local version
wins, and pasta prints a warning to stderr so the suppression is
visible. Two remote modules exporting an analyzer with the same
name is an error (resolve by renaming, dropping one of the
imports, or shadowing both with a local rule).

Rule files in remote modules can also be `import`ed by name from
your local `.cue` files when you want to compose rather than just
auto-enroll:

```cue
import "github.com/alice/lint-rules/python_taint"
```

Modules are cached under `$XDG_CACHE_HOME/pasta/modules/` and keyed
by commit, so re-tagging upstream after a sync can't silently change
what your rules see — `pasta` re-uses the locked SHA until you run
`pasta sync` again. The cache is hash-verified on every load: if the
cached files no longer match the lockfile's recorded digest, pasta
refuses to load and tells you which dir to remove.

Publishing a rule module is just `git push` plus `git tag`: any
public repo whose `https://<path>.git` URL `git ls-remote` can
resolve will work. Versions are git refs (tags, branches, or full
SHAs) — there's no semver resolution, and a remote module is not
allowed to declare its own remote imports (flat deps only in v1).

## Use case: shipping adapters for breaking changes

Library authors can use `pasta` rules as **codemods that travel with a
release**. When a breaking API change lands, ship a `.cue` file
alongside the version bump and downstream consumers can run
`pasta -fix upgrade_v1.2.3.cue ./...` to migrate their call sites mechanically.

The `.cue` file expresses the rewrite once, in a tree-aware way, and
runs against any caller's source -- no separate per-codebase script,
and no need for the library author to publish (or each consumer to
write) a one-off migrator.

[`analyzers/go_api_migration`](./analyzers/go_api_migration/go_api_migration.cue)
is a working example covering two of the most common shapes:

- **Added trailing argument.** v1.2.3 of a fictional `widget` library
  added a trailing `opts *Options` parameter to `widget.Render`. The
  rule matches *only* the pre-migration single-arg call shape (using
  `named_child_count`), rewrites `widget.Render(x)` to
  `widget.Render(x, nil)`, and is a no-op once a codebase has been
  migrated, so re-running it is safe.

- **Rename.** v1.3.0 renamed `widget.OldName` to `widget.NewName`.
  The rule matches the selector expression itself (not the call), so
  it rewrites both `widget.OldName` value references and
  `widget.OldName(...)` calls in one pass.

Each rule emits a diagnostic *and* a rewrite. Without `-fix`, `pasta`
reports unmigrated call sites; use `-fail-on=error` (or `warning`) in
CI so findings fail the build. With `-fix` it edits them in place.
The same pattern extends naturally to:

- Removed arguments (`delete_from`/`delete_to` between captures).
- Argument reorder (capture each arg, reassemble in the new order).
- Removed APIs that need a hand-written replacement (emit a
  diagnostic only -- leave the rewrite off so a human handles it).

The full test, with positive and negative cases (different package,
different method, already-migrated arity), lives in
[`analyzers/go_api_migration/testdata/a.go`](./analyzers/go_api_migration/testdata/a.go)
and its `.golden` counterpart.

## LSP

The repo also has an [LSP](https://en.wikipedia.org/wiki/Language_Server_Protocol) server, `pastals`. The [`.editors/`](./editors/) directory has instructions about setting this up for your IDE; I've only tested it with Zed.

If you specify rules in your repo at `pasta.cue` or `.pasta/**/*.cue`, these rules will be loaded and evaluated.

-----

Working in this repo? See [AGENTS.md](./AGENTS.md) for layout, how
to add a new analyzer or language, and conventions worth knowing.

See [cue.md](./cue.md) for the case for CUE as the rule schema, and
[future-work.md](./future-work.md) for what's deliberately not yet done.
