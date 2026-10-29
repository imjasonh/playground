---
name: google-go-style
description: Follow the Google Go style guide when writing or editing Go. Use for any .go file in this repo.
paths: ["**/*.go"]
---

# Google Go style

Follow the Google Go style documents when you write or edit Go:

- [Style guide](https://google.github.io/styleguide/go/guide) (principles)
- [Decisions](https://google.github.io/styleguide/go/decisions) (normative)
- [Best practices](https://google.github.io/styleguide/go/best-practices)

`gofmt` is the formatter. The guide does not set a line limit. Project rules in `AGENTS.md` are stricter where they overlap: `log/slog` and `clog` instead of `fmt.Print`, and `go-envconfig` for environment variables.

Apply the guide to new code and to lines you are already editing. Do not restyle a file only to match it.

## Checks

These pasta rules fail the build. Each name is the `pasta:ignore` token.

| Rule | What it flags |
| --- | --- |
| `go_dot_import` | `import .` |
| `go_import_alias` | An alias that contains `_` or a capital letter. A lowercase alias used to avoid a collision is fine. |
| `go_package_name` | A package name that contains `_` or a capital letter, except a name ending in `_test`. |
| `go_receiver_name` | A receiver named `this`, `self`, or `_`. Use a short abbreviation of the type, or omit an unused receiver. |
| `go_error_punctuation` | `errors.New` or `fmt.Errorf` text that ends in `.`, `!`, or `?`. A trailing `...` is allowed. |
| `go_context_param` | A `context.Context` parameter that is not first. A second context after a leading context is fine. A context inside a nested function type belongs to that function. |
| `go_context_field` | A struct field of type `context.Context` or `*context.Context`. Pass the context as a parameter. |
| `use_t_context` | `context.Background` or `context.TODO` in a `*_test.go` file. Use `t.Context()`, `b.Context()`, or `f.Context()`. |
| `use_percent_q` | A `fmt` format string that puts quotes around `%s` (`\"%s\"`, or `"%s"` in a raw string). Use `%q`. |

The decisions guide allows `context.Background` in `main`, `init`, and tests. This repo allows it in `main` and `init`. A test uses `t.Context()`. A helper outside a test file that runs one test starts from `t.Context()`.

HTTP handlers, streaming RPC methods, and `Test` functions take their context from the request, the stream, or `t.Context()`. They do not add a context parameter, so `go_context_param` does not see them. A test helper that takes a context takes it first. When a signature you cannot change takes context later, mark that line:

```go
func (s *svc) Method(name string, ctx context.Context) error { // pasta:ignore go_context_param (signature is fixed by the upstream interface)
```

Error strings start with a lowercase letter unless the first word is an exported name, a proper noun, or an acronym. Capitalization is not checked, because those exceptions are not visible in the string alone.

## Also follow, not checked

- MixedCaps names. Initialisms keep a consistent case (`URL`, `url`, not `Url`).
- Package names are short, lowercase, and one word. Avoid `util`, `common`, and `helper`.
- Import groups are the groups `gofmt` and `goimports` already produce.
- A function that returns an error returns it as the last result. Handle the error or return it. Indent the error path.
- Prefer `any` over `interface{}` in new code.
- Do not call `panic` for ordinary failures. A `Must` function is the documented exception.
- Name a getter for the noun it returns. Do not prefix it with `Get`.
