---
name: google-js-style
description: Follow the Google JavaScript and TypeScript style guides when writing or editing JS or TS. Use for .js, .mjs, .cjs, .jsx, .ts, and .tsx files in this repo.
paths: ["**/*.js", "**/*.mjs", "**/*.cjs", "**/*.jsx", "**/*.ts", "**/*.tsx"]
---

# Google JavaScript and TypeScript style

Follow the [JavaScript style guide](https://google.github.io/styleguide/jsguide.html) for JavaScript, and the [TypeScript style guide](https://google.github.io/styleguide/tsguide.html) for TypeScript. Where the TypeScript guide is silent, the JavaScript guide applies.

[Section 8.4](https://google.github.io/styleguide/jsguide.html#policies-reformatting-existing-code) of the JavaScript guide says new code follows the guide, and existing code is not reformatted only to match. Apply the formatting rules to the lines you are editing. Do not convert a file's quotes, semicolons, or line wrapping in a drive-by edit.

Closure library rules (`goog.module`, `goog.require`) do not apply. This repo uses ES modules.

## Checks

These pasta rules fail the build. Each name is the `pasta:ignore` token.

| Rule | What it flags |
| --- | --- |
| `js_double_equals` | `==` and `!=`, rewritten to `===` and `!==`. `== null` and `!= null` stay, because that is the guide's nullish check. |
| `js_var_to_let` | `var`, rewritten to `let`. |
| `js_no_default_export` | `export default`. Use a named export. Tool configs (`*.config.js` and the other `*.config.*` patterns in `.pasta/pasta.cue`) are exempt, because those tools require a default export. |
| `js_new_parens` | `new Foo` without `()`. Write `new Foo()`. |

`js_no_eq_null` is disabled. It bans `== null`, which the JavaScript and TypeScript guides allow. Do not turn it back on.

`js_one_var` is a hint. The guide wants one declaration per statement. A hint does not fail the build. Follow it in new code.

## Formatting to follow in new and edited code

The formatter is not checked, because applying it to existing files would rewrite them.

- Single quotes for strings, unless the string itself contains a quote.
- End statements with semicolons.
- Braces for every control-structure body.
- Indent two spaces.
- Keep lines to 80 columns when you can do it without harming readability.
- Trailing commas in multiline literals and parameter lists.
- `const` for a binding you do not reassign, `let` otherwise.
- Name files `lower_snake_case` or the name the neighboring files in that app already use. Match the app.

## TypeScript

- Do not use `enum`. Use a union of string literals, or a const object, as the TypeScript guide describes.
- Do not prefix an interface name with `I`.
- A type that is only `null` or only `undefined` is not a useful type. Use the other one consistently at a boundary.
