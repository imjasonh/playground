---
name: google-style
description: Follow the Google style guides for code in this repo. Use when writing or editing Go, Rust, JavaScript, TypeScript, or any other language that has a Google style guide.
---

# Google style guides

Write code in this repository to the [Google style guides](https://google.github.io/styleguide/).

Comments, READMEs, UI copy, and PR prose follow the developer documentation style guide, not these code guides. Use [google-developer-style](../google-developer-style/SKILL.md) for that prose.

## Which guide

| Language | Guide | Skill |
| --- | --- | --- |
| Go | [guide](https://google.github.io/styleguide/go/guide), [decisions](https://google.github.io/styleguide/go/decisions), [best practices](https://google.github.io/styleguide/go/best-practices) | [google-go-style](../google-go-style/SKILL.md) |
| Rust | [Rust style guide](https://google.github.io/styleguide/rustguide.html) | [google-rust-style](../google-rust-style/SKILL.md) |
| JavaScript | [JavaScript style guide](https://google.github.io/styleguide/jsguide.html) | [google-js-style](../google-js-style/SKILL.md) |
| TypeScript | [TypeScript style guide](https://google.github.io/styleguide/tsguide.html) | [google-js-style](../google-js-style/SKILL.md) |
| Shell | [Shell style guide](https://google.github.io/styleguide/shellguide.html) | |
| Python | [Python style guide](https://google.github.io/styleguide/pyguide.html) | |
| HTML and CSS | [HTML/CSS style guide](https://google.github.io/styleguide/htmlcssguide.html) | |
| Swift | [Swift style guide](https://google.github.io/swift/) | |
| Markdown | [Markdown style guide](https://google.github.io/styleguide/docguide/style.html) | |

For a language in the index that is not in this table, follow that language's guide. `AGENTS.md` and an app's own README still win when they set a stricter project rule.

## What pasta checks

Pasta rules under `pasta/analyzers/` flag violations that the syntax can decide. They run as warnings, and `pasta -fail-on=warning` fails CI. A judgment call (naming that depends on meaning, quote style across an existing file, 80-column wrapping) stays in the language skill and is not a rule.

When the guide allows an exception, or you are keeping a line you are not rewriting, mark that line:

```
// pasta:ignore rule_name (why this line stays)
```

The reason must start with a character that is not a rule-name character, such as `(`. Words after the rule name are read as more rule names until that character. An ignore that names a rule which did not fire on that line fails the build.

Do not reformat a file only to match a guide. Apply the guide to the lines you are already changing, and to new code.
