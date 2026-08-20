# `pasta`: a polyglot linter/fixer for monorepos

I believe that monorepos are the future. For the record, I believed that _before_ LLMs could write tens of thousands of lines of code before I finished checking Slack. It's only more true now.

![a delightful meme about monorepos](./monorepo.jpg)

All the benefits of monorepos for humans -- consistent checks and policy, consistently available context, consistent access control -- are only more important when you can hire a relatively cheap army of over-eager junior supergeniuses.

One consistent problem I've experienced in a monorepo is ensuring consistent quality checks across the codebase. Is every* line of Go [`gofmt`](https://go.dev/blog/gofmt)ed and [`go vet`](https://pkg.go.dev/cmd/vet)ted and [`golangci-lint run`](https://golangci-lint.run/)ned? In a polyglot monorepo -- a monorepo which may include backend code, frontend code, infra-as-code, CI-as-code, docs, and the whole kitchen sink -- this gets even worse. You may start running [`rustfmt`](https://rust-lang.github.io/rustfmt/) and [`clippy`](https://doc.rust-lang.org/clippy/) and [`eslint`](https://eslint.org/), then before you know it you're running [`checkov`](https://www.checkov.io/) and [`zizmor`](https://docs.zizmor.sh/) and [`yamlfmt`](https://github.com/google/yamlfmt) and who knows what else.

Each of these tools is great! Most of them are either highly configurable, or simple and strict enough there's nothing to configure (`gofmt` you absolute legend 🤎). But a growing roster of tools each with their own bespoke configuration and idiosyncratic quirks made me wonder if there might be a better way to handle this more consistently across languages.

### 🌲 ASTs

Each of these tools is fundamentally doing [static program analysis](https://en.wikipedia.org/wiki/Static_program_analysis), where the source code characters are being parsed into an [abstract syntax tree](https://en.wikipedia.org/wiki/Abstract_syntax_tree) (AST) consisting to nodes with children. So the source code `if err != nil {` isn't seen as `[]byte{'i', 'f', ' ', 'e', 'r', 'r', ...}`, but rather as a node representing `if`, with a boolean statement `err != nil`, where that statement node has three children: the variable `err`, the operation `!=`, and the value `nil`. With that representation, the tool can perform checks on the tree, for example to ensure that it's not comparing the variable `err` with a poorly-named variable `nill`.

I took a lot of inspiration from [Go's `analysis` framework](https://pkg.go.dev/golang.org/x/tools/go/analysis), which powers `go vet`, and offers a Go API to define rules to enforce on Go AST nodes, and even lets you define transformations on that AST that should be applied when the rule isn't satisfied. I started by having an agent write [an Analyzer for a particular Go style preference of mine](https://github.com/imjasonh/iferr-analyzer), and sure enough, you can run it to find and automatically fix non-compliant code. I had an agent write a [couple](https://github.com/imjasonh/ctxhttp-analyzer) [more](https://github.com/imjasonh/pkgerrors-analyzer). It was fun, and easy, and if you write Go regularly I highly recommend playing around with it.

### 🗯️ Polyglot Analyzers

The problem with a monorepo, however, is that you may have other languages you want to analyze and autofix. One could (and I did) imagine a Rust Analyzer framework, a JavaScript Analyzer framework, a TypeScript Analyzer, a YAML Analyzer, CSS Analyzer, and so on, and sure, you could probably put an agent on that and get some okay results pretty quickly. But you'd still end up with a sprawl of static analyzer passes in each of those languages, potentially inconsistently applied across your codebase.

You could (and I did) also imagine a Go-based analyzer framework that worked on _any_ language, and you could probably get an agent to build that too. For AST handling across many languages you'd probably want to use [Tree-sitter](https://tree-sitter.github.io/tree-sitter/), which powers syntax highlighting and [LSP servers](https://langserver.org/) in basically any place you see them. But writing Go to lint TypeScript feels sort of _...wrong._

I wanted some neutral ~language for describing AST nodes and the rules that govern them. For that I reached for [CUE](https://cuelang.org/), which I've used elsewhere with moderate success. CUE is like YAML in that it declaratively describes data structures, but unlike YAML in that it's typed, and has much more sane rules and syntax for referencing other variables. And it's typed.

> [!IMPORTANT]
> Right about now you might be saying, "you didn't want to make TypeScript developers learn Go, but you'll make them learn CUE instead?" to which I'll say, _shut up_, this is my project and I'll do what I want! Have your own agents write your own thing if you want. I stand by CUE, and thanks to the next paragraph _you haven't even read yet_ it doesn't really matter anyway.

CUE is a bit verbose, and for some complicated rules can be pretty opaque and dense to read. Luckily, the Go Analysis framework has more life lessons to learn from, in its documented [testing philosophy](https://pkg.go.dev/golang.org/x/tools/go/analysis#hdr-Testing_an_Analyzer). To test a Go analyzer you can pass it to a checker along with a `testdata` directory containing files to check. That testdata file includes examples of code that passes and fails the check, with a comment noting where the analyzer should find an issue (example [here]([url](https://cs.opensource.google/go/x/tools/+/refs/tags/v0.49.0:go/analysis/passes/httpmux/testdata/src/a/a.go))). I took this a step further in my tool, and had my tool also check for `testdata/*.golden` files that specify the file contents after being fixed by the rule's autofix transform, if specified.

This means that I don't even have to read any of the CUE that the agent writes, I only need to eyeball the testdata files showing good and bad examples, and the fixes it produces. Not bad!

I call the tool 🍝`pasta` by the way. Like AST? And because code is spaghetti? Anyway I was entertained by it.

With this in place, it was just a matter of having an agent write a bunch of rules, and generating before/after testdata examples. `pasta` looks for rules in a `.pasta/` directory. Like any good linter tool, it also supports `//nolint` directives in comments, to ignore known rules violations.

My agent and I have managed to implement a subset of both [Zizmor](https://github.com/imjasonh/playground/pull/229) and [Checkov](https://github.com/imjasonh/playground/pull/238) rules with relatively little config.

### 🌴 Tree-Sitter and Go Crimes

`pasta` worked well for my monorepo, but my monorepo isn't exactly a challenge, so eventually I ran it against a large slice of a codebase at work, with a few relatively simple rules, just to see how it went.

It went ...slowly.

Out of a strong preference for pure-Go solutions ([cgo](https://go.dev/wiki/cgo) tends to complicate things unless it's truly necessary), I'd opted for [`gotreesitter`](https://github.com/odvcencio/gotreesitter), a pure-Go implementation of tree-sitter. Unfortunately this made parsing code into ASTs significantly slower than just using the standard C tree-sitter code via cgo. Cgo was truly necessary. 😭

...Or was it! I'd heard of other folks avoiding cgo by compiling C to [Wasm](https://webassembly.org/) then executing it directly in Go, and that seemed just crazy enough to work for me too. After a bit of prompting, I got tree-sitter wasmed and `go:embed`ded into `pasta`, where it executes using [`wazero`](https://wazero.io/). It's an abomination, but it made `pasta` _14x faster_. This wasn't as fast as tree-sitter via cgo, but it was fast enough for me, and it made `pasta lint`ing tens of thousands of files reasonably fast. It now parses and lints at ~1MB/s, and the whole journey only made the binary ~1.4 MB bigger. Not bad!

For reference, the PR where we made the change: https://github.com/imjasonh/playground/pull/210

### Conclusion

I'm pretty happy with this turned out. It's not perfect, nothing is, but it's pretty fast, easy to review and debug via examples, and LLM agents are pretty great at one-shotting new rules based on my vague directions. If nothing else, it was fun to build, and to write about here.

If you've got a monorepo handy and this sounds like it might be useful, give it a shot. If you're an AST nerd who just wants to play, give it a shot!
