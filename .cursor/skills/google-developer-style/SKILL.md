---
name: google-developer-style
description: Apply the Google developer documentation style guide when writing or editing comments, documentation, READMEs, AGENTS.md, API docs, HTML help text, user-facing strings, and PR descriptions. Use whenever you draft or revise prose in this repo.
---

# Google developer documentation style

Apply the [Google developer documentation style guide](https://developers.google.com/style) when you write comments or documentation in this repository.

This skill is a working subset for comments, READMEs, `AGENTS.md`, other Markdown, HTML copy, API doc comments, and PR prose. When this file and project docs don't cover a question, follow the official guide. When the guide also doesn't cover it, use project-specific style first, then Merriam-Webster for spelling, *The Chicago Manual of Style* for nontechnical questions, and the Microsoft Writing Style Guide for technical style.

These are guidelines, not rules. Prefer clarity over rigid adherence. Don't rewrite existing comments or docs unless you're already editing that prose or the user asked for a style pass.

## When to use

Use this skill when you write or revise any of the following:

- Markdown docs (`README.md`, `AGENTS.md`, `docs/`)
- HTML help text and other user-facing copy
- Code comments and generated API docs (godoc, rustdoc, JSDoc, Swift doc comments)
- PR titles and bodies that explain behavior to a reader

For commit subject lines, keep the repo's usual imperative first line. Still apply inclusive language, precise word choice, and American spelling.

## Source priority

1. Project-specific guidance (`AGENTS.md`, the app README, pasta rules, language or framework conventions).
2. The language's comment *form* (for example, Go godoc starts with the symbol name).
3. This skill and the [official style guide](https://developers.google.com/style).
4. Merriam-Webster, Chicago, then Microsoft, as listed earlier.

If two sources conflict, keep the project or language form and apply Google style to word choice, tone, and grammar.

## Voice and grammar

Be conversational and friendly without being frivolous. Sound like a knowledgeable friend who understands what the reader wants to do. Don't use slang, internet abbreviations (`tl;dr`, `ymmv`), pop-culture jokes, or exclamation points.

- Address the reader as **you**. Don't use *we* for "you and I." *We* is OK only when it clearly means the project or organization, and the antecedent is obvious.
- Use **user** only for the person who uses the software that the *reader* is building. Don't call the reader "the user."
- Use **active voice**. Make it clear who performs the action.
- Use **present tense** for general behavior. Use future tense only when the action is actually later (for example, "The file will be archived the next time backup runs"). Don't use *will* to describe what a function does now. Don't use hypothetical *would*.
- Use standard American spelling and punctuation.
- Use common two-word contractions (`don't`, `isn't`, `can't`, `you're`). Don't invent contractions or use three-word forms (`mightn't've`).
- Put the **condition, goal, or circumstance before the instruction**, so the reader can skip it when it doesn't apply.

| Recommended | Not recommended |
| --- | --- |
| If the token is missing, return an error. | Return an error if the token is missing. |
| To delete the file, click **Delete**. | Click **Delete** if you want to delete the file. |
| The server sends an acknowledgment. | The server will send an acknowledgment. |
| The function returns the parsed path. | A parsed path is returned by the function. |

### Recommendations and requirements

Avoid *should*; it's ambiguous. Pick the word that matches the meaning:

| Meaning | Use |
| --- | --- |
| Required action or state | *must*, or an imperative ("Do the following.") |
| Recommended action | "We recommend…" or a clearly conventional *should* ("Use a strong password.") |
| Optional action | *can* |
| Expected outcome | State the fact ("The process returns 10 items.") |
| Possible outcome | *might* or *can* |
| Permission | *can*, not *may* |
| Legal or policy permission | *may* |

Don't use *shall* unless a lawyer asked for it. Don't use *could* when *can* works.

### Don't anthropomorphize

Don't give software or hardware human senses or speech.

| Recommended | Not recommended |
| --- | --- |
| The parser detects a new device. | The parser sees a new device. |
| A `Delimiter` specifies where to split the string. | A `Delimiter` tells the splitter where to break the string. |

## Comments versus documentation

Apply the same word choice, inclusive language, and grammar everywhere. Change *person* and *shape* to match the artifact.

### Documentation (README, AGENTS.md, HTML, tutorials)

- Use second person and the imperative for procedures.
- Write task-oriented titles when the page is a how-to.
- Use sentence case for titles and headings.
- Introduce code samples with a sentence. End that sentence with a colon when the sample follows immediately.
- Don't pre-announce unreleased features. Don't use *currently*, *soon*, *new*, *latest*, or *as of this writing* unless you give a date or version as an anchor.
- Identify the audience when it isn't obvious (developer, operator, or someone else) and stay consistent.

### API and doc comments

Follow the language's first-sentence convention, then apply this style to the rest.

- **Go:** `Parse` parses… (symbol name first). Don't start with "This function…"
- **Rust, Swift, JSDoc:** state what the item does in present tense. Don't restate the identifier as the whole description.
- First sentence: what the item does that you can't deduce from the name and signature.
- Later sentences: when to call it, preconditions, empty or error cases, defaults, and related APIs.
- Describe every exported type, function, parameter, return value, and error the reader can observe.
- If something is deprecated, say what to use instead.

### Inline comments

- Explain *why*, an invariant, a constraint, or a non-obvious consequence. Don't narrate the next line.
- Use present tense and active voice.
- Put the condition first when the comment is an instruction to a future reader ("If the buffer is empty, skip the flush. The writer already no-ops, but skipping avoids a metric bump.").
- Don't use *we* to mean the authors ("Here we check…"). State the fact or the reason.

### Don't write

- Filler: *just*, *simply*, *easy*, *obviously*, *please note*, *note that*, *basically*.
- Over-polite *please* in instructions ("Please click **Save**.").
- *Let's* ("Let's add a handler.").
- Directional UI language: *above*, *below*, *left*, *right*, *upper-right*. Use *earlier*, *preceding*, *later*, or *following*, or name the control.
- *Click on*. Use *click* on desktop and *tap* on touch.
- *Via*, *and/or*, `&` as a substitute for *and*, *e.g.* or *i.e.* in running text (write *for example* or *that is*).
- Figurative or violent jargon when a literal term exists.

## Formatting

- **Headings:** sentence case ("Source priority", not "Source Priority"). Use a unique `h1` / `#` per page. Don't skip heading levels. Don't use a heading as the only formatting for a short phrase; follow it with content.
- **Lists:** numbered lists for sequences; bullets for unordered items; description lists for term/definition pairs. Make items parallel. Start each item with a capital letter unless case is part of the data.
- **List punctuation:** end items with a period when they are sentences or include a verb. Omit the period for a single word, a phrase with no verb, an item that's entirely code, or an item that's only a link or title. If punctuation would be inconsistent, rewrite for parallel structure or punctuate every item.
- **Serial comma:** "strings, arrays, and objects."
- **Code in text:** put filenames, paths, commands, HTTP status codes, class names, method names, flags, and placeholders in code font. Don't inflect a code token (don't write "`Parse`s"). Add an English noun and inflect that: "call the `Parse` function."
- **Filenames:** write the `example.toml` file, not "the example.toml." Use the real spelling even if it doesn't follow hyphen-case.
- **Placeholders:** `UPPER_SNAKE_CASE` (`API_NAME`, `PATH`). After a command, introduce them with "Replace the following:"
- **UI labels:** bold (`**Save**`). If the label is also a code-like token, use bold and code font.
- **Dates:** January 19, 2017. If you must use digits only, use `YYYY-MM-DD`. Don't write `04/05/09`. Don't use seasons ("next summer").
- **Times:** 9:00 AM, 3 PM (all caps, no periods, space before AM or PM).
- **Versions:** "version 2.2 or later," not *higher*, *above*, or `2.2+`.
- **Numbers:** US grouping and a period for decimals. Hyphenate a number plus a spelled-out unit when they modify a noun ("a 10-minute timeout").
- **Ranges:** a hyphen (`10-20`), or *from* / *through* when a hyphen is ambiguous. Don't mix both.
- **Links:** descriptive text ("see [Procedures](https://developers.google.com/style/procedures)"), not *click here* or a raw URL. Don't reuse the same link text for two destinations. "For more information about X, see …" — not "See … for more information."
- **Images:** alt text that states the purpose. Don't put new information only in an image. Don't screenshot code; use a code block.
- **That / which:** *that* for restrictive clauses (no comma); *which* for nonrestrictive clauses (comma). Use *who* for people.

## Inclusive language and a global audience

Write US English that's easy to translate. Use short sentences, subject-verb-object order, and the main subject and verb near the start. Use consistent terms; don't vary synonyms for the same concept.

- Avoid idioms, humor, sports metaphors, and holiday or seasonal references.
- Use a diverse set of example names and `example.com` (or other reserved example domains).
- Don't use ableist, violent, or gendered figurative terms. Prefer literal replacements. See [references/word-list.md](references/word-list.md).
- When a non-inclusive identifier exists only in code you don't control, use it in code font, explain it once, and use the preferred term after that.
- Use singular *they*. Don't use gendered pronouns for a generic person.
- Don't present information with color or direction alone.

Load [references/word-list.md](references/word-list.md) when you choose a questionable term. If the term isn't there, check the [official word list](https://developers.google.com/style/word-list) and use the first Merriam-Webster spelling.

For before-and-after rewrites of docs and comments, see [references/examples.md](references/examples.md).

## Before you ship

Read the prose out loud (or subvocalize). If a sentence is awkward spoken, rewrite it.

Check that you:

- Used *you* for the reader and active, present-tense verbs.
- Put conditions before instructions.
- Used sentence-case headings and serial commas.
- Put code tokens and filenames in code font, with an English noun when you inflect.
- Removed *just*, *simply*, *easy*, *please*, *should* (unless you truly mean a soft recommendation), *via*, and directional *above* / *below*.
- Replaced non-inclusive or figurative jargon.
- Avoided time-anchored words unless a date or version is present.
- Didn't add comments that only repeat the next line of code.

## Official guide

- [About this guide](https://developers.google.com/style)
- [Highlights](https://developers.google.com/style/highlights)
- [Word list](https://developers.google.com/style/word-list)
- [API reference code comments](https://developers.google.com/style/api-reference-comments)
- [Voice and tone](https://developers.google.com/style/tone)
- [Second person](https://developers.google.com/style/person)
- [Active voice](https://developers.google.com/style/voice)
- [Present tense](https://developers.google.com/style/tense)
- [Sentence structure](https://developers.google.com/style/sentence-structure)
- [Procedures](https://developers.google.com/style/procedures)
- [Lists](https://developers.google.com/style/lists)
- [Headings](https://developers.google.com/style/headings)
- [Code in text](https://developers.google.com/style/code-in-text)
- [Inclusive documentation](https://developers.google.com/style/inclusive-documentation)
- [Writing for a global audience](https://developers.google.com/style/translation)
- [Timeless documentation](https://developers.google.com/style/timeless-documentation)
