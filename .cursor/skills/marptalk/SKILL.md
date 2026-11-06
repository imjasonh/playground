---
name: marptalk
description: >-
  Write a narrated Marp deck for marptalk: slides plus a spoken voiceover in
  each slide's speaker notes, read aloud by browser text-to-speech with
  subtitles. Use when asked for a presentation, talk, explainer, lesson, or
  slideshow with narration or voiceover, or when editing a deck under
  marptalk/decks.
---

# Marptalk decks

A marptalk deck is one Marp Markdown file. The slides are what the viewer sees. The HTML comments on each slide are what a synthetic voice says while that slide is up, and each spoken sentence is also shown as a subtitle. The app is `marptalk/` in this repo, published at `https://imjasonh.github.io/playground/marptalk/`. Read one of the bundled decks in `marptalk/decks/` before you write a new one; `git-objects.md` is the plainest.

## Workflow

1. Settle the topic, the audience, and a length. Default to 8 to 12 slides, which is 3 to 6 minutes at 1×.
2. Outline one sentence per slide: the claim that slide makes. If two slides make the same claim, merge them. If a claim needs "and", split it.
3. Write the slides, then the voiceover for each.
4. Run `node marptalk/scripts/check.js <deck.md>` and fix every finding. It needs no `npm install`. It exits 1 while there are findings.
5. Read the voiceover aloud, or play the deck in the app. Rewrite any sentence you stumble on.

## File shape

```markdown
---
marp: true
title: How GPS finds you
theme: uncover
paginate: true
lang: en-US
---

<!-- _class: lead -->
<!-- _paginate: false -->

# How GPS finds you

Time, distance, and relativity

<!--
Your phone can tell where you are to within a few meters, without sending a
single bit to space. It only listens.
-->

---

# Time becomes distance

...
```

- Always set `marp: true`, `title`, and `lang`. `lang` selects the voices and the sentence rules. Write the voiceover in that language.
- Themes are `default`, `gaia`, and `uncover`. Add `class: invert` for a dark deck. Put deck-wide CSS in the `style` front matter key, not in `style` attributes, which are stripped.
- Use `<!-- _class: lead -->` for the title and closing slides, and `<!-- _paginate: false -->` on the title slide. Use `false`, not `skip`, so Marp's page number matches the app's slide counter.
- Separate slides with `---` on its own line.

## Slides

The slide is what the viewer looks at while listening. It holds the thing that is hard to say aloud: a table, a code sample, a diagram, a number.

- Make each heading a claim, not a topic. "Branches are files with a hash in them", not "Branches".
- Keep visible text under 50 words. The check flags more. Move explanation into the voiceover.
- Use three or four bullets of a few words each, or one table, one code block, or one big number. Not all of them.
- Don't put on the slide what the voice says word for word. The two should support each other.
- Code blocks are syntax-highlighted for common languages (see `KEEP_LANGUAGES` in `marptalk/scripts/vendor.js`). Others render as plain text. Keep code under about 10 lines.
- Text diagrams in a ```` ```text ```` fence work. In a flex or grid layout, give each column a fixed width. Marp shrinks a code block to fit its container, and a flex item that sizes to its content collapses.
- Math is not rendered; `$...$` stays literal and the check flags it. Write formulas as text or code.
- Avoid images unless the user supplies them. Remote images load from their host, and a missing one leaves a hole. Use `![bg right](url)` syntax only for images you know exist.
- Inline HTML follows Marp's allowlist: `div`, `span`, `table`, `mark`, `kbd`, `sub`, `sup`, and similar work with a `class`. `style` and `id` attributes are stripped, and `<svg>`, `<iframe>`, and `<script>` render as text.

## Voiceover

The voiceover is a script for a voice, read by browser text-to-speech at the speed the viewer picks.

- Every slide gets a voiceover. A slide without one stays up for 3 seconds during playback, and the check flags it.
- Aim for 40 to 120 words per slide, about 15 to 45 seconds. The check flags more than 160. Split the slide instead.
- Write plain sentences, the way you would say them. No Markdown, bullets, URLs, emoji, or arrows. The check flags these. The voice would read `**`, `->`, or "h t t p s" aloud.
- Keep sentences under about 25 words. Each sentence is one subtitle. A sentence longer than 120 characters is split at a comma, then at a space, so a long sentence still reads as two subtitles.
- Write numbers and symbols the way they should sound when a voice could read them two ways: "twenty thousand kilometers", "thirty eight microseconds", "B three slash S two three". Years and small counts are fine as digits.
- Write initialisms with spaces when they are said letter by letter and a voice might pronounce them as a word: "M I T". Common ones such as GPS are fine.
- Refer to the slide: "this table", "the second column", "on the left". The viewer is looking at it.
- Don't start a comment with a word that is a Marp directive name followed by a colon (`header:`, `footer:`, `class:`, `color:`, `backgroundColor:`, `paginate:`, `theme:`). Marp reads that comment as a directive and it is never spoken.
- Several comments on one slide are read in order, so you can keep a directive comment and the voiceover separate.

## Structure

- Open with a hook on the title slide: a surprising fact or a question the deck answers. Not "In this presentation we will".
- Build one idea per slide, each depending only on earlier slides.
- Close with a recap slide that restates the claims in order, and say where to go next if there is a real place, such as another app in this repo.
- Check facts. Dates, numbers, and names in a narrated deck sound authoritative. If you are unsure of a figure, round it and say "about", or leave it out.

## Adding a bundled deck

To add a deck to the app's picker, save it as `marptalk/decks/<id>.md` and add `{id, title}` to `DECKS` in `marptalk/src/decks.js`, with `title` equal to the deck's `title`. `npm test` in `marptalk/` renders every bundled deck and fails on any check finding.
