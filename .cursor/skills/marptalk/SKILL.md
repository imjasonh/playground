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
- In a flex or grid layout, give a column that holds a code block a fixed width. Marp shrinks a code block to fit its container, and a flex item that sizes to its content collapses.
- Math is not rendered; `$...$` stays literal and the check flags it. Write formulas as text or code.
- Avoid images unless the user supplies them. Remote images load from their host, and a missing one leaves a hole. Use `![bg right](url)` syntax only for images you know exist.
- Inline HTML follows Marp's allowlist: `div`, `span`, `table`, `mark`, `kbd`, `sub`, `sup`, and similar work with a `class`. `style` and `id` attributes are stripped, and `<iframe>` and `<script>` render as text. The check flags tags that render as text.

## Links

- Put links on the slide as Markdown links, such as `[life-lab](https://imjasonh.github.io/playground/life-lab/)`, and say in the voiceover that the link is on the slide. Never put a URL in the voiceover.
- Use full URLs. A relative link breaks once the deck is uploaded on its own, and the check flags it. Link apps in this repo at `https://imjasonh.github.io/playground/<app>/`.
- Links open in a new tab and pause playback. `[the rules](#3)` jumps to slide 3 and keeps playing.
- Link only to pages you know exist.

## Diagrams

When a slide explains structure, flow, geometry, or change over time, draw it. A diagram with a voiceover that walks through it beats bullets. Each bundled deck has an example: the object graph in `git-objects.md`, the circles in `gps.md`, and the cell grids in `game-of-life.md`.

Draw diagrams as inline `<svg>` in the slide, so the deck stays one file. Marp has no Mermaid or other diagram syntax, and images beside an uploaded deck don't load.

```html
<svg viewBox="0 0 1000 300" width="1000" role="img" aria-label="Commit B points at commit A">
  <rect x="40" y="120" width="220" height="60" rx="10" fill="none" stroke="currentColor" stroke-width="2" />
  <text x="150" y="158" text-anchor="middle" font-size="24" fill="currentColor">commit A</text>
  <line x1="740" y1="150" x2="276" y2="150" stroke="#2563eb" stroke-width="2" />
  <polygon points="262,150 280,141 280,159" fill="#2563eb" />
  <rect x="740" y="120" width="220" height="60" rx="10" fill="#dbeafe" stroke="#2563eb" stroke-width="2" />
  <text x="850" y="158" text-anchor="middle" font-size="24" fill="currentColor">commit B</text>
</svg>
```

- Allowed elements: `svg`, `g`, `title`, `rect`, `circle`, `ellipse`, `line`, `polyline`, `polygon`, `path`, `text`, and `tspan`. Allowed attributes: geometry (`x`, `y`, `width`, `height`, `rx`, `cx`, `r`, `points`, `d`, and so on), `viewBox`, `transform`, `class`, `role`, `aria-label`, `fill`, `stroke`, their `-opacity`, `-width`, `-dasharray`, `-linecap`, and `-linejoin` variants, `opacity`, `font-size`, `font-weight`, `font-family`, `font-style`, `text-anchor`, and `dominant-baseline`.
- Not allowed: `style`, `id`, `<marker>`, `<defs>`, `<use>`, `<image>`, `<foreignObject>`, gradients, and filters. Draw arrowheads as small `<polygon>`s at the line ends.
- Leave no blank lines inside an `<svg>`. Markdown ends the HTML block at a blank line and shows the rest as text. The check flags this.
- Work in slide units. A 16:9 slide is 1280 by 720, and about 1100 by 480 is free under a heading. Set `width` on the `<svg>` and keep every shape inside the `viewBox`; anything outside is clipped.
- Use `fill="currentColor"` for text and outlines so they follow the theme, including `class: invert`. Use one accent color for the part the voiceover is about, and say which color it is: "the blue boxes are new".
- Center a diagram with `svg { display: block; margin: 0 auto; }` in the `style` front matter. Beside bullets, use a grid with the text in `1fr` and the SVG in `auto`, as on the second slide of `game-of-life.md`.
- Add `role="img"` and an `aria-label` that says what the diagram shows.
- Labels count toward the 50 words on screen. Keep them to a few words each.
- Compute coordinates instead of guessing. Check where lines cross boxes, and that labels don't overlap lines. Look at the slide in the app before you hand it back.

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
