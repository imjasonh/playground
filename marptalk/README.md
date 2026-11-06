# Marptalk

Present a [Marp](https://marp.app) deck with its speaker notes read aloud by
the browser's built-in text-to-speech, with subtitles. Each slide's HTML
comments are its voiceover. When the voiceover for a slide ends, the next
slide starts.

This is a browser-only port of
[imjasonh/marptalk](https://github.com/imjasonh/marptalk). That project used
the Marp CLI, Google Cloud Text-to-Speech, Puppeteer, and ffmpeg. This one
needs no account, API key, or server: the page renders the deck with a
bundled copy of Marp Core and speaks with the
[Web Speech API](https://developer.mozilla.org/docs/Web/API/SpeechSynthesis).

The app is meant for decks that an LLM writes. The
[marptalk skill](../.cursor/skills/marptalk/SKILL.md) tells an agent how to
write one, and `scripts/check.js` finds what to fix.

## Use it

Pick one of the bundled decks, or open your own `.md` file with **Open .md**
or by dropping it on the page. The file stays in the browser.

| Key | Action |
| --- | --- |
| Space or K | Play or pause |
| Left and right arrows | Previous or next slide |
| Home and End | First or last slide |
| `<` and `>` | Slower or faster |
| C | Subtitles on or off |
| M | Mute the voice; subtitles keep their timing |
| F | Full screen |

Clicking the slide also plays or pauses. Clicking a line in the
**Voiceover** list plays the slide from that line. The speed (0.5× to 2×),
voice, subtitle, and mute settings are saved in the browser.

The URL records the deck and slide, for example `?deck=gps#4`. Uploaded decks
aren't in the URL.

## Write a deck

A deck is ordinary Marp Markdown. Put the narration for each slide in an HTML
comment on that slide:

```markdown
---
marp: true
title: How GPS finds you
theme: uncover
lang: en-US
---

# Clocks in orbit

- About 30 satellites
- Atomic clocks on board

<!--
The GPS constellation has about thirty working satellites. Each one carries
atomic clocks and broadcasts the exact time the signal left.
-->
```

- `lang` picks the voices offered and the sentence rules for subtitles.
- `title` names the deck in the page title. Without it, the first heading is
  used.
- Several comments on one slide are read in order. A comment that is only
  Marp directives, such as `<!-- _class: lead -->`, isn't read.
- Each sentence is spoken and shown as one subtitle. A sentence longer than
  120 characters is split at a comma or a space.

Check a deck before you present it:

```bash
node marptalk/scripts/check.js my-deck.md
```

It reports slides with no voiceover, Markdown or URLs in the voiceover, too
much narration on one slide, too much text on screen, and math. It needs no
`npm install`.

### What renders

Everything Marp Core renders, except math: `$...$` stays as text. Built-in
themes are `default`, `gaia`, and `uncover`. Code fences are highlighted for
the languages listed in `scripts/vendor.js`; others render as plain text.
Inline HTML follows Marp's default allowlist, so `<div class="...">` works but
`style` attributes, `<svg>`, and `<iframe>` don't. Use the `style` directive
for CSS.

## Speech

Browsers differ in the voices they have. Chrome on desktop has network voices
named "Google ..."; Safari and macOS have voices named "(Premium)" or
"(Enhanced)" once you download them in system settings. The voice list shows
the voices for the deck's language, best guess first.

The narrator speaks one sentence at a time. That keeps each utterance short,
which matters in Chrome: its network voices stop after about 15 seconds of one
utterance. When a browser has no voices, or speech fails, the subtitle for
that sentence stays up for as long as it would take to say, and the deck keeps
going.

## Run locally

```bash
cd marptalk
npm start
```

Open http://localhost:3000.

## Test

```bash
cd marptalk
npm test
```

The tests cover splitting notes into subtitles, the narrator and player (with
a fake speech synthesizer and clock), voice choice, deck rendering, the deck
checks, and the bundled decks.

## Vendored Marp Core

`vendor/marp.js` and `vendor/marp-browser.js` are Marp Core bundled with
esbuild, without math. To update them after bumping `@marp-team/marp-core`:

```bash
npm install
npm run vendor
```

## Fixed from the original

- Browser speech never ran: `generate-html.js` loaded the notes but never put
  them in the page, and it had a syntax error.
- Notes were split from Marp's notes file on `---`, so a slide without notes
  shifted every later voiceover onto the wrong slide. Notes now come from Marp
  Core per slide.
- Long notes stalled in Chrome, which drops utterances longer than about 15
  seconds without an `end` event.
- Pause restarted the slide's narration from the beginning. It now resumes at
  the current sentence.
- After you moved to another slide, the previous slide's audio could still end
  and advance the deck a second time.
- The slide count used a selector that never matched, and its fallback counted
  every `<section>`, so slides with background images counted more than once.
