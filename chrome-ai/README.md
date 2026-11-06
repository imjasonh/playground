# Chrome AI

Chat with the language model built into Chrome (Gemini Nano), through the
[Prompt API](https://github.com/webmachinelearning/prompt-api). The model
runs on your device, so prompts and replies don't leave it.

This app starts with a single chat window. Later experiments with Chrome's
built-in AI APIs go here too.

## Requirements

- Desktop Chrome with the Prompt API exposed to web pages. If your Chrome
  version doesn't expose it by default, open `chrome://flags`, enable
  **Prompt API for Gemini Nano**, and restart Chrome.
- Hardware that Chrome accepts for the on-device model. When the device
  doesn't qualify, the page reports that the model isn't available.

The first time you use the model, the page shows a **Download model** button.
Chrome downloads the model once and shares it with every site that uses it.

## Run locally

```bash
cd chrome-ai
npm start
```

Open http://localhost:3000. The Prompt API needs a secure context, and
`localhost` counts as one.

## Use it

- Press Enter to send and Shift+Enter for a new line. On a touch keyboard,
  Enter adds a new line and **Send** sends.
- **Stop** ends the reply in progress and keeps the text so far.
- **New chat** discards the session and its history.

## Attachments

To attach files, click the paperclip, drag files onto the page, or paste an
image into the message box. The model takes three kinds of input:

- Images go to the model as they are, if the device supports image input.
- Audio clips go to the model as they are, if the device supports audio input.
- Text files, such as `.txt`, `.md`, `.csv`, `.json`, and source code, are
  read into the prompt. They can be up to 512 KB, and they still have to fit
  in the context window. SVG files count as text.

On load, the page asks Chrome which of image and audio input this device
supports. The file picker offers only those, and the page rejects other files
with a message. The model can't read PDFs, Office documents, or video.

## Saved chats

Each chat is saved in the browser's IndexedDB, attachments included, so
nothing leaves the device. **Chats** lists them, most recent first, and each
one has a delete button.

When you open a saved chat, the page shows its messages and creates a model
session with them as `initialPrompts`, so the next message continues the
conversation. A compacted chat starts from its summary and the messages after
it. If that still doesn't fit in the context window, the page drops the
oldest exchanges until it does, compacts the chat, and the status line says
so.

Storage is versioned in two places:

- `DB_VERSION` in `src/store.js` covers the IndexedDB object stores. To add
  a store or index, bump it and add a step to `upgrade`.
- `CONVERSATION_VERSION` in `src/history.js` covers the record format. To
  change the format, bump it and add a step to `MIGRATIONS` that upgrades a
  record from the previous version. Records come up to date when they're
  read. A record from a newer version of the app is skipped and left in
  storage.

## Context window

The thin bar on the line above the message box shows how much of the model's
context window the chat holds. Hover over it or focus it for the token count.

When a chat fills up, the page compacts it:

1. After a reply, if the session holds 70% or more of its window, the model
   summarizes every message except the last two exchanges. It does this in a
   separate session, folding in the previous summary if there is one.
1. A new session starts with the summary as a system prompt, followed by the
   last two exchanges word for word. The next message waits for this.
1. Before a message is sent, the page measures it, where Chrome supports
   `measureContextUsage()`. If the message would push the session past 90%,
   the page compacts first.

The summary is saved with the chat (`summary` in the record), so a resumed
chat replays the summary instead of the old messages. The log keeps every
message and shows a divider where the summarized part ends. The constants are
in `src/compaction.js`.

## Markdown

Replies render as Markdown with [marked](https://github.com/markedjs/marked)
(GitHub-flavored: tables, fenced code, task lists). The HTML then goes through
[DOMPurify](https://github.com/cure53/DOMPurify), because a reply can repeat
HTML from the prompt. The sanitizer keeps HTML only (no SVG or MathML) and
also drops images, media, `<style>`, inline `style` attributes, and forms.
Those would load a URL as soon as they render, which could send chat text
off the device, or would restyle the page. Links open in a new tab.

The page's Content-Security-Policy backs this up. It allows scripts, styles,
and images only from the page itself, plus `blob:` images and media for
attachments, so the browser refuses any other load even if the sanitizer
misses one.

Both libraries are vendored in `vendor/`, so Pages serves the app without a
build step. After you bump either package, run:

```bash
npm install
npm run vendor
```

## Tests

```bash
npm test
```

The tests run `src/model.js` in Node against a fake `LanguageModel`,
`src/store.js` against [fake-indexeddb](https://github.com/dumbmatter/fakeIndexedDB),
`src/attachments.js`, `src/history.js`, and `src/compaction.js` on plain
objects, `Blob`s, and fake sessions, and
`src/markdown.js` against the vendored marked, so they don't need Chrome or
the model.
