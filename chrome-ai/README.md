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

- Press Enter to send and Shift+Enter for a new line.
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

The status line shows how much of the model's context window the chat has
used. When the conversation outgrows it, Chrome drops the oldest messages and
the status line says so.

## Markdown

Replies render as Markdown with [marked](https://github.com/markedjs/marked)
(GitHub-flavored: tables, fenced code, task lists). The HTML then goes through
[DOMPurify](https://github.com/cure53/DOMPurify), because a reply can repeat
HTML from the prompt. The sanitizer also drops images and other media, which
would load a URL as soon as they render. Links open in a new tab.

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
`src/attachments.js` on plain objects and `Blob`s, and `src/markdown.js`
against the vendored marked, so they don't need Chrome or the model.
