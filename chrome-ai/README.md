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

The status line shows how much of the model's context window the chat has
used. When the conversation outgrows it, Chrome drops the oldest messages and
the status line says so.

## Tests

```bash
npm test
```

The tests run `src/model.js` in Node against a fake `LanguageModel`, so they
don't need Chrome or the model.
