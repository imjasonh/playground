# WebRTC

Serverless, peer-to-peer app with **audio, video, text, file transfer, live
location sharing, and live captions** — no backend, no accounts, no signaling
server. Two browsers connect directly over WebRTC; you bootstrap the connection
by **sharing a link**.

> Formerly called **LinkChat**. The app moved to the `webrtc/` directory and was
> renamed to reflect that it's a small showcase of what the WebRTC + modern
> browser APIs can do with zero backend.

## How it can work without a server

A WebRTC call normally needs a *signaling server* only to swap two small blobs
of connection info (SDP + ICE candidates) before the peer-to-peer link forms.
Once connected, audio/video/data already flow directly between browsers.

This app replaces that server with **manual, link-based signaling**:

1. **Host** clicks _Create invite link_. The browser builds a WebRTC **offer**,
   waits for ICE gathering to finish (so every candidate is baked into the SDP —
   "non-trickle" ICE), packs it into a URL-safe token, and puts it in the page's
   URL hash. Host copies the link (or uses the native **Share** sheet) and sends
   it to a friend.
2. **Guest** opens the link. The offer is read straight out of the hash (hashes
   never hit a server), the browser creates an **answer**, and shows a short
   **reply code**.
3. **Guest** sends that reply code back (any channel — chat, email…). **Host**
   pastes it and clicks _Connect_.
4. The direct peer-to-peer connection opens. Video, voice, chat, files,
   location, and captions all flow browser-to-browser.

Public **STUN** servers (Google's) are used purely to discover each peer's
public address for NAT traversal — they never see your media or messages, and
they aren't a backend we operate.

### The one real limitation

Peers behind **symmetric NAT** (some corporate/mobile networks) can't establish
a direct path with STUN alone; they need a **TURN relay** to forward packets.
A TURN relay is a server, so a genuinely serverless app can't provide one — such
networks may fail to connect. This is a fundamental WebRTC constraint, not a bug.
Everything else (same LAN, most home networks) works directly.

Other practical notes:

- **HTTPS is required** for camera/microphone, geolocation, screen capture, and
  speech recognition, so use the deployed GitHub Pages URL (or `localhost`)
  rather than a raw `file://` page.
- The handshake is a two-way exchange (invite out, reply back) because WebRTC
  needs both sides' descriptions. That's inherent to serverless signaling.
- Text chat, file transfer, and location sharing work even if you turn the
  camera and mic off.

## Features

- One-to-one video + voice call
- Real-time text chat over a WebRTC data channel
- File transfer of any size (chunked with backpressure), with progress bars and
  a download link on the receiving side
- **Location sharing** — drop your current position once, or share **live
  location** that updates as you move. Permission-gated by the browser
  (Geolocation API), with the current grant reflected via the Permissions API.
  Shared positions render as a map link (OpenStreetMap, no API key).
- **Live captions** — realtime speech-to-text subtitles for the call via the
  Web Speech API, with optional **on-device translation** and **text-to-speech**
  in another language. See [Live captions](#live-captions).
- **Screen sharing** — swap your outgoing camera feed for your screen
  (`getDisplayMedia`), no renegotiation needed.
- **Native share** of the invite link via the Web Share API where supported.
- **QR codes** for both the invite link and the reply code — scan to join
- Toggle camera / mic mid-call; hang up to reset
- One small vendored dependency (a QR encoder); no build step — plain HTML + ES
  modules

## Location sharing

Two buttons appear once the peer connection is open:

- **📍 Share location** reads a single position with `getCurrentPosition` and
  sends it to your peer.
- **Live location** starts a `watchPosition` stream and forwards each update,
  tagged as live, until you toggle it off (which sends a "stopped" note).

The browser prompts for permission before the first read. Where the
[Permissions API](https://developer.mozilla.org/docs/Web/API/Permissions_API) is
available, the hint under the buttons reflects whether location is granted,
prompt-on-use, or blocked. Received coordinates are shown with their accuracy and
a link to OpenStreetMap; nothing is stored or sent anywhere but to your peer.

## Live captions

Toggle **Captions** during a call to get realtime subtitles, powered by the
[Web Speech API](https://developer.mozilla.org/docs/Web/API/Web_Speech_API)
(`SpeechRecognition`).

Recognition only ever hears your **own** microphone, so captions in a two-way
call are cooperative: each peer transcribes their own speech on-device and
streams the text to the other over the data channel. Your words show over your
local preview; your peer's words show over their video — no captions server, no
audio ever leaves the call for transcription by us.

Interim results update live as you speak and finalized lines linger briefly
before clearing. It's Chromium-only in practice (Chrome/Edge, and Safari with
the `webkit` prefix); where `SpeechRecognition` is unavailable (e.g. Firefox)
the Captions button stays disabled. The recognition language follows
`navigator.language`, and each caption line is tagged with that language so the
receiver can translate it.

### Realtime translation + text-to-speech

Because captions arrive as tagged text, the receiver can go further with two
more on-device, no-backend browser APIs:

- **Translate captions to** — pick a language and incoming captions are
  translated locally with the built-in-AI
  [Translator API](https://developer.mozilla.org/docs/Web/API/Translator)
  (`Translator.create({ sourceLanguage, targetLanguage })`). The model runs
  on-device (the first use downloads a small language pack); nothing is sent to
  a translation server. Only settled (final) lines are translated, so interim
  text stays responsive.
- **🔊 Speak** — read incoming captions aloud with the Web Speech API's
  [`SpeechSynthesis`](https://developer.mozilla.org/docs/Web/API/SpeechSynthesis),
  using a voice that matches the target language. Combined with translation,
  this gives spoken, live interpretation of your peer's speech in your language.

Both are receive-side: your peer speaks and captions in their language, and your
browser translates/speaks in yours — no protocol change and no server. Where the
Translator API isn't available (currently Chrome-only), the language picker is
disabled with a hint; text-to-speech falls back to the caption's original
language when translation is off or unavailable.

## A note on payments

An earlier version experimented with **requesting money via the Web Payments
API** (`PaymentRequest`). It was removed: that API only *presents* a request and
then hands off to a payment handler/processor to actually move the money — and a
payment handler is itself a backend. With no handler installed, `show()` opens
the native sheet and spins on "Processing…" forever, because nothing ever
settles the payment. A genuinely serverless app can't provide that handler, so
the feature couldn't actually work here and was dropped.

## What else can a serverless P2P app do with browser APIs?

Once two browsers share a `RTCPeerConnection` + data channel, a surprising
amount is possible with **no backend** — the data channel is just a reliable,
ordered, low-latency pipe, and the peers are ordinary web pages with access to
the full platform. Implemented here: **Geolocation**, **Permissions**,
**Screen Capture** (`getDisplayMedia`), **Web Speech** (recognition for live
captions **and** synthesis for text-to-speech), the built-in-AI **Translator
API** (on-device caption translation), **Web Share**, **Clipboard**,
**Compression Streams** (link compression), and **Barcode Detection** (QR reply
scanning).

Other capabilities that fit the same "just a link, no server" model and would be
natural additions:

- **Wake Lock API** — keep the screen awake during a call.
- **Notifications + Page Visibility** — alert on a new message when the tab is
  hidden (local notifications need no push server).
- **Vibration API** — buzz on incoming messages/calls (mobile).
- **File System Access API** — stream received files straight to disk instead of
  buffering a Blob in memory.
- **Web Audio API** — mic level meters, mute detection, push-to-talk, simple
  voice effects.
- **Canvas / MediaStream capture** — a shared whiteboard or collaborative
  drawing sent over the data channel.
- **Gamepad / Pointer / Device Orientation** — real-time input sharing for P2P
  games or remote control.
- **Media Session API** — lock-screen/hardware media controls for the call.
- **Language Detector API** — auto-detect a caption's language when the sender
  doesn't tag it, before translating.
- **Contact Picker / Web Share Target** — smoother invite sharing on mobile.
- **IndexedDB** — persist chat/transfer history locally (per browser, no server).
- **WebCodecs / Insertable Streams** — custom encoding or end-to-end media
  encryption on top of the peer connection.

All of these run entirely client-side; the only thing a backend would add is
*discovery/relay* (a signaling or TURN server), which this app deliberately does
without.

## Sharing via QR code

Both the invite and the reply are shown as QR codes as well as text:

- The **invite** QR encodes the full invite URL, so the other person can scan
  it with their **phone's native camera** to open the link and join — no app or
  copy-paste needed.
- The **reply** QR encodes the reply code. The host can read it with the
  **Scan reply with camera** button (shown where the browser supports the
  `BarcodeDetector` API — Chrome/Edge on Android, Windows, macOS, ChromeOS), or
  just copy-paste the code. (Safari/iOS lack in-app `BarcodeDetector`, so use
  copy-paste there.)

### Why the links had to be compressed first

A QR code holds at most ~2953 bytes, but a raw WebRTC session description is
~7–9 KB — far too big. The app therefore **DEFLATE-compresses** each payload
(via the Compression Streams API) before encoding it, which shrinks a typical
description ~4× (to ~1.7 KB) so it fits in a QR and also keeps the copyable link
short. Compressed links use a `#z=` hash; older uncompressed `#c=` links are
still accepted. If a session description is unusually large and still won't fit
a QR, the code is hidden and you fall back to the copyable link/code.

## Run locally

```bash
cd webrtc
npm start          # serves at http://localhost:3000
```

Open two tabs (or two devices on the same network) to try a call: create an
invite in one, open the link in the other, and pass the reply code back.

## Test

Pure signaling, file-protocol, location, caption, and translation helpers are
unit tested with the Node test runner (no browser needed):

```bash
npm test
```

## Layout

```
webrtc/
├── index.html            # UI shell
├── styles.css
├── src/
│   ├── signaling.js      # encode/decode offers & answers into shareable tokens
│   ├── codec.js          # DEFLATE compress/inflate (Compression Streams API)
│   ├── fileTransfer.js   # chunking + reassembly protocol helpers
│   ├── location.js       # geolocation message + formatting helpers
│   ├── captions.js       # Web Speech caption protocol + transcript helpers
│   ├── translation.js    # Translator API + SpeechSynthesis helpers
│   ├── qr.js             # QR render wrapper (canvas)
│   ├── app.js            # WebRTC wiring, media, chat, files, location, captions, QR
│   └── vendor/
│       └── qrcode-generator.js   # vendored MIT QR encoder (ES module wrapper)
└── tests/
    ├── signaling.test.js
    ├── codec.test.js
    ├── fileTransfer.test.js
    ├── location.test.js
    ├── captions.test.js
    ├── translation.test.js
    └── qr.test.js
```
