# LinkChat

Serverless, peer-to-peer chat with **audio, video, text, and file transfer** —
no backend, no accounts, no signaling server. Two browsers connect directly
over WebRTC; you bootstrap the connection by **sharing a link**.

## How it can work without a server

A WebRTC call normally needs a *signaling server* only to swap two small blobs
of connection info (SDP + ICE candidates) before the peer-to-peer link forms.
Once connected, audio/video/data already flow directly between browsers.

LinkChat replaces that server with **manual, link-based signaling**:

1. **Host** clicks _Create invite link_. The browser builds a WebRTC **offer**,
   waits for ICE gathering to finish (so every candidate is baked into the SDP —
   "non-trickle" ICE), packs it into a URL-safe token, and puts it in the page's
   URL hash. Host copies the link and sends it to a friend.
2. **Guest** opens the link. The offer is read straight out of the hash (hashes
   never hit a server), the browser creates an **answer**, and shows a short
   **reply code**.
3. **Guest** sends that reply code back (any channel — chat, email…). **Host**
   pastes it and clicks _Connect_.
4. The direct peer-to-peer connection opens. Video, voice, chat, and files all
   flow browser-to-browser.

Public **STUN** servers (Google's) are used purely to discover each peer's
public address for NAT traversal — they never see your media or messages, and
they aren't a backend we operate.

### The one real limitation

Peers behind **symmetric NAT** (some corporate/mobile networks) can't establish
a direct path with STUN alone; they need a **TURN relay** to forward packets.
A TURN relay is a server, so a genuinely serverless app can't provide one — such
networks may fail to connect. This is a fundamental WebRTC constraint, not a bug
in LinkChat. Everything else (same LAN, most home networks) works directly.

Other practical notes:

- **HTTPS is required** for camera/microphone access, so use the deployed
  GitHub Pages URL (or `localhost`) rather than a raw `file://` page.
- The handshake is a two-way exchange (invite out, reply back) because WebRTC
  needs both sides' descriptions. That's inherent to serverless signaling.
- Text chat and file transfer work even if you turn the camera and mic off.

## Features

- One-to-one video + voice call
- Real-time text chat over a WebRTC data channel
- File transfer of any size (chunked with backpressure), with progress bars and
  a download link on the receiving side
- Toggle camera / mic mid-call; hang up to reset
- No dependencies, no build step — plain HTML + ES modules

## Run locally

```bash
cd linkchat
npm start          # serves at http://localhost:3000
```

Open two tabs (or two devices on the same network) to try a call: create an
invite in one, open the link in the other, and pass the reply code back.

## Test

Pure signaling and file-protocol helpers are unit tested with the Node test
runner (no browser needed):

```bash
npm test
```

## Layout

```
linkchat/
├── index.html            # UI shell
├── styles.css
├── src/
│   ├── signaling.js      # encode/decode offers & answers into shareable tokens
│   ├── fileTransfer.js   # chunking + reassembly protocol helpers
│   └── app.js            # WebRTC wiring, media, chat, file UI
└── tests/
    ├── signaling.test.js
    └── fileTransfer.test.js
```
