# MPEG Canvas

A static, browser-only MPEG transport stream player. It decodes MPEG-1 video
and MP2 audio without blocking the page:

```
fetch / File.stream()
        │ transferable ArrayBuffers
        ▼
dedicated worker ── JSMpeg WebAssembly MPEG-1 + MP2 decoder
        │                            │
        │ YCbCr textures             │ transferable PCM
        ▼                            ▼
OffscreenCanvas WebGL          MessagePort → AudioWorklet
```

The worker renders directly into the page's canvas, so decoded video frames do
not cross back through the main thread. PCM travels directly from the decoder
worker to the audio render thread. The `AudioWorklet` keeps a bounded planar
queue and resamples MP2 output to the browser's audio-device sample rate.

## Supported media

- MPEG transport stream (`.ts`, 188-byte packets)
- MPEG-1 video
- Optional MPEG-1 Audio Layer II (MP2), mono or stereo
- No B-frames (a JSMpeg decoder limitation)

Browsers do not expose portable native MPEG-1/MP2 support through WebCodecs, so
this player uses JSMpeg's small WASM software decoder. The WASM decoder is
written in C. A Rust wrapper would not improve the hot path, and the available
pure-Rust MPEG video crates do not yet provide an equally proven browser
playback pipeline.

Convert other media with FFmpeg:

```bash
ffmpeg -i input.mp4 \
  -c:v mpeg1video -q:v 3 -bf 0 \
  -c:a mp2 -b:a 160k \
  -f mpegts output.ts
```

Remote URLs must allow browser CORS requests. Local files are read in chunks
and never uploaded.

## Run and test

```bash
npm install
npm run vendor
npm start

npm test
npm run test:e2e
```

`npm run vendor` copies the pinned `@seydx/jsmpeg` distribution and license
into `vendor/`, keeping the deployed GitHub Pages app independent of a CDN.

## Performance choices

- JSMpeg's MPEG-1 and MP2 WebAssembly decoders
- Dedicated decoder/demux worker
- Transferable input chunks with backpressure
- `OffscreenCanvas` rendering in the worker
- WebGL shader-based YCbCr-to-RGB conversion, with Canvas 2D fallback
- A direct `MessageChannel` from the decoder worker to an `AudioWorklet`
- No per-frame RGBA copies through the UI thread
- Playback pauses when the tab is hidden

The included demo is a short FFmpeg-generated MPEG-TS fixture.
