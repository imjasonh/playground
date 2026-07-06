// WebRTC — serverless, link-based peer-to-peer app with audio, video, files,
// live location sharing, and payment requests.
//
// There is no backend. To start a call, one person ("host") creates an offer
// that is packed into a shareable link. The other person ("guest") opens the
// link, which produces a short reply code they send back. Pasting that reply
// completes the WebRTC handshake and the peer-to-peer connection opens
// directly between the two browsers. Public STUN servers help traverse NATs;
// no media or messages pass through any server we run.

import {
  encodeSignalCompressed,
  buildCompressedLink,
  decodeAnySignal,
  tokenFromUrl,
  extractToken,
} from "./signaling.js";
import { renderToCanvas, QrCapacityError } from "./qr.js";
import {
  CHUNK_SIZE,
  MESSAGE_KIND,
  createFileMeta,
  createChatMessage,
  createFileEnd,
  chunkRanges,
  formatBytes,
  FileAssembler,
} from "./fileTransfer.js";

// Public STUN servers only. STUN just tells each peer its public address; it
// never relays media. Symmetric-NAT networks that need a TURN *relay* won't
// connect here, because a relay requires a server we don't run.
const ICE_SERVERS = [
  { urls: "stun:stun.l.google.com:19302" },
  { urls: "stun:stun1.l.google.com:19302" },
];

const ICE_GATHER_TIMEOUT_MS = 4000;
// Pause sending file chunks when the channel's send buffer climbs past this,
// resume once it drains — simple backpressure so we don't blow past memory.
const BUFFER_HIGH = 8 * 1024 * 1024;
const BUFFER_LOW = 1 * 1024 * 1024;

const state = {
  role: null, // "host" | "guest"
  pc: null,
  channel: null,
  localStream: null,
  wantCamera: true,
  wantMic: true,
  incoming: null, // active FileAssembler
  sending: false,
};

const el = {};

function $(id) {
  return document.getElementById(id);
}

function cacheElements() {
  const ids = [
    "screen-start",
    "screen-invite",
    "screen-reply",
    "screen-call",
    "start-title",
    "start-intro",
    "opt-camera",
    "opt-mic",
    "start-button",
    "start-error",
    "invite-link",
    "copy-invite",
    "invite-qr",
    "scan-reply",
    "answer-input",
    "answer-connect",
    "invite-status",
    "reply-code",
    "copy-reply",
    "reply-qr",
    "reply-status",
    "scanner",
    "scan-video",
    "scan-cancel",
    "local-video",
    "remote-video",
    "remote-placeholder",
    "toggle-cam",
    "toggle-mic",
    "hangup",
    "call-status",
    "chat-log",
    "chat-input",
    "chat-send",
    "file-input",
    "file-list",
  ];
  for (const id of ids) el[id] = $(id);
}

function showScreen(name) {
  for (const key of ["screen-start", "screen-invite", "screen-reply", "screen-call"]) {
    el[key].classList.toggle("hidden", key !== name);
  }
}

function setStatus(node, text, kind = "") {
  if (!node) return;
  node.textContent = text;
  node.dataset.kind = kind;
}

// ---------------------------------------------------------------------------
// Media
// ---------------------------------------------------------------------------

async function acquireMedia() {
  state.wantCamera = el["opt-camera"].checked;
  state.wantMic = el["opt-mic"].checked;
  if (!state.wantCamera && !state.wantMic) {
    return null; // text/files only
  }
  try {
    const stream = await navigator.mediaDevices.getUserMedia({
      video: state.wantCamera,
      audio: state.wantMic,
    });
    state.localStream = stream;
    return stream;
  } catch (err) {
    // Continue without media rather than dead-ending the whole call.
    setStatus(
      el["start-error"],
      `Couldn't access camera/mic (${err.name}). Continuing with text & files only.`,
      "warn",
    );
    return null;
  }
}

// ---------------------------------------------------------------------------
// Peer connection
// ---------------------------------------------------------------------------

function createPeerConnection() {
  const pc = new RTCPeerConnection({ iceServers: ICE_SERVERS });

  pc.addEventListener("track", (event) => {
    const [stream] = event.streams;
    if (stream) attachRemoteStream(stream);
  });

  pc.addEventListener("connectionstatechange", () => {
    const s = pc.connectionState;
    if (s === "connected") {
      enterCall();
    } else if (s === "failed") {
      setStatus(el["call-status"], "Connection failed. The network may need a TURN relay.", "error");
    } else if (s === "disconnected") {
      setStatus(el["call-status"], "Peer disconnected…", "warn");
    } else if (s === "closed") {
      setStatus(el["call-status"], "Call ended.", "warn");
    }
  });

  if (state.localStream) {
    for (const track of state.localStream.getTracks()) {
      pc.addTrack(track, state.localStream);
    }
  }
  return pc;
}

// Wait until ICE gathering finishes so the SDP we share already contains all
// candidates (non-trickle). A timeout guards browsers that never fire
// "complete".
function waitForIceGatheringComplete(pc, timeoutMs = ICE_GATHER_TIMEOUT_MS) {
  if (pc.iceGatheringState === "complete") return Promise.resolve();
  return new Promise((resolve) => {
    let settled = false;
    const finish = () => {
      if (settled) return;
      settled = true;
      pc.removeEventListener("icegatheringstatechange", check);
      resolve();
    };
    const check = () => {
      if (pc.iceGatheringState === "complete") finish();
    };
    pc.addEventListener("icegatheringstatechange", check);
    setTimeout(finish, timeoutMs);
  });
}

// ---------------------------------------------------------------------------
// Host flow: create an offer link, then accept the guest's reply.
// ---------------------------------------------------------------------------

async function startAsHost() {
  await acquireMedia();
  state.pc = createPeerConnection();

  const channel = state.pc.createDataChannel("webrtc", { ordered: true });
  setupChannel(channel);

  const offer = await state.pc.createOffer({
    offerToReceiveAudio: true,
    offerToReceiveVideo: true,
  });
  await state.pc.setLocalDescription(offer);
  await waitForIceGatheringComplete(state.pc);

  const link = await buildCompressedLink(window.location.href, state.pc.localDescription);
  el["invite-link"].value = link;
  showQr(el["invite-qr"], link, "Scan with a phone camera to join");
  // Offer to scan the guest's reply with the camera, where supported.
  if ("BarcodeDetector" in window) el["scan-reply"].classList.remove("hidden");
  attachLocalPreview();
  setStatus(el["invite-status"], "Waiting for a reply code…");
  showScreen("screen-invite");
}

async function acceptAnswer() {
  const token = extractToken(el["answer-input"].value);
  let answer = null;
  if (token) {
    try {
      answer = await decodeAnySignal(token);
    } catch {
      answer = null;
    }
  }
  if (!answer || answer.type !== "answer") {
    setStatus(el["invite-status"], "That doesn't look like a valid reply code.", "error");
    return;
  }
  try {
    await state.pc.setRemoteDescription({ type: "answer", sdp: answer.sdp });
    setStatus(el["invite-status"], "Reply accepted. Connecting…");
  } catch (err) {
    setStatus(el["invite-status"], `Could not apply reply: ${err.message}`, "error");
  }
}

// ---------------------------------------------------------------------------
// Guest flow: consume the offer from the link, produce a reply code.
// ---------------------------------------------------------------------------

async function startAsGuest(offer) {
  await acquireMedia();
  state.pc = createPeerConnection();
  state.pc.addEventListener("datachannel", (event) => setupChannel(event.channel));

  await state.pc.setRemoteDescription({ type: "offer", sdp: offer.sdp });
  const answer = await state.pc.createAnswer();
  await state.pc.setLocalDescription(answer);
  await waitForIceGatheringComplete(state.pc);

  const token = await encodeSignalCompressed(state.pc.localDescription);
  el["reply-code"].value = token;
  showQr(el["reply-qr"], token, "Or let them scan this");
  attachLocalPreview();
  setStatus(el["reply-status"], "Send this reply back, then keep this tab open…");
  showScreen("screen-reply");
}

// ---------------------------------------------------------------------------
// Data channel: chat + file transfer
// ---------------------------------------------------------------------------

function setupChannel(channel) {
  state.channel = channel;
  channel.binaryType = "arraybuffer";
  channel.bufferedAmountLowThreshold = BUFFER_LOW;

  channel.addEventListener("open", () => {
    setStatus(el["call-status"], "Connected — peer to peer.", "ok");
    el["chat-input"].disabled = false;
    el["chat-send"].disabled = false;
    el["file-input"].disabled = false;
  });
  channel.addEventListener("close", () => {
    setStatus(el["call-status"], "Channel closed.", "warn");
  });
  channel.addEventListener("message", (event) => handleChannelMessage(event.data));
}

function handleChannelMessage(data) {
  if (typeof data === "string") {
    let msg;
    try {
      msg = JSON.parse(data);
    } catch {
      return;
    }
    if (msg.kind === MESSAGE_KIND.chat) {
      addChatLine("them", msg.text);
    } else if (msg.kind === MESSAGE_KIND.fileMeta) {
      state.incoming = new FileAssembler(msg);
      renderIncomingFile(msg, 0);
    } else if (msg.kind === MESSAGE_KIND.fileEnd) {
      finalizeIncomingFile();
    }
    return;
  }
  // Binary: a file chunk for the file announced by the most recent meta.
  if (state.incoming) {
    const progress = state.incoming.addChunk(data);
    renderIncomingFile(state.incoming.meta, progress);
  }
}

function sendChat() {
  const text = el["chat-input"].value.trim();
  if (!text || !state.channel || state.channel.readyState !== "open") return;
  state.channel.send(JSON.stringify(createChatMessage(text)));
  addChatLine("me", text);
  el["chat-input"].value = "";
}

async function sendFiles(files) {
  if (!state.channel || state.channel.readyState !== "open") return;
  for (const file of files) {
    await sendOneFile(file);
  }
}

async function sendOneFile(file) {
  const channel = state.channel;
  const meta = createFileMeta(file);
  channel.send(JSON.stringify(meta));
  const row = renderOutgoingFile(meta);

  const ranges = chunkRanges(file.size);
  let sent = 0;
  for (const { start, end } of ranges) {
    const buffer = await file.slice(start, end).arrayBuffer();
    await waitForDrain(channel);
    channel.send(buffer);
    sent += end - start;
    updateFileRow(row, meta, sent / (file.size || 1));
  }
  channel.send(JSON.stringify(createFileEnd(meta.id)));
  updateFileRow(row, meta, 1, "sent");
}

function waitForDrain(channel) {
  if (channel.bufferedAmount < BUFFER_HIGH) return Promise.resolve();
  return new Promise((resolve) => {
    const onLow = () => {
      channel.removeEventListener("bufferedamountlow", onLow);
      resolve();
    };
    channel.addEventListener("bufferedamountlow", onLow);
  });
}

// ---------------------------------------------------------------------------
// Call UI
// ---------------------------------------------------------------------------

function attachLocalPreview() {
  if (state.localStream) {
    el["local-video"].srcObject = state.localStream;
  }
}

function attachRemoteStream(stream) {
  el["remote-video"].srcObject = stream;
  el["remote-placeholder"].classList.add("hidden");
}

function enterCall() {
  attachLocalPreview();
  const hasVideo = state.localStream && state.localStream.getVideoTracks().length > 0;
  const hasAudio = state.localStream && state.localStream.getAudioTracks().length > 0;
  el["toggle-cam"].disabled = !hasVideo;
  el["toggle-mic"].disabled = !hasAudio;
  showScreen("screen-call");
}

function toggleTrack(kind) {
  if (!state.localStream) return true;
  const tracks =
    kind === "video"
      ? state.localStream.getVideoTracks()
      : state.localStream.getAudioTracks();
  let enabled = true;
  for (const track of tracks) {
    track.enabled = !track.enabled;
    enabled = track.enabled;
  }
  return enabled;
}

function hangup() {
  if (state.channel) try { state.channel.close(); } catch {}
  if (state.pc) try { state.pc.close(); } catch {}
  if (state.localStream) {
    for (const t of state.localStream.getTracks()) t.stop();
  }
  // Return to a clean start screen for a fresh call.
  window.location.hash = "";
  window.location.reload();
}

// ---------------------------------------------------------------------------
// Rendering helpers
// ---------------------------------------------------------------------------

function addChatLine(who, text) {
  const line = document.createElement("div");
  line.className = `chat-line ${who}`;
  const label = document.createElement("span");
  label.className = "chat-who";
  label.textContent = who === "me" ? "You" : "Peer";
  const body = document.createElement("span");
  body.className = "chat-text";
  body.textContent = text;
  line.append(label, body);
  el["chat-log"].append(line);
  el["chat-log"].scrollTop = el["chat-log"].scrollHeight;
}

function fileRowId(meta, dir) {
  return `file-${dir}-${meta.id}`;
}

function renderOutgoingFile(meta) {
  return upsertFileRow(meta, "out", "sending");
}

function renderIncomingFile(meta, progress) {
  const row = upsertFileRow(meta, "in", "receiving");
  updateFileRow(row, meta, progress);
  return row;
}

function upsertFileRow(meta, dir, verb) {
  const id = fileRowId(meta, dir);
  let row = document.getElementById(id);
  if (!row) {
    row = document.createElement("div");
    row.id = id;
    row.className = "file-row";
    row.innerHTML = `
      <div class="file-head">
        <span class="file-arrow">${dir === "out" ? "↑" : "↓"}</span>
        <span class="file-name"></span>
        <span class="file-size"></span>
      </div>
      <progress max="1" value="0"></progress>
      <div class="file-note"></div>`;
    el["file-list"].prepend(row);
  }
  row.querySelector(".file-name").textContent = meta.name;
  row.querySelector(".file-size").textContent = formatBytes(meta.size);
  row.querySelector(".file-note").textContent = verb;
  return row;
}

function updateFileRow(row, meta, progress, doneVerb) {
  const bar = row.querySelector("progress");
  bar.value = Math.max(0, Math.min(1, progress));
  if (doneVerb) row.querySelector(".file-note").textContent = doneVerb;
}

function finalizeIncomingFile() {
  const assembler = state.incoming;
  if (!assembler) return;
  const meta = assembler.meta;
  const blob = assembler.toBlob();
  const url = URL.createObjectURL(blob);
  const row = document.getElementById(fileRowId(meta, "in"));
  if (row) {
    row.querySelector("progress").value = 1;
    const note = row.querySelector(".file-note");
    note.textContent = "";
    const link = document.createElement("a");
    link.href = url;
    link.download = meta.name;
    link.textContent = `Save ${meta.name}`;
    link.className = "file-download";
    note.append(link);
  }
  state.incoming = null;
}

// ---------------------------------------------------------------------------
// QR codes + camera scanning
// ---------------------------------------------------------------------------

function showQr(container, text, caption) {
  container.innerHTML = "";
  try {
    const canvas = renderToCanvas(text, { size: 360 });
    canvas.setAttribute("role", "img");
    canvas.setAttribute("alt", "QR code");
    container.append(canvas);
    if (caption) {
      const cap = document.createElement("p");
      cap.className = "qr-caption";
      cap.textContent = caption;
      container.append(cap);
    }
    container.classList.remove("hidden");
  } catch (err) {
    // Too much data for a QR (unusually large SDP) — fall back to the link.
    container.classList.add("hidden");
    if (!(err instanceof QrCapacityError)) throw err;
  }
}

function stopScanner() {
  if (state.scanStop) {
    state.scanStop();
    state.scanStop = null;
  }
  el["scanner"].classList.add("hidden");
}

async function startScanner(onResult) {
  if (!("BarcodeDetector" in window)) return;
  let stream;
  try {
    stream = await navigator.mediaDevices.getUserMedia({
      video: { facingMode: "environment" },
    });
  } catch {
    return; // no camera / denied
  }
  const detector = new window.BarcodeDetector({ formats: ["qr_code"] });
  const video = el["scan-video"];
  video.srcObject = stream;
  await video.play().catch(() => {});
  el["scanner"].classList.remove("hidden");

  let stopped = false;
  state.scanStop = () => {
    stopped = true;
    for (const t of stream.getTracks()) t.stop();
    video.srcObject = null;
  };

  const tick = async () => {
    if (stopped) return;
    try {
      const codes = await detector.detect(video);
      if (codes.length && codes[0].rawValue) {
        const value = codes[0].rawValue;
        stopScanner();
        onResult(value);
        return;
      }
    } catch {
      // transient detect errors are ignored; keep scanning
    }
    setTimeout(tick, 250);
  };
  tick();
}

// ---------------------------------------------------------------------------
// Wiring
// ---------------------------------------------------------------------------

async function copyToClipboard(text, button) {
  try {
    await navigator.clipboard.writeText(text);
    const original = button.textContent;
    button.textContent = "Copied!";
    setTimeout(() => {
      button.textContent = original;
    }, 1500);
  } catch {
    // Clipboard API may be unavailable; select the field so the user can copy.
  }
}

function bindEvents() {
  el["start-button"].addEventListener("click", async () => {
    el["start-button"].disabled = true;
    try {
      if (state.role === "guest") {
        await startAsGuest(state.pendingOffer);
      } else {
        await startAsHost();
      }
    } catch (err) {
      setStatus(el["start-error"], `Something went wrong: ${err.message}`, "error");
      el["start-button"].disabled = false;
    }
  });

  el["copy-invite"].addEventListener("click", () =>
    copyToClipboard(el["invite-link"].value, el["copy-invite"]),
  );
  el["copy-reply"].addEventListener("click", () =>
    copyToClipboard(el["reply-code"].value, el["copy-reply"]),
  );
  el["answer-connect"].addEventListener("click", acceptAnswer);

  el["scan-reply"].addEventListener("click", () =>
    startScanner((value) => {
      el["answer-input"].value = value;
      acceptAnswer();
    }),
  );
  el["scan-cancel"].addEventListener("click", stopScanner);

  el["chat-send"].addEventListener("click", sendChat);
  el["chat-input"].addEventListener("keydown", (e) => {
    if (e.key === "Enter" && !e.shiftKey) {
      e.preventDefault();
      sendChat();
    }
  });

  el["file-input"].addEventListener("change", async (e) => {
    const files = Array.from(e.target.files || []);
    e.target.value = "";
    await sendFiles(files);
  });

  el["toggle-cam"].addEventListener("click", () => {
    const on = toggleTrack("video");
    el["toggle-cam"].textContent = on ? "Camera on" : "Camera off";
    el["toggle-cam"].classList.toggle("off", !on);
  });
  el["toggle-mic"].addEventListener("click", () => {
    const on = toggleTrack("audio");
    el["toggle-mic"].textContent = on ? "Mic on" : "Mic off";
    el["toggle-mic"].classList.toggle("off", !on);
  });
  el["hangup"].addEventListener("click", hangup);
}

function init() {
  cacheElements();
  bindEvents();

  if (!("RTCPeerConnection" in window)) {
    setStatus(
      el["start-error"],
      "This browser doesn't support WebRTC, so this app can't run here.",
      "error",
    );
    el["start-button"].disabled = true;
    return;
  }

  showScreen("screen-start");

  const token = tokenFromUrl(window.location.href);
  if (!token) {
    state.role = "host";
    markReady();
    return;
  }

  // A token is present, so this is likely a join. Decoding may be async
  // (compressed links), so disable the button until the role is resolved.
  state.role = "host";
  el["start-button"].disabled = true;
  decodeAnySignal(token)
    .then((signal) => {
      if (signal && signal.type === "offer") {
        state.role = "guest";
        state.pendingOffer = signal;
        el["start-title"].textContent = "You've been invited to a chat";
        el["start-intro"].textContent =
          "Choose what to share, then join. You'll get a short reply code to send back to the person who invited you.";
        el["start-button"].textContent = "Join chat";
      }
    })
    .catch(() => {
      // Not a usable offer token; fall back to hosting.
    })
    .finally(() => {
      el["start-button"].disabled = false;
      markReady();
    });
}

function markReady() {
  // Signal that event handlers are wired up and the role is resolved
  // (used by e2e/smoke tests).
  document.body.dataset.webrtcReady = "1";
}

if (typeof document !== "undefined") {
  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
}

export { state };
