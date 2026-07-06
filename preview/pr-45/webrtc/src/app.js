// WebRTC — serverless, link-based peer-to-peer app with audio, video, files,
// live location sharing, payment requests, and speech-to-text captions.
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
import {
  LOCATION_KIND,
  LOCATION_STOP_KIND,
  createLocationMessage,
  createLocationStop,
  parseLocationMessage,
  formatCoords,
  formatAccuracy,
  mapsLink,
} from "./location.js";
import {
  PAYMENT_REQUEST_KIND,
  PAYMENT_RESULT_KIND,
  createPaymentRequestMessage,
  parsePaymentRequestMessage,
  createPaymentResultMessage,
  parsePaymentResultMessage,
  formatAmount,
  buildPaymentMethodData,
  buildPaymentDetails,
} from "./payments.js";
import {
  CAPTION_KIND,
  createCaptionMessage,
  parseCaptionMessage,
  getSpeechRecognition,
  isSpeechRecognitionSupported,
  collectTranscript,
} from "./captions.js";

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
  watchId: null, // geolocation watch id while sharing live location
  screenStream: null, // active getDisplayMedia stream
  cameraTrack: null, // camera track parked while screen sharing
  recognition: null, // active SpeechRecognition for captions
  captionsOn: false,
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
    "share-invite",
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
    "remote-caption",
    "local-caption",
    "toggle-cam",
    "toggle-mic",
    "share-screen",
    "toggle-captions",
    "hangup",
    "call-status",
    "chat-log",
    "chat-input",
    "chat-send",
    "file-input",
    "file-list",
    "share-location",
    "toggle-live-location",
    "request-money",
    "perm-hint",
    "pay-form",
    "pay-amount",
    "pay-currency",
    "pay-note",
    "extras-log",
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
  // Offer the native share sheet (Web Share API) where available.
  if (typeof navigator !== "undefined" && typeof navigator.share === "function") {
    el["share-invite"].classList.remove("hidden");
  }
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
    if (el["toggle-captions"]) {
      el["toggle-captions"].disabled = !isSpeechRecognitionSupported(window);
    }
    enableExtras(true);
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
    } else if (msg.kind === LOCATION_KIND) {
      const loc = parseLocationMessage(msg);
      if (loc) renderLocation("them", loc);
    } else if (msg.kind === LOCATION_STOP_KIND) {
      renderExtraNote("Peer stopped sharing live location.");
    } else if (msg.kind === PAYMENT_REQUEST_KIND) {
      const req = parsePaymentRequestMessage(msg);
      if (req) renderIncomingPaymentRequest(req);
    } else if (msg.kind === PAYMENT_RESULT_KIND) {
      const result = parsePaymentResultMessage(msg);
      if (result) applyPaymentResult(result);
    } else if (msg.kind === CAPTION_KIND) {
      const cap = parseCaptionMessage(msg);
      if (cap) updateCaption(el["remote-caption"], cap.text, cap.final);
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
  stopLiveLocation();
  stopCaptions();
  if (state.screenStream) {
    for (const t of state.screenStream.getTracks()) t.stop();
    state.screenStream = null;
  }
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
// Extras: enable/disable, location sharing, screen share, payments
// ---------------------------------------------------------------------------

function enableExtras(on) {
  const ids = ["share-location", "toggle-live-location", "request-money", "share-screen"];
  for (const id of ids) {
    if (el[id]) el[id].disabled = !on;
  }
  // getDisplayMedia isn't available everywhere (notably most mobile browsers).
  const canScreenShare =
    typeof navigator !== "undefined" &&
    navigator.mediaDevices &&
    typeof navigator.mediaDevices.getDisplayMedia === "function";
  if (el["share-screen"]) el["share-screen"].disabled = !on || !canScreenShare;
  if (on) reflectGeolocationPermission();
}

// Reflect the current Geolocation permission in the hint text via the
// Permissions API, where supported. Purely informational — the actual prompt
// still happens on first use.
async function reflectGeolocationPermission() {
  if (!el["perm-hint"]) return;
  if (!("geolocation" in navigator)) {
    el["perm-hint"].textContent = "Geolocation isn't supported in this browser.";
    return;
  }
  if (!navigator.permissions || typeof navigator.permissions.query !== "function") {
    el["perm-hint"].textContent = "Your browser will ask permission before sharing location.";
    return;
  }
  try {
    const status = await navigator.permissions.query({ name: "geolocation" });
    const describe = () => {
      const map = {
        granted: "Location permission granted.",
        prompt: "Your browser will ask permission before sharing location.",
        denied: "Location permission is blocked — enable it in site settings to share.",
      };
      el["perm-hint"].textContent = map[status.state] || "";
    };
    describe();
    status.addEventListener("change", describe);
  } catch {
    el["perm-hint"].textContent = "";
  }
}

function getPosition(options) {
  return new Promise((resolve, reject) => {
    navigator.geolocation.getCurrentPosition(resolve, reject, options);
  });
}

async function shareLocationOnce() {
  if (!("geolocation" in navigator)) {
    renderExtraNote("Geolocation isn't supported here.", "error");
    return;
  }
  if (!channelOpen()) return;
  el["share-location"].disabled = true;
  try {
    const position = await getPosition({ enableHighAccuracy: true, timeout: 10000 });
    const msg = createLocationMessage(position, { live: false });
    state.channel.send(JSON.stringify(msg));
    renderLocation("me", parseLocationMessage(msg));
  } catch (err) {
    renderExtraNote(`Couldn't get your location (${err.message || err.code}).`, "error");
  } finally {
    el["share-location"].disabled = !channelOpen();
    reflectGeolocationPermission();
  }
}

function toggleLiveLocation() {
  if (state.watchId != null) {
    stopLiveLocation();
    if (channelOpen()) state.channel.send(JSON.stringify(createLocationStop()));
    return;
  }
  if (!("geolocation" in navigator) || !channelOpen()) return;
  state.watchId = navigator.geolocation.watchPosition(
    (position) => {
      const msg = createLocationMessage(position, { live: true });
      if (channelOpen()) state.channel.send(JSON.stringify(msg));
      renderLocation("me", parseLocationMessage(msg));
    },
    (err) => {
      renderExtraNote(`Live location error (${err.message || err.code}).`, "error");
      stopLiveLocation();
    },
    { enableHighAccuracy: true, maximumAge: 5000, timeout: 15000 },
  );
  setLiveLocationButton(true);
  reflectGeolocationPermission();
}

function stopLiveLocation() {
  if (state.watchId != null) {
    navigator.geolocation.clearWatch(state.watchId);
    state.watchId = null;
  }
  setLiveLocationButton(false);
}

function setLiveLocationButton(on) {
  const btn = el["toggle-live-location"];
  if (!btn) return;
  btn.textContent = on ? "Live location on" : "Live location off";
  btn.classList.toggle("off", !on);
}

async function shareScreen() {
  if (!navigator.mediaDevices || typeof navigator.mediaDevices.getDisplayMedia !== "function") {
    renderExtraNote("Screen sharing isn't supported in this browser.", "error");
    return;
  }
  // Screen share swaps the outgoing camera track via replaceTrack, which needs
  // no renegotiation. Our one-shot serverless signaling can't add brand-new
  // media mid-call, so an existing outgoing video track is required.
  const sender =
    state.pc &&
    state.pc.getSenders().find((s) => s.track && s.track.kind === "video");
  if (!sender) {
    renderExtraNote(
      "Start the call with your camera on to share your screen — serverless signaling can't add new video mid-call.",
      "warn",
    );
    return;
  }
  try {
    const display = await navigator.mediaDevices.getDisplayMedia({ video: true });
    const screenTrack = display.getVideoTracks()[0];
    state.screenStream = display;
    state.cameraTrack = state.cameraTrack || sender.track;
    await sender.replaceTrack(screenTrack);
    el["local-video"].srcObject = display;
    setScreenShareButton(true);
    // Restore the camera when the user stops sharing from the browser UI.
    screenTrack.addEventListener("ended", () => stopScreenShare());
  } catch (err) {
    if (err && err.name !== "NotAllowedError") {
      renderExtraNote(`Couldn't share screen (${err.name || err.message}).`, "error");
    }
  }
}

async function stopScreenShare() {
  if (!state.screenStream) return;
  for (const t of state.screenStream.getTracks()) t.stop();
  state.screenStream = null;
  const sender =
    state.pc &&
    state.pc.getSenders().find((s) => s.track && s.track.kind === "video");
  if (sender && state.cameraTrack) {
    try {
      await sender.replaceTrack(state.cameraTrack);
    } catch {
      // ignore — camera may have been stopped
    }
  }
  state.cameraTrack = null;
  attachLocalPreview();
  setScreenShareButton(false);
}

function setScreenShareButton(on) {
  const btn = el["share-screen"];
  if (!btn) return;
  btn.textContent = on ? "Stop sharing screen" : "Share screen";
  btn.classList.toggle("off", on);
}

function toggleScreenShare() {
  if (state.screenStream) {
    stopScreenShare();
  } else {
    shareScreen();
  }
}

function sendPaymentRequest() {
  if (!channelOpen()) return;
  let msg;
  try {
    msg = createPaymentRequestMessage({
      amount: el["pay-amount"].value,
      currency: el["pay-currency"].value || "USD",
      note: el["pay-note"].value,
    });
  } catch (err) {
    renderExtraNote(`Invalid request: ${err.message}`, "error");
    return;
  }
  state.channel.send(JSON.stringify(msg));
  renderOutgoingPaymentRequest(msg);
  el["pay-form"].classList.add("hidden");
  el["pay-amount"].value = "";
  el["pay-note"].value = "";
}

// The payer's side: launch the Web Payments UI for an incoming request.
async function payViaWebPayments(req, cardEl) {
  const statusEl = cardEl.querySelector(".extra-status");
  const payBtn = cardEl.querySelector("button");
  const report = (status, detail, kind) => {
    if (channelOpen()) {
      state.channel.send(JSON.stringify(createPaymentResultMessage(req.id, status, detail)));
    }
    if (statusEl) {
      statusEl.textContent = detail;
      statusEl.className = `extra-status ${kind || ""}`;
    }
  };

  if (typeof window.PaymentRequest !== "function") {
    report("unsupported", "Web Payments isn't supported in this browser.", "warn");
    return;
  }
  if (payBtn) payBtn.disabled = true;

  try {
    const request = new window.PaymentRequest(
      buildPaymentMethodData(),
      buildPaymentDetails(req),
    );
    // Not all browsers expose canMakePayment; treat missing as "try anyway".
    if (typeof request.canMakePayment === "function") {
      const ok = await request.canMakePayment().catch(() => null);
      if (ok === false) {
        report(
          "unsupported",
          "No payment app is available to complete this on your device.",
          "warn",
        );
        if (payBtn) payBtn.disabled = false;
        return;
      }
    }
    const response = await request.show();
    await response.complete("success");
    report("paid", "Paid — thanks!", "ok");
  } catch (err) {
    if (err && err.name === "AbortError") {
      report("declined", "Payment cancelled.", "warn");
    } else {
      report("failed", `Payment failed (${(err && err.name) || err}).`, "error");
    }
    if (payBtn) payBtn.disabled = false;
  }
}

function channelOpen() {
  return state.channel && state.channel.readyState === "open";
}

async function shareInvite() {
  const url = el["invite-link"].value;
  if (!url) return;
  try {
    await navigator.share({
      title: "Join my private WebRTC call",
      text: "Open this link to start a direct, serverless peer-to-peer session:",
      url,
    });
  } catch {
    // User dismissed the share sheet, or sharing is unavailable — no-op.
  }
}

// --- Live captions (Web Speech API) ---

function toggleCaptions() {
  if (state.captionsOn) stopCaptions();
  else startCaptions();
}

function startCaptions() {
  const Recognition = getSpeechRecognition(window);
  if (!Recognition) {
    renderExtraNote(
      "Live captions need the Web Speech API (try Chrome or Edge).",
      "warn",
    );
    return;
  }
  const rec = new Recognition();
  rec.continuous = true;
  rec.interimResults = true;
  rec.lang = (typeof navigator !== "undefined" && navigator.language) || "en-US";

  rec.addEventListener("result", (event) => {
    const { interim, final } = collectTranscript(event.results, event.resultIndex);
    // Show my own words locally and stream them to the peer. Recognition only
    // hears my mic, so the peer relies on these messages for my captions.
    if (final) {
      updateCaption(el["local-caption"], final, true);
      sendCaption(final, true);
    } else if (interim) {
      updateCaption(el["local-caption"], interim, false);
      sendCaption(interim, false);
    }
  });

  rec.addEventListener("error", (event) => {
    if (event.error === "not-allowed" || event.error === "service-not-allowed") {
      renderExtraNote("Microphone permission is required for captions.", "error");
      stopCaptions();
    }
    // Transient errors (e.g. "no-speech", "aborted") are ignored; the "end"
    // handler restarts recognition while captions stay on.
  });

  rec.addEventListener("end", () => {
    // Recognition ends itself after pauses; keep it going while enabled.
    if (state.captionsOn && state.recognition === rec) {
      try {
        rec.start();
      } catch {
        // start() throws if it's already running — safe to ignore.
      }
    }
  });

  state.recognition = rec;
  state.captionsOn = true;
  setCaptionButton(true);
  try {
    rec.start();
  } catch {
    // Ignore: a rapid toggle can leave it mid-start.
  }
}

function stopCaptions() {
  state.captionsOn = false;
  if (state.recognition) {
    try {
      state.recognition.stop();
    } catch {
      // ignore
    }
    state.recognition = null;
  }
  updateCaption(el["local-caption"], "", true);
  setCaptionButton(false);
}

function setCaptionButton(on) {
  const btn = el["toggle-captions"];
  if (!btn) return;
  btn.textContent = on ? "Captions on" : "Captions off";
  btn.classList.toggle("active", on);
}

function sendCaption(text, final) {
  if (!channelOpen()) return;
  try {
    state.channel.send(JSON.stringify(createCaptionMessage(text, final)));
  } catch {
    // Channel may have closed between the check and the send — ignore.
  }
}

// Show a caption line, replacing any interim text. Final lines linger briefly
// then clear so the overlay doesn't hold stale text.
function updateCaption(node, text, final) {
  if (!node) return;
  clearTimeout(node._captionTimer);
  node.textContent = text || "";
  node.classList.toggle("hidden", !text);
  if (final && text) {
    node._captionTimer = setTimeout(() => {
      node.textContent = "";
      node.classList.add("hidden");
    }, 4000);
  }
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

// --- Extras feed (location + payments) ---

function extraCard(who) {
  const card = document.createElement("div");
  card.className = `extra-card ${who === "me" ? "me" : "them"}`;
  el["extras-log"].prepend(card);
  return card;
}

function whoLabel(who) {
  const span = document.createElement("span");
  span.className = "extra-who";
  span.textContent = who === "me" ? "You" : "Peer";
  return span;
}

function renderExtraNote(text, kind = "") {
  const card = extraCard("them");
  const body = document.createElement("div");
  body.className = `extra-body extra-status ${kind}`;
  body.textContent = text;
  card.append(body);
}

function renderLocation(who, loc) {
  if (!loc) return;
  const card = extraCard(who);
  const head = document.createElement("div");
  head.className = "extra-head";
  head.append(whoLabel(who));
  const label = document.createElement("span");
  label.className = "extra-body";
  label.textContent = "📍 Location";
  head.append(label);
  if (loc.live) {
    const badge = document.createElement("span");
    badge.className = "extra-badge live";
    badge.textContent = "Live";
    head.append(badge);
  }
  card.append(head);

  const link = document.createElement("a");
  link.className = "extra-link";
  link.href = mapsLink(loc.lat, loc.lon);
  link.target = "_blank";
  link.rel = "noopener noreferrer";
  link.textContent = formatCoords(loc.lat, loc.lon);
  const body = document.createElement("div");
  body.className = "extra-body";
  body.append(link);
  card.append(body);

  const bits = [];
  if (Number.isFinite(loc.accuracy)) bits.push(`accuracy ${formatAccuracy(loc.accuracy)}`);
  if (loc.ts) bits.push(new Date(loc.ts).toLocaleTimeString());
  if (bits.length) {
    const sub = document.createElement("div");
    sub.className = "extra-sub";
    sub.textContent = bits.join(" · ");
    card.append(sub);
  }
}

function paymentCardId(id) {
  return `pay-${id}`;
}

function renderOutgoingPaymentRequest(msg) {
  const card = extraCard("me");
  card.id = paymentCardId(msg.id);
  const head = document.createElement("div");
  head.className = "extra-head";
  head.append(whoLabel("me"));
  const label = document.createElement("span");
  label.className = "extra-body";
  label.textContent = `💸 Requested ${formatAmount(msg.amount, msg.currency)}`;
  head.append(label);
  card.append(head);
  if (msg.note) {
    const sub = document.createElement("div");
    sub.className = "extra-sub";
    sub.textContent = msg.note;
    card.append(sub);
  }
  const status = document.createElement("div");
  status.className = "extra-status";
  status.textContent = "Waiting for peer to pay…";
  card.append(status);
}

function renderIncomingPaymentRequest(req) {
  const card = extraCard("them");
  card.id = paymentCardId(req.id);
  const head = document.createElement("div");
  head.className = "extra-head";
  head.append(whoLabel("them"));
  const label = document.createElement("span");
  label.className = "extra-body";
  label.textContent = `💸 Requests ${formatAmount(req.amount, req.currency)}`;
  head.append(label);
  card.append(head);
  if (req.note) {
    const sub = document.createElement("div");
    sub.className = "extra-sub";
    sub.textContent = req.note;
    card.append(sub);
  }
  const actions = document.createElement("div");
  actions.className = "extra-actions";
  const payBtn = document.createElement("button");
  payBtn.type = "button";
  payBtn.className = "primary";
  payBtn.textContent = `Pay ${formatAmount(req.amount, req.currency)}`;
  payBtn.addEventListener("click", () => payViaWebPayments(req, card));
  const status = document.createElement("span");
  status.className = "extra-status";
  actions.append(payBtn, status);
  card.append(actions);
}

function applyPaymentResult(result) {
  const card = document.getElementById(paymentCardId(result.id));
  if (!card) return;
  let status = card.querySelector(".extra-status");
  if (!status) {
    status = document.createElement("div");
    status.className = "extra-status";
    card.append(status);
  }
  const map = {
    paid: ["Peer paid this request.", "ok"],
    declined: ["Peer cancelled the payment.", "warn"],
    unsupported: ["Peer's browser can't complete Web Payments.", "warn"],
    failed: ["Payment failed on the peer's device.", "error"],
  };
  const [text, kind] = map[result.status] || ["Payment update.", ""];
  status.textContent = result.detail ? `${text} (${result.detail})` : text;
  status.className = `extra-status ${kind}`;
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
  el["share-invite"].addEventListener("click", shareInvite);
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

  // Extras: screen share, captions, location sharing, and payment requests.
  el["share-screen"].addEventListener("click", toggleScreenShare);
  el["toggle-captions"].addEventListener("click", toggleCaptions);
  el["share-location"].addEventListener("click", shareLocationOnce);
  el["toggle-live-location"].addEventListener("click", toggleLiveLocation);
  el["request-money"].addEventListener("click", () => {
    el["pay-form"].classList.toggle("hidden");
    if (!el["pay-form"].classList.contains("hidden")) el["pay-amount"].focus();
  });
  el["pay-form"].addEventListener("submit", (e) => {
    e.preventDefault();
    sendPaymentRequest();
  });
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
