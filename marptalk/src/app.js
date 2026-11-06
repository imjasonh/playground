/**
 * Wires the page to the deck renderer, the narrator, and the player.
 */
import {browser as marpBrowser} from '../vendor/marp-browser.js';

import {deckDurationMs, parseDeck} from './deck.js';
import {DECKS, deckPath} from './decks.js';
import {Narrator} from './narrator.js';
import {Player} from './player.js';
import {pickVoice, voicesFor} from './voices.js';

const SPEEDS = [0.5, 0.75, 1, 1.25, 1.5, 1.75, 2];
const SETTINGS_KEY = 'marptalk:settings';
const UPLOAD = 'upload';
const MAX_UPLOAD_BYTES = 2 * 1024 * 1024;
const IDLE_MS = 2500;

const SCREEN_CSS = `
:host { display: block; width: 100%; height: 100%; }
div.marpit { width: 100%; height: 100%; }
div.marpit > svg { display: none; width: 100%; height: 100%; }
div.marpit > svg.active { display: block; }
`;

const $ = (id) => document.getElementById(id);
const els = {
  deck: $('deck'),
  open: $('open'),
  file: $('file'),
  stage: $('stage'),
  viewport: $('viewport'),
  screen: $('screen'),
  caption: $('caption'),
  status: $('status'),
  prev: $('prev'),
  play: $('play'),
  next: $('next'),
  counter: $('counter'),
  progress: $('progress'),
  speed: $('speed'),
  voice: $('voice'),
  captions: $('captions'),
  mute: $('mute'),
  fullscreen: $('fullscreen'),
  drop: $('drop'),
  meta: $('meta'),
  cues: $('cues'),
  noCues: $('no-cues'),
};

const settings = loadSettings();
const synth = globalThis.speechSynthesis ?? null;
const narrator = new Narrator();
narrator.rate = settings.rate;
narrator.setMuted(settings.muted);

const shadow = els.screen.attachShadow({mode: 'open'});
/** @type {?import('./deck.js').Deck} */
let deck = null;
/** @type {?Player} */
let player = null;
/** @type {!Array<!Element>} */
let slideEls = [];
let marpCleanup = null;
let upload = null;
let wakeLock = null;
let statusTimer = null;
let idleTimer = null;

function loadSettings() {
  const defaults = {rate: 1, voiceURI: '', captions: true, muted: false};
  try {
    const saved = JSON.parse(localStorage.getItem(SETTINGS_KEY) || '{}');
    const merged = {...defaults, ...saved};
    if (!SPEEDS.includes(merged.rate)) merged.rate = 1;
    return merged;
  } catch {
    return defaults;
  }
}

function saveSettings() {
  try {
    localStorage.setItem(SETTINGS_KEY, JSON.stringify(settings));
  } catch {
    // Private browsing can refuse storage; settings then last for the visit.
  }
}

/**
 * @param {string} message
 * @param {number=} ms How long to show it; 0 keeps it up.
 */
function showStatus(message, ms = 5000) {
  clearTimeout(statusTimer);
  els.status.textContent = message;
  els.status.classList.toggle('visible', Boolean(message));
  if (message && ms) statusTimer = setTimeout(() => showStatus(''), ms);
}

/**
 * Renders `markdown` and makes it the current deck.
 *
 * @param {string} markdown
 * @return {boolean} Whether the deck rendered.
 */
function loadDeck(markdown) {
  let next;
  try {
    next = parseDeck(markdown);
  } catch (e) {
    showStatus(`Couldn't render that deck: ${e.message}`, 0);
    return false;
  }
  if (!next.slides.length) {
    showStatus('That file has no slides.', 0);
    return false;
  }

  player?.dispose();
  marpCleanup?.();
  deck = next;
  narrator.lang = deck.lang;

  const style = document.createElement('style');
  style.textContent = `${deck.css}\n${SCREEN_CSS}`;
  const template = document.createElement('template');
  template.innerHTML = deck.html;
  shadow.replaceChildren(style, template.content);
  slideEls = Array.from(shadow.querySelectorAll('div.marpit > svg'));
  const box = slideEls[0]?.viewBox?.baseVal;
  const ratio = box?.width && box?.height ? box.width / box.height : 16 / 9;
  els.stage.style.setProperty('--ratio', String(ratio));
  marpCleanup = marpBrowser(shadow);

  player = new Player(deck, narrator);
  player.addEventListener('slide', (e) => showSlide(e.detail.index));
  player.addEventListener('cue', (e) => showCue(e.detail.index, e.detail.text));
  player.addEventListener('word', (e) => showWord(e.detail));
  player.addEventListener('state', (e) => showPlaying(e.detail.playing));
  player.addEventListener('finished', () => showCaption(''));

  document.title = `${deck.title} · Marptalk`;
  buildProgress();
  updateVoices();
  updateMeta();
  showPlaying(false);
  showStatus('');
  player.goTo(slideFromHash());
  return true;
}

/** @return {number} The 0-based slide index in the URL fragment. */
function slideFromHash() {
  const n = Number.parseInt(location.hash.slice(1), 10);
  return Number.isFinite(n) && n > 0 ? n - 1 : 0;
}

/**
 * @param {string} id
 * @param {{keepHash?: boolean}=} options
 */
async function loadBuiltIn(id, {keepHash = false} = {}) {
  const entry = DECKS.find((d) => d.id === id) ?? DECKS[0];
  els.deck.value = entry.id;
  const url = new URL(location.href);
  url.searchParams.set('deck', entry.id);
  if (!keepHash) url.hash = '';
  history.replaceState(null, '', url);
  try {
    const res = await fetch(deckPath(entry.id));
    if (!res.ok) throw new Error(`HTTP ${res.status}`);
    loadDeck(await res.text());
  } catch (e) {
    showStatus(`Couldn't load ${entry.title}: ${e.message}`, 0);
  }
}

/** @param {!File} file */
async function loadFile(file) {
  if (file.size > MAX_UPLOAD_BYTES) {
    showStatus(`${file.name} is larger than 2 MB.`, 0);
    return;
  }
  const markdown = await file.text();
  const url = new URL(location.href);
  url.searchParams.delete('deck');
  url.hash = '';
  history.replaceState(null, '', url);
  if (!loadDeck(markdown)) return;
  upload = {name: file.name, markdown};
  buildDeckPicker();
  els.deck.value = UPLOAD;
}

function buildDeckPicker() {
  const options = DECKS.map((d) => new Option(d.title, d.id));
  if (upload) options.push(new Option(upload.name, UPLOAD));
  els.deck.replaceChildren(...options);
}

function buildProgress() {
  const buttons = deck.slides.map((_, i) => {
    const b = document.createElement('button');
    b.type = 'button';
    b.setAttribute('aria-label', `Slide ${i + 1}`);
    b.addEventListener('click', () => player.goTo(i));
    return b;
  });
  els.progress.replaceChildren(...buttons);
}

/** @param {number} index */
function showSlide(index) {
  slideEls.forEach((el, i) => el.classList.toggle('active', i === index));
  els.counter.textContent = `${index + 1} / ${deck.slides.length}`;
  els.prev.disabled = index === 0;
  els.next.disabled = index === deck.slides.length - 1;
  Array.from(els.progress.children).forEach((b, i) => {
    b.classList.toggle('seen', i < index);
    if (i === index) {
      b.setAttribute('aria-current', 'step');
    } else {
      b.removeAttribute('aria-current');
    }
  });
  const hash = `#${index + 1}`;
  if (location.hash !== hash) history.replaceState(null, '', hash);
  showCaption('');
  buildCues(deck.slides[index].cues);
}

/** @param {!Array<string>} cues */
function buildCues(cues) {
  const items = cues.map((text, i) => {
    const li = document.createElement('li');
    const b = document.createElement('button');
    b.type = 'button';
    b.textContent = text;
    b.addEventListener('click', () => player.playCue(i));
    li.append(b);
    return li;
  });
  els.cues.replaceChildren(...items);
  els.cues.scrollTop = 0;
  els.noCues.hidden = cues.length > 0;
}

/**
 * @param {number} index
 * @param {string} text
 */
function showCue(index, text) {
  showCaption(text);
  Array.from(els.cues.children).forEach((li, i) => {
    li.classList.toggle('active', i === index);
    if (i !== index) return;
    const list = els.cues;
    const top = li.offsetTop - list.offsetTop;
    const bottom = top + li.offsetHeight;
    if (top < list.scrollTop || bottom > list.scrollTop + list.clientHeight) {
      list.scrollTop = top - list.clientHeight / 3;
    }
  });
}

/** @param {string} text */
function showCaption(text) {
  els.caption.replaceChildren(text);
  els.caption.dataset.text = text;
  els.caption.hidden = !text || !settings.captions;
}

/** @param {{charIndex: number, charLength: number}} detail */
function showWord({charIndex, charLength}) {
  const text = els.caption.dataset.text || '';
  let end = charIndex + (charLength || 0);
  if (!charLength) {
    const m = text.slice(charIndex).match(/^\S*/);
    end = charIndex + (m ? m[0].length : 0);
  }
  const said = document.createElement('span');
  said.className = 'said';
  said.textContent = text.slice(0, end);
  const rest = document.createElement('span');
  rest.className = 'rest';
  rest.textContent = text.slice(end);
  els.caption.replaceChildren(said, rest);
}

/** @param {boolean} playing */
function showPlaying(playing) {
  els.stage.classList.toggle('playing', playing);
  els.play.setAttribute('aria-label', playing ? 'Pause' : 'Play');
  if (playing) {
    requestWakeLock();
    pokeIdle();
  } else {
    wakeLock?.release().catch(() => {});
    wakeLock = null;
    els.stage.classList.remove('idle');
  }
}

async function requestWakeLock() {
  if (wakeLock || !navigator.wakeLock) return;
  try {
    wakeLock = await navigator.wakeLock.request('screen');
    wakeLock.addEventListener('release', () => (wakeLock = null));
  } catch {
    // The screen may still sleep; narration keeps going.
  }
}

function updateMeta() {
  if (!deck) return;
  const ms = deckDurationMs(deck, settings.rate);
  const minutes = Math.max(1, Math.round(ms / 60000));
  const count = deck.slides.length;
  els.meta.textContent =
    `${deck.title} · ${count} slide${count === 1 ? '' : 's'} · ` +
    `about ${minutes} min at ${settings.rate}×`;
}

function updateVoices() {
  if (!deck) return;
  if (!synth) {
    els.voice.replaceChildren(new Option('No speech in this browser', ''));
    els.voice.disabled = true;
    els.mute.disabled = true;
    showStatus("This browser can't speak. Subtitles advance on a timer.", 0);
    return;
  }
  const all = synth.getVoices();
  if (!all.length) {
    els.voice.replaceChildren(new Option('Default voice', ''));
    return;
  }
  const list = voicesFor(all, deck.lang);
  const chosen = pickVoice(all, deck.lang, settings.voiceURI);
  els.voice.replaceChildren(
    ...list.map((v) => new Option(`${v.name} (${v.lang})`, v.voiceURI)),
  );
  els.voice.disabled = false;
  if (chosen) els.voice.value = chosen.voiceURI;
  if (narrator.voice?.voiceURI !== chosen?.voiceURI) narrator.setVoice(chosen);
}

/** @param {number} rate */
function setRate(rate) {
  settings.rate = rate;
  saveSettings();
  els.speed.value = String(rate);
  player?.setRate(rate);
  if (!player) narrator.rate = rate;
  updateMeta();
}

/** @param {number} step */
function stepRate(step) {
  const i = SPEEDS.indexOf(settings.rate);
  const next = SPEEDS[Math.max(0, Math.min(SPEEDS.length - 1, i + step))];
  if (next !== settings.rate) {
    setRate(next);
    showStatus(`Speed ${next}×`, 1200);
  }
}

function toggleCaptions() {
  settings.captions = !settings.captions;
  saveSettings();
  els.captions.setAttribute('aria-pressed', String(settings.captions));
  showCaption(els.caption.dataset.text || '');
}

function toggleMute() {
  if (!synth) return;
  settings.muted = !settings.muted;
  saveSettings();
  showMuted();
  narrator.setMuted(settings.muted);
}

function showMuted() {
  const label = settings.muted ? 'Unmute voice' : 'Mute voice';
  els.mute.setAttribute('aria-pressed', String(settings.muted));
  els.mute.setAttribute('aria-label', label);
}

function toggleFullscreen() {
  if (document.fullscreenElement) {
    document.exitFullscreen();
  } else if (els.stage.requestFullscreen) {
    els.stage
      .requestFullscreen()
      .catch(() => els.stage.classList.toggle('expanded'));
  } else {
    els.stage.classList.toggle('expanded');
  }
}

function pokeIdle() {
  els.stage.classList.remove('idle');
  clearTimeout(idleTimer);
  idleTimer = setTimeout(() => {
    if (player?.playing) els.stage.classList.add('idle');
  }, IDLE_MS);
}

/** @param {!KeyboardEvent} e */
function onKey(e) {
  if (!player || e.altKey || e.ctrlKey || e.metaKey) return;
  const target = /** @type {!Element} */ (e.target);
  if (target.closest('select, input, textarea')) return;
  if (target.closest('button') && (e.key === ' ' || e.key === 'Enter')) return;
  const actions = {
    ' ': () => player.toggle(),
    k: () => player.toggle(),
    ArrowRight: () => player.next(),
    PageDown: () => player.next(),
    ArrowLeft: () => player.prev(),
    PageUp: () => player.prev(),
    Home: () => player.goTo(0),
    End: () => player.goTo(deck.slides.length - 1),
    '>': () => stepRate(1),
    '<': () => stepRate(-1),
    c: toggleCaptions,
    m: toggleMute,
    f: toggleFullscreen,
  };
  const action = actions[e.key.length === 1 ? e.key.toLowerCase() : e.key] ??
    actions[e.key];
  if (!action) return;
  e.preventDefault();
  action();
  pokeIdle();
}

function wire() {
  buildDeckPicker();
  els.speed.value = String(settings.rate);
  els.captions.setAttribute('aria-pressed', String(settings.captions));
  showMuted();

  els.deck.addEventListener('change', () => {
    if (els.deck.value === UPLOAD) {
      loadDeck(upload.markdown);
    } else {
      loadBuiltIn(els.deck.value);
    }
  });
  els.open.addEventListener('click', () => els.file.click());
  els.file.addEventListener('change', () => {
    const [file] = els.file.files;
    if (file) loadFile(file);
    els.file.value = '';
  });
  els.prev.addEventListener('click', () => player?.prev());
  els.next.addEventListener('click', () => player?.next());
  els.play.addEventListener('click', () => player?.toggle());
  els.speed.addEventListener('change', () => setRate(Number(els.speed.value)));
  els.voice.addEventListener('change', () => {
    const uri = els.voice.value;
    const voice = synth?.getVoices().find((v) => v.voiceURI === uri);
    settings.voiceURI = voice?.voiceURI ?? '';
    saveSettings();
    narrator.setVoice(voice ?? null);
  });
  els.captions.addEventListener('click', toggleCaptions);
  els.mute.addEventListener('click', toggleMute);
  els.fullscreen.addEventListener('click', toggleFullscreen);
  els.viewport.addEventListener('click', (e) => {
    const onLink = e
      .composedPath()
      .some((n) => n instanceof Element && n.closest('a'));
    if (!onLink) player?.toggle();
  });
  els.stage.addEventListener('pointermove', pokeIdle);
  document.addEventListener('keydown', onKey);
  document.addEventListener('fullscreenchange', () => {
    const full = Boolean(document.fullscreenElement);
    els.stage.classList.toggle('fullscreen', full);
  });
  window.addEventListener('hashchange', () => {
    const index = slideFromHash();
    if (player && index !== player.index) player.goTo(index);
  });

  const reported = new Set();
  narrator.addEventListener('speecherror', (e) => {
    if (reported.has(e.detail.error)) return;
    reported.add(e.detail.error);
    showStatus(
      `Speech failed (${e.detail.error}). Subtitles advance on a timer.`,
    );
  });
  synth?.addEventListener?.('voiceschanged', updateVoices);

  let dragDepth = 0;
  document.addEventListener('dragenter', (e) => {
    if (!e.dataTransfer?.types.includes('Files')) return;
    dragDepth++;
    els.drop.hidden = false;
  });
  document.addEventListener('dragleave', () => {
    dragDepth = Math.max(0, dragDepth - 1);
    if (!dragDepth) els.drop.hidden = true;
  });
  document.addEventListener('dragover', (e) => e.preventDefault());
  document.addEventListener('drop', (e) => {
    e.preventDefault();
    dragDepth = 0;
    els.drop.hidden = true;
    const file = e.dataTransfer?.files?.[0];
    if (file) loadFile(file);
  });
  window.addEventListener('pagehide', () => narrator.stop());
}

wire();
const params = new URLSearchParams(location.search);
loadBuiltIn(params.get('deck') ?? DECKS[0].id, {keepHash: true});
