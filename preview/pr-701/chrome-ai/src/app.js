import {
  CHAT_OPTIONS,
  availabilityMessage,
  contextUsage,
  createSession,
  findLanguageModel,
  formatProgress,
  streamReply,
} from './model.js';
import {renderMarkdown} from './markdown.js';

const el = {
  log: document.querySelector('#log'),
  empty: document.querySelector('#empty'),
  messages: document.querySelector('#messages'),
  status: document.querySelector('#status'),
  download: document.querySelector('#download'),
  composer: document.querySelector('#composer'),
  prompt: document.querySelector('#prompt'),
  send: document.querySelector('#send'),
  stop: document.querySelector('#stop'),
  newChat: document.querySelector('#new-chat'),
};

const api = findLanguageModel(globalThis);

let session = null;
let controller = null;
let ready = false;
let overflowed = false;

const sessionCallbacks = {
  onProgress: (loaded) => setStatus(formatProgress(loaded)),
  onOverflow: () => {
    overflowed = true;
  },
};

function setStatus(text, {error = false} = {}) {
  el.status.textContent = text;
  el.status.classList.toggle('is-error', error);
}

function showUsage() {
  const usage = session ? contextUsage(session) : '';
  const note = overflowed
    ? 'The oldest messages no longer fit, so the model dropped them.'
    : '';
  setStatus([note, usage].filter(Boolean).join(' '));
}

function setReady(isReady) {
  ready = isReady;
  el.composer.hidden = !isReady;
  el.prompt.disabled = !isReady;
  updateSend();
}

function updateSend() {
  const busy = controller !== null;
  el.send.hidden = busy;
  el.stop.hidden = !busy;
  el.send.disabled = !ready || busy || el.prompt.value.trim() === '';
  el.newChat.disabled = el.messages.childElementCount === 0;
}

function applyAvailability(status) {
  setStatus(availabilityMessage(status));
  el.download.hidden = status !== 'downloadable' && status !== 'downloading';
  setReady(status === 'available');
}

function isNearBottom() {
  const {scrollHeight, scrollTop, clientHeight} = el.log;
  return scrollHeight - scrollTop - clientHeight < 48;
}

function scrollToBottom() {
  el.log.scrollTop = el.log.scrollHeight;
}

function addMessage(role, text) {
  const item = document.createElement('li');
  item.className = `message from-${role}`;
  const label = document.createElement('span');
  label.className = 'visually-hidden';
  label.textContent = role === 'user' ? 'You said:' : 'Model said:';
  const body = document.createElement('div');
  body.className = 'body';
  body.textContent = text;
  item.append(label, body);
  el.messages.append(item);
  el.empty.hidden = true;
  scrollToBottom();
  return body;
}

function describeError(err) {
  if (err?.name === 'QuotaExceededError') {
    return "That message is too long for the model's context window.";
  }
  if (err?.name === 'NotAllowedError') {
    return 'Chrome blocked the model. Click Send again to retry.';
  }
  return `The model failed: ${err?.message || err}`;
}

async function send(text) {
  controller = new AbortController();
  const {signal} = controller;
  addMessage('user', text);
  const reply = addMessage('model', '');
  reply.parentElement.classList.add('is-pending');
  updateSend();
  try {
    if (!session) {
      const created = await createSession(api, sessionCallbacks);
      if (signal.aborted) {
        created.destroy();
        return;
      }
      session = created;
    }
    await streamReply(session, text, {
      signal,
      onText: (sofar) => {
        const follow = isNearBottom();
        renderMarkdown(reply, sofar);
        if (follow) {
          scrollToBottom();
        }
      },
    });
  } catch (err) {
    if (err?.name !== 'AbortError') {
      reply.textContent = describeError(err);
      reply.parentElement.classList.add('is-error');
    }
  } finally {
    reply.parentElement.classList.remove('is-pending');
    if (signal.aborted && reply.textContent === '') {
      reply.parentElement.remove();
    }
    if (controller?.signal === signal) {
      controller = null;
    }
    updateSend();
    showUsage();
  }
}

function newChat() {
  controller?.abort();
  controller = null;
  session?.destroy();
  session = null;
  overflowed = false;
  el.messages.replaceChildren();
  el.empty.hidden = false;
  setStatus('');
  updateSend();
  el.prompt.focus();
}

async function download() {
  el.download.disabled = true;
  setStatus(formatProgress(0));
  try {
    session = await createSession(api, sessionCallbacks);
    el.download.hidden = true;
    setReady(true);
    showUsage();
    el.prompt.focus();
  } catch (err) {
    setStatus(describeError(err), {error: true});
  } finally {
    el.download.disabled = false;
  }
}

el.composer.addEventListener('submit', (e) => {
  e.preventDefault();
  const text = el.prompt.value.trim();
  if (!ready || controller || text === '') {
    return;
  }
  el.prompt.value = '';
  send(text);
});

el.prompt.addEventListener('keydown', (e) => {
  if (e.key === 'Enter' && !e.shiftKey && !e.isComposing) {
    e.preventDefault();
    el.composer.requestSubmit();
  }
});

el.prompt.addEventListener('input', updateSend);
el.stop.addEventListener('click', () => controller?.abort());
el.newChat.addEventListener('click', newChat);
el.download.addEventListener('click', download);

async function init() {
  if (!api) {
    applyAvailability('unsupported');
    return;
  }
  try {
    applyAvailability(await api.availability(CHAT_OPTIONS));
  } catch (err) {
    applyAvailability('unavailable');
    setStatus(describeError(err), {error: true});
  }
}

init();
