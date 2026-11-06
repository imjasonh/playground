import {acceptList, buildPrompt, checkFile} from './attachments.js';
import {renderMarkdown} from './markdown.js';
import {
  availabilityMessage,
  chatOptions,
  contextUsage,
  createSession,
  findLanguageModel,
  formatProgress,
  streamReply,
  supportedMedia,
} from './model.js';

const el = {
  app: document.querySelector('.app'),
  log: document.querySelector('#log'),
  empty: document.querySelector('#empty'),
  messages: document.querySelector('#messages'),
  status: document.querySelector('#status'),
  download: document.querySelector('#download'),
  attachments: document.querySelector('#attachments'),
  composer: document.querySelector('#composer'),
  attach: document.querySelector('#attach'),
  fileInput: document.querySelector('#file-input'),
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
let media = [];
let pending = [];
const sentUrls = [];

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
  el.attach.disabled = !isReady;
  updateSend();
}

function updateSend() {
  const busy = controller !== null;
  const empty = el.prompt.value.trim() === '' && pending.length === 0;
  el.send.hidden = busy;
  el.stop.hidden = !busy;
  el.send.disabled = !ready || busy || empty;
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

function attachmentElement(attachment, {onRemove} = {}) {
  const item = document.createElement('li');
  item.className = `attachment is-${attachment.kind}`;
  if (attachment.kind === 'image') {
    const img = document.createElement('img');
    img.src = attachment.url;
    img.alt = attachment.name;
    item.append(img);
  } else if (attachment.kind === 'audio' && !onRemove) {
    const audio = document.createElement('audio');
    audio.controls = true;
    audio.src = attachment.url;
    audio.setAttribute('aria-label', attachment.name);
    item.append(audio);
  } else {
    const name = document.createElement('span');
    name.className = 'name';
    name.textContent = attachment.name;
    item.append(name);
  }
  if (onRemove) {
    const remove = document.createElement('button');
    remove.type = 'button';
    remove.className = 'remove';
    remove.textContent = '×';
    remove.setAttribute('aria-label', `Remove ${attachment.name}`);
    remove.addEventListener('click', onRemove);
    item.append(remove);
  }
  return item;
}

function renderPending() {
  el.attachments.replaceChildren(
    ...pending.map((attachment) =>
      attachmentElement(attachment, {
        onRemove: () => {
          if (attachment.url) {
            URL.revokeObjectURL(attachment.url);
          }
          pending = pending.filter((a) => a !== attachment);
          renderPending();
          el.prompt.focus();
        },
      }),
    ),
  );
  el.attachments.hidden = pending.length === 0;
  updateSend();
}

async function addFiles(files) {
  const errors = [];
  for (const file of files) {
    const check = checkFile(file, media);
    if (check.error) {
      errors.push(check.error);
      continue;
    }
    const attachment = {kind: check.kind, name: file.name, file, text: null};
    if (check.kind === 'text') {
      attachment.text = await file.text();
    } else {
      attachment.url = URL.createObjectURL(file);
    }
    pending.push(attachment);
  }
  renderPending();
  if (errors.length > 0) {
    setStatus(errors.join(' '), {error: true});
  }
}

function addMessage(role, text, attachments = []) {
  const item = document.createElement('li');
  item.className = `message from-${role}`;
  const label = document.createElement('span');
  label.className = 'visually-hidden';
  label.textContent = role === 'user' ? 'You said:' : 'Model said:';
  item.append(label);
  if (attachments.length > 0) {
    const list = document.createElement('ul');
    list.className = 'attachments';
    list.append(...attachments.map((a) => attachmentElement(a)));
    item.append(list);
  }
  const body = document.createElement('div');
  body.className = 'body';
  body.textContent = text;
  item.append(body);
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
  if (err?.name === 'EncodingError') {
    return "The model couldn't decode one of the attachments.";
  }
  return `The model failed: ${err?.message || err}`;
}

async function send(text, attachments) {
  controller = new AbortController();
  const {signal} = controller;
  addMessage('user', text, attachments);
  const reply = addMessage('model', '');
  reply.parentElement.classList.add('is-pending');
  updateSend();
  try {
    if (!session) {
      const created = await createSession(api, {...sessionCallbacks, media});
      if (signal.aborted) {
        created.destroy();
        return;
      }
      session = created;
    }
    await streamReply(session, buildPrompt(text, attachments), {
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
  for (const url of sentUrls.splice(0)) {
    URL.revokeObjectURL(url);
  }
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
    session = await createSession(api, {...sessionCallbacks, media});
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
  if (!ready || controller || (text === '' && pending.length === 0)) {
    return;
  }
  const attachments = pending;
  pending = [];
  sentUrls.push(...attachments.map((a) => a.url).filter(Boolean));
  el.prompt.value = '';
  renderPending();
  send(text, attachments);
});

el.prompt.addEventListener('keydown', (e) => {
  if (e.key === 'Enter' && !e.shiftKey && !e.isComposing) {
    e.preventDefault();
    el.composer.requestSubmit();
  }
});

el.prompt.addEventListener('paste', (e) => {
  const files = [...(e.clipboardData?.files ?? [])];
  if (ready && files.length > 0) {
    e.preventDefault();
    addFiles(files);
  }
});

// Dropping a file anywhere else would navigate the tab to it, so every file
// drag is handled here, even before the model is ready.
function isFileDrag(e) {
  return e.dataTransfer?.types.includes('Files') ?? false;
}

document.addEventListener('dragover', (e) => {
  if (isFileDrag(e)) {
    e.preventDefault();
    el.app.classList.toggle('is-dragging', ready);
  }
});

document.addEventListener('dragleave', (e) => {
  if (e.relatedTarget === null) {
    el.app.classList.remove('is-dragging');
  }
});

document.addEventListener('drop', (e) => {
  el.app.classList.remove('is-dragging');
  if (isFileDrag(e)) {
    e.preventDefault();
    if (ready) {
      addFiles([...e.dataTransfer.files]);
      el.prompt.focus();
    }
  }
});

el.attach.addEventListener('click', () => el.fileInput.click());
el.fileInput.addEventListener('change', () => {
  addFiles([...el.fileInput.files]);
  el.fileInput.value = '';
  el.prompt.focus();
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
    const status = await api.availability(chatOptions());
    if (status !== 'unavailable') {
      media = await supportedMedia(api);
    }
    el.fileInput.accept = acceptList(media);
    applyAvailability(status);
  } catch (err) {
    applyAvailability('unavailable');
    setStatus(describeError(err), {error: true});
  }
}

init();
