import {acceptList, buildPrompt, checkFile} from './attachments.js';
import {
  COMPACT_AFTER,
  COMPACT_BEFORE,
  foldPoint,
  isOver,
  summarize,
} from './compaction.js';
import {
  formatWhen,
  historyPrompts,
  newConversation,
  storedAttachment,
  titleFor,
} from './history.js';
import {renderMarkdown} from './markdown.js';
import {
  availabilityMessage,
  chatOptions,
  contextUsage,
  findLanguageModel,
  formatProgress,
  measureUsage,
  restoreSession,
  streamReply,
  supportedMedia,
  usageOf,
} from './model.js';
import {openStore} from './store.js';

const el = {
  app: document.querySelector('.app'),
  log: document.querySelector('#log'),
  empty: document.querySelector('#empty'),
  messages: document.querySelector('#messages'),
  status: document.querySelector('#status'),
  meter: document.querySelector('#meter'),
  meterFill: document.querySelector('#meter-fill'),
  meterTip: document.querySelector('#meter-tip'),
  download: document.querySelector('#download'),
  attachments: document.querySelector('#attachments'),
  composer: document.querySelector('#composer'),
  attach: document.querySelector('#attach'),
  fileInput: document.querySelector('#file-input'),
  prompt: document.querySelector('#prompt'),
  send: document.querySelector('#send'),
  stop: document.querySelector('#stop'),
  newChat: document.querySelector('#new-chat'),
  chats: document.querySelector('#chats'),
  history: document.querySelector('#history'),
  closeHistory: document.querySelector('#close-history'),
  emptyHistory: document.querySelector('#empty-history'),
  conversations: document.querySelector('#conversations'),
  trashIcon: document.querySelector('#trash-icon'),
};

const api = findLanguageModel(globalThis);

let store = null;
let conversation = null;
let session = null;
let sessionPromise = null;
let generation = 0;
let controller = null;
let ready = false;
let overflowed = false;
let media = [];
let pending = [];
const shownUrls = [];
const deletedIds = new Set();

const sessionCallbacks = {
  onProgress: showDownload,
  onOverflow: () => {
    overflowed = true;
  },
};

function setStatus(text, {error = false} = {}) {
  el.status.textContent = text;
  el.status.classList.toggle('is-error', error);
}

// The meter shows the model download while there is one, and the context
// window the rest of the time.
function setMeter({label, fraction, details, className = ''}) {
  const percent = Math.min(100, Math.max(0, Math.round(fraction * 100)));
  el.meter.hidden = false;
  el.meter.className = `meter ${className}`.trim();
  el.meter.style.setProperty('--fill', `${percent}%`);
  el.meter.setAttribute('aria-label', label);
  el.meter.setAttribute('aria-valuenow', String(percent));
  el.meter.setAttribute('aria-valuetext', details.join(' '));
  el.meterTip.textContent = details.join('\n');
}

function showDownload(loaded) {
  setMeter({
    label: 'Model download',
    fraction: loaded,
    details: [formatProgress(loaded)],
    className: 'is-downloading',
  });
}

function showUsage() {
  const usage = usageOf(session);
  el.meter.hidden = usage === null;
  if (usage) {
    const details = [contextUsage(session)];
    if (conversation?.summary) {
      details.push('Older messages are summarized.');
    }
    setMeter({
      label: 'Context window',
      fraction: usage.used / usage.total,
      details,
      className: isOver(usage, COMPACT_AFTER) ? 'is-high' : '',
    });
  }
  setStatus(
    overflowed
      ? 'The oldest messages no longer fit, so the model dropped them.'
      : '',
  );
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

// Returns the session for the open conversation, creating it the first time.
// A saved conversation's summary and messages go in as initial prompts.
function ensureSession() {
  if (sessionPromise) {
    return sessionPromise;
  }
  const started = generation;
  const history = conversation ? historyPrompts(conversation, media) : [];
  const promise = restoreSession(api, history, {...sessionCallbacks, media});
  sessionPromise = promise.then(
    (restored) => {
      if (started !== generation) {
        restored.session.destroy();
        throw new DOMException('The chat changed.', 'AbortError');
      }
      session = restored.session;
      overflowed ||= restored.dropped > 0;
      return session;
    },
    (err) => {
      if (started === generation) {
        sessionPromise = null;
      }
      throw err;
    },
  );
  return sessionPromise;
}

function save(record) {
  if (!store || deletedIds.has(record.id)) {
    return;
  }
  record.title = titleFor(record.messages);
  record.updatedAt = Date.now();
  store.put(record).catch((err) => {
    setStatus(`Couldn't save this chat: ${err?.message || err}`, {
      error: true,
    });
  });
}

// Shows where the summarized part of the chat ends.
function markSummary(through) {
  el.messages.querySelector('.divider')?.remove();
  const first = el.messages.querySelector(`[data-index="${through}"]`);
  if (!first) {
    return;
  }
  const divider = document.createElement('li');
  divider.className = 'divider';
  divider.setAttribute('role', 'separator');
  divider.textContent = 'The model sees a summary of the messages above';
  first.before(divider);
}

// Summarizes the open chat's older messages, then moves the chat to a new
// session that holds the summary and the messages after it, up to `end`.
// Resolves to whether the session changed.
async function compact(record, end, signal) {
  const from = record.summary?.through ?? 0;
  const through =
    foldPoint(record.messages, {from, end}) ??
    foldPoint(record.messages, {from, end, keep: 1});
  if (through === null) {
    return false;
  }
  const started = generation;
  setStatus('Summarizing older messages to make room…');
  try {
    const text = await summarize(api, {
      media,
      previous: record.summary?.text ?? null,
      messages: record.messages.slice(from, through),
      signal,
    });
    record.summary = {text, through};
    save(record);
    if (started !== generation) {
      return false;
    }
    const restored = await restoreSession(
      api,
      historyPrompts(record, media, end),
      {...sessionCallbacks, media},
    );
    if (started !== generation) {
      restored.session.destroy();
      return false;
    }
    session?.destroy();
    session = restored.session;
    overflowed = restored.dropped > 0;
    markSummary(through);
    showUsage();
    return true;
  } catch (err) {
    if (started === generation) {
      if (err?.name === 'AbortError') {
        showUsage();
      } else {
        setStatus(`Couldn't summarize older messages: ${err?.message || err}`, {
          error: true,
        });
      }
    }
    return false;
  }
}

// Compacts in the background. The next message waits for it, because it
// waits for the session.
function compactSoon(record) {
  if (!sessionPromise) {
    return;
  }
  const end = record.messages.length;
  sessionPromise = sessionPromise
    .then(() => compact(record, end))
    .then(() => session);
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

async function send(text, attachments) {
  controller = new AbortController();
  const {signal} = controller;
  const sessionReady = ensureSession();
  conversation ??= newConversation({
    id: crypto.randomUUID(),
    now: Date.now(),
  });
  const record = conversation;
  record.messages.push({
    role: 'user',
    text,
    attachments: attachments.map(storedAttachment),
  });
  save(record);

  const sent = addMessage('user', text, attachments).parentElement;
  sent.dataset.index = String(record.messages.length - 1);
  const reply = addMessage('model', '');
  reply.parentElement.classList.add('is-pending');
  updateSend();
  let replyText = '';
  let failed = false;
  try {
    let current = await sessionReady;
    const prompt = buildPrompt(text, attachments);
    const incoming = await measureUsage(current, prompt);
    if (
      incoming !== null &&
      record === conversation &&
      isOver(usageOf(current), COMPACT_BEFORE, incoming) &&
      (await compact(record, record.messages.length - 1, signal))
    ) {
      current = session;
    }
    if (signal.aborted) {
      return;
    }
    await streamReply(current, prompt, {
      signal,
      onText: (sofar) => {
        replyText = sofar;
        const follow = isNearBottom();
        renderMarkdown(reply, sofar);
        if (follow) {
          scrollToBottom();
        }
      },
    });
  } catch (err) {
    if (err?.name !== 'AbortError') {
      failed = true;
      reply.textContent = describeError(err);
      reply.parentElement.classList.add('is-error');
    }
  } finally {
    if (!failed && replyText !== '') {
      record.messages.push({role: 'assistant', text: replyText, attachments: []});
      reply.parentElement.dataset.index = String(record.messages.length - 1);
      save(record);
    }
    reply.parentElement.classList.remove('is-pending');
    if (signal.aborted && reply.textContent === '') {
      reply.parentElement.remove();
    }
    if (controller?.signal === signal) {
      controller = null;
      updateSend();
      showUsage();
      if (isOver(usageOf(session), COMPACT_AFTER)) {
        compactSoon(record);
      }
    }
  }
}

function resetChat() {
  generation++;
  controller?.abort();
  controller = null;
  session?.destroy();
  session = null;
  sessionPromise = null;
  conversation = null;
  overflowed = false;
  for (const url of shownUrls.splice(0)) {
    URL.revokeObjectURL(url);
  }
  el.messages.replaceChildren();
  el.empty.hidden = false;
  el.meter.hidden = true;
  setStatus('');
  updateSend();
}

function newChat() {
  resetChat();
  el.prompt.focus();
}

function openConversation(record) {
  resetChat();
  conversation = record;
  record.messages.forEach((message, index) => {
    const attachments = message.attachments.map((a) => {
      if (!a.file) {
        return a;
      }
      const url = URL.createObjectURL(a.file);
      shownUrls.push(url);
      return {...a, url};
    });
    const body =
      message.role === 'user'
        ? addMessage('user', message.text, attachments)
        : addMessage('model', '');
    if (message.role === 'assistant') {
      renderMarkdown(body, message.text);
    }
    body.parentElement.dataset.index = String(index);
  });
  if (record.summary) {
    markSummary(record.summary.through);
  }
  updateSend();
  if (!ready) {
    return;
  }
  setStatus('Loading the conversation into the model…');
  ensureSession().then(
    () => {
      showUsage();
      if (overflowed || isOver(usageOf(session), COMPACT_AFTER)) {
        compactSoon(record);
      }
    },
    (err) => {
      if (err?.name !== 'AbortError') {
        setStatus(describeError(err), {error: true});
      }
    },
  );
  el.prompt.focus();
}

function conversationItem(record) {
  const item = document.createElement('li');
  item.className = 'conversation';
  item.classList.toggle('is-current', record.id === conversation?.id);

  const open = document.createElement('button');
  open.type = 'button';
  open.className = 'open';
  const title = document.createElement('span');
  title.className = 'title';
  title.textContent = record.title;
  const when = document.createElement('time');
  when.dateTime = new Date(record.updatedAt).toISOString();
  when.textContent = formatWhen(record.updatedAt, Date.now());
  open.append(title, when);
  open.addEventListener('click', () => {
    el.history.close();
    openConversation(record);
  });

  const remove = document.createElement('button');
  remove.type = 'button';
  remove.className = 'ghost icon delete';
  remove.setAttribute('aria-label', `Delete ${record.title}`);
  remove.title = 'Delete';
  remove.append(el.trashIcon.content.cloneNode(true));
  remove.addEventListener('click', () => deleteConversation(record));

  item.append(open, remove);
  return item;
}

async function showHistory() {
  try {
    const records = await store.list();
    el.conversations.replaceChildren(...records.map(conversationItem));
    el.emptyHistory.hidden = records.length > 0;
  } catch (err) {
    setStatus(`Couldn't load saved chats: ${err?.message || err}`, {
      error: true,
    });
    return;
  }
  if (!el.history.open) {
    el.history.showModal();
  }
}

async function deleteConversation(record) {
  if (!confirm(`Delete "${record.title}"?`)) {
    return;
  }
  deletedIds.add(record.id);
  if (record.id === conversation?.id) {
    resetChat();
  }
  try {
    await store.delete(record.id);
  } catch (err) {
    setStatus(`Couldn't delete the chat: ${err?.message || err}`, {
      error: true,
    });
  }
  showHistory();
}

async function download() {
  el.download.disabled = true;
  setStatus(availabilityMessage('downloading'));
  showDownload(0);
  try {
    await ensureSession();
    el.download.hidden = true;
    setReady(true);
    showUsage();
    el.prompt.focus();
  } catch (err) {
    el.meter.hidden = true;
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
  shownUrls.push(...attachments.map((a) => a.url).filter(Boolean));
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
el.chats.addEventListener('click', showHistory);
el.closeHistory.addEventListener('click', () => el.history.close());

async function initStore() {
  try {
    store = await openStore(indexedDB);
    el.chats.hidden = false;
  } catch {
    store = null;
  }
}

async function initModel() {
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

initStore();
initModel();
