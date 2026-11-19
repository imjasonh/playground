import {makeCard, spokenProblem} from './problems.js';
import {filledDots, loadStats, recordAnswer, saveStats} from './stats.js';

const KIND = 'addition';
// A drag past this fraction of the card's width picks that side's answer.
const COMMIT_FRACTION = 0.3;
// A flick faster than this (pixels per millisecond) picks an answer before
// the drag reaches the commit distance, once it has moved FLICK_MIN_PX.
const FLICK_SPEED = 0.5;
const FLICK_MIN_PX = 40;
// Horizontal movement before a press becomes a drag.
const DRAG_SLOP_PX = 8;
// The card tilts one degree for each this many pixels of drag.
const TILT_PX_PER_DEG = 20;
// How long a tapped or keyed answer shows on the card before it flies off.
const RIGHT_PAUSE_MS = 350;
// How long the right answer stays up after a wrong pick.
const WRONG_PAUSE_MS = 1600;
const CHEER_MS = 2400;
const PIECES = 40;
const PIECE_SYMBOLS = [...'0123456789', '+', '+', '+', '='];
const PIECE_COLORS = [
  '#ff4f8b', '#ff9f1c', '#ffd23f', '#2dc76d', '#1fc7b6', '#2f80ff',
  '#8b5cf6',
];
const SPRING = CSS.supports('transition-timing-function', 'linear(0, 1)') ?
    'linear(0, 0.45 15%, 1.08 35%, 0.97 55%, 1.01 75%, 1)' :
    'ease-out';
const KEY_SIDES = new Map([['ArrowLeft', 'left'], ['ArrowRight', 'right']]);

const cardEl = document.querySelector('#card');
const problemEl = document.querySelector('#problem');
const buttons = {
  left: document.querySelector('#choice-left'),
  right: document.querySelector('#choice-right'),
};
const statEls = {
  answered: document.querySelector('#answered'),
  streak: document.querySelector('#streak'),
  best: document.querySelector('#best'),
};
const dotEls = [...document.querySelectorAll('#dots li')];
const statusEl = document.querySelector('#status');
const partyEl = document.querySelector('#party');
const cheerEl = document.querySelector('#cheer');
const cheerCountEl = document.querySelector('#cheer-count');
const reducedMotion = window.matchMedia('(prefers-reduced-motion: reduce)');

let storage = null;
try {
  storage = window.localStorage;
} catch {
  // Storage is blocked. Stats last until the page closes.
}

let stats = loadStats(storage);
let card = null;
let busy = false;
let drag = null;
let offset = 0;
function delay(ms) {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

function span(className, text, hidden = false) {
  const el = document.createElement('span');
  el.className = className;
  el.textContent = text;
  if (hidden) {
    el.setAttribute('aria-hidden', 'true');
  }
  return el;
}

function renderStats(bump) {
  for (const [key, el] of Object.entries(statEls)) {
    const text = String(stats[key]);
    if (el.textContent === text) {
      continue;
    }
    el.textContent = text;
    if (bump) {
      el.classList.remove('is-bumped');
      // Restarts the animation when the class comes straight back.
      void el.offsetWidth;
      el.classList.add('is-bumped');
    }
  }
  const filled = filledDots(stats.streak);
  dotEls.forEach((dot, i) => dot.classList.toggle('is-filled', i < filled));
}

function renderCard() {
  const visual = span('', '', true);
  card.operands.forEach((n, i) => {
    if (i > 0) {
      visual.append(' ', span('operator', card.operator), ' ');
    }
    visual.append(span('operand', String(n)));
  });
  visual.append(' ', span('equals', '='), ' ', span('slot', '?'));
  problemEl.replaceChildren(
      span('visually-hidden', `${spokenProblem(card)} equals what?`),
      visual);

  for (const [i, side] of ['left', 'right'].entries()) {
    const button = buttons[side];
    button.querySelector('.value').textContent = String(card.choices[i]);
    button.classList.remove('is-answer', 'is-miss', 'is-leaning');
  }
  cardEl.classList.remove('is-correct', 'is-wrong');
}

function revealAnswer(correct, side) {
  problemEl.querySelector('.slot').textContent = String(card.answer);
  cardEl.classList.add(correct ? 'is-correct' : 'is-wrong');
  for (const [i, s] of ['left', 'right'].entries()) {
    const isAnswer = card.choices[i] === card.answer;
    buttons[s].classList.toggle('is-answer', isAnswer);
    buttons[s].classList.toggle('is-miss', s === side && !isAnswer);
  }
}

function announce(text) {
  statusEl.textContent = text;
}

/** Moves the card to rest at the center with no transition. */
function resetCardPosition() {
  cardEl.classList.add('is-dragging');
  for (const animation of cardEl.getAnimations()) {
    animation.cancel();
  }
  offset = 0;
  cardEl.style.translate = '';
  cardEl.style.rotate = '';
  // Applies the reset while transitions are off, so the next style change
  // doesn't animate from the old position.
  void cardEl.offsetWidth;
  cardEl.classList.remove('is-dragging');
}

function setOffset(x) {
  offset = x;
  cardEl.style.translate = `${x}px 0`;
  cardEl.style.rotate = `${x / TILT_PX_PER_DEG}deg`;
}

function snapBack() {
  cardEl.classList.remove('is-dragging');
  offset = 0;
  cardEl.style.translate = '';
  cardEl.style.rotate = '';
}

function lean(side) {
  buttons.left.classList.toggle('is-leaning', side === 'left');
  buttons.right.classList.toggle('is-leaning', side === 'right');
}

function enterCard() {
  if (reducedMotion.matches) {
    cardEl.animate({opacity: [0, 1]}, {duration: 150, easing: 'ease-out'});
    return;
  }
  cardEl.animate({opacity: [0, 1]}, {duration: 150, easing: 'ease-out'});
  cardEl.animate({scale: [0.6, 1]}, {duration: 450, easing: SPRING});
}

function flyAway(side) {
  if (reducedMotion.matches) {
    return cardEl.animate({opacity: [1, 0]},
        {duration: 150, easing: 'ease-in', fill: 'forwards'}).finished;
  }
  const direction = side === 'left' ? -1 : 1;
  const distance = window.innerWidth * 1.2;
  return cardEl.animate([
    {translate: `${offset}px 0`, rotate: `${offset / TILT_PX_PER_DEG}deg`},
    {translate: `${direction * distance}px 0`, rotate: `${direction * 24}deg`},
  ], {duration: 320, easing: 'ease-in', fill: 'forwards'}).finished;
}

function fadeOut() {
  return cardEl.animate({opacity: [1, 0]},
      {duration: 150, easing: 'ease-in', fill: 'forwards'}).finished;
}

function shake() {
  if (reducedMotion.matches) {
    return;
  }
  // Animates transform, so it runs alongside the transition that brings
  // translate back to the center.
  cardEl.animate([
    {transform: 'translateX(0)'},
    {transform: 'translateX(-0.75rem)'},
    {transform: 'translateX(0.75rem)'},
    {transform: 'translateX(-0.5rem)'},
    {transform: 'translateX(0.5rem)'},
    {transform: 'translateX(0)'},
  ], {duration: 450, easing: 'ease-in-out'});
}

function deal(note = '') {
  card = makeCard(KIND, Math.random, card);
  resetCardPosition();
  renderCard();
  const next = `${spokenProblem(card)} equals what?`;
  announce(note ? `${note} Next, ${next}` : next);
}

async function choose(side) {
  if (busy || !card) {
    return;
  }
  busy = true;
  drag = null;
  lean(null);
  const picked = card.choices[side === 'left' ? 0 : 1];
  const correct = picked === card.answer;
  const result = recordAnswer(stats, correct);
  stats = result.stats;
  saveStats(storage, stats);
  renderStats(true);
  revealAnswer(correct, side);

  const solved = `${spokenProblem(card)} is ${card.answer}.`;
  let note = correct ? `Right! ${solved}` : `Not quite. ${solved}`;
  let cheered = null;
  if (result.celebrate) {
    note += ` ${stats.streak} in a row!`;
    cheered = celebrate(stats.streak);
  }

  try {
    if (correct) {
      if (offset === 0) {
        await delay(RIGHT_PAUSE_MS);
      }
      await flyAway(side);
      await cheered;
      deal(note);
    } else {
      announce(note);
      snapBack();
      shake();
      await delay(WRONG_PAUSE_MS);
      await fadeOut();
      deal();
    }
  } finally {
    busy = false;
  }
  enterCard();
}

function press(side) {
  const button = buttons[side];
  button.classList.add('is-pressed');
  setTimeout(() => button.classList.remove('is-pressed'), 120);
}

// Celebration

async function hideCheer() {
  try {
    await cheerEl.animate({opacity: [1, 0]}, {duration: 250, easing: 'ease-in'})
        .finished;
  } catch {
    // A canceled fade still hides the cheer.
  }
  cheerEl.hidden = true;
}

function burst() {
  const width = window.innerWidth;
  const height = window.innerHeight;
  const reach = Math.min(width, height) * 0.55;
  for (let i = 0; i < PIECES; i++) {
    const piece = span('piece',
        PIECE_SYMBOLS[Math.floor(Math.random() * PIECE_SYMBOLS.length)]);
    piece.style.color =
        PIECE_COLORS[Math.floor(Math.random() * PIECE_COLORS.length)];
    piece.style.fontSize = `${1.5 + Math.random() * 2.5}rem`;
    partyEl.append(piece);

    const angle = Math.random() * Math.PI * 2;
    const distance = reach * (0.5 + Math.random() * 0.6);
    const dx = Math.cos(angle) * distance;
    const dy = Math.sin(angle) * distance;
    const fall = height * (0.2 + Math.random() * 0.2);
    const spin = (Math.random() - 0.5) * 720;
    const at = (x, y) => `calc(-50% + ${x}px) calc(-50% + ${y}px)`;
    piece.animate([
      {translate: at(0, 0), rotate: '0deg', scale: 0.3, opacity: 1},
      {
        offset: 0.45,
        translate: at(dx, dy),
        rotate: `${spin / 2}deg`,
        scale: 1,
        opacity: 1,
      },
      {translate: at(dx * 1.1, dy + fall), rotate: `${spin}deg`, opacity: 0},
    ], {
      duration: 1500 + Math.random() * 700,
      easing: 'cubic-bezier(0.2, 0.7, 0.4, 1)',
      fill: 'forwards',
    }).finished.finally(() => piece.remove());
  }
}

async function celebrate(streak) {
  cheerCountEl.textContent = String(streak);
  for (const animation of cheerEl.getAnimations()) {
    animation.cancel();
  }
  cheerEl.hidden = false;
  if (reducedMotion.matches) {
    cheerEl.animate({opacity: [0, 1]}, {duration: 200, easing: 'ease-out'});
  } else {
    cheerEl.animate({opacity: [0, 1]}, {duration: 150, easing: 'ease-out'});
    cheerEl.animate({scale: [0.3, 1]}, {duration: 600, easing: SPRING});
    burst();
  }
  await delay(CHEER_MS);
  await hideCheer();
}

// Input

function commitDistance() {
  return cardEl.offsetWidth * COMMIT_FRACTION;
}

cardEl.addEventListener('pointerdown', (event) => {
  if (busy || !event.isPrimary || event.button !== 0) {
    return;
  }
  drag = {
    pointerId: event.pointerId,
    startX: event.clientX,
    startY: event.clientY,
    lastX: event.clientX,
    lastTime: event.timeStamp,
    velocity: 0,
    active: false,
  };
  cardEl.setPointerCapture(event.pointerId);
});

cardEl.addEventListener('pointermove', (event) => {
  if (!drag || event.pointerId !== drag.pointerId) {
    return;
  }
  const dx = event.clientX - drag.startX;
  const dy = event.clientY - drag.startY;
  if (!drag.active) {
    if (Math.abs(dx) < DRAG_SLOP_PX && Math.abs(dy) < DRAG_SLOP_PX) {
      return;
    }
    if (Math.abs(dy) > Math.abs(dx)) {
      drag = null;
      return;
    }
    drag.active = true;
    cardEl.classList.add('is-dragging');
  }
  const elapsed = Math.max(1, event.timeStamp - drag.lastTime);
  const instant = (event.clientX - drag.lastX) / elapsed;
  drag.velocity = drag.velocity * 0.3 + instant * 0.7;
  drag.lastX = event.clientX;
  drag.lastTime = event.timeStamp;
  setOffset(dx);
  lean(Math.abs(dx) < commitDistance() ? null : sideOf(dx));
});

function sideOf(dx) {
  return dx < 0 ? 'left' : 'right';
}

function endDrag(event) {
  if (!drag || event.pointerId !== drag.pointerId) {
    return;
  }
  const {active, velocity} = drag;
  drag = null;
  lean(null);
  if (!active) {
    return;
  }
  const distance = Math.abs(offset);
  const flicked = Math.abs(velocity) > FLICK_SPEED &&
      distance > FLICK_MIN_PX && Math.sign(velocity) === Math.sign(offset);
  if (event.type === 'pointerup' &&
      (distance > commitDistance() || flicked)) {
    choose(sideOf(offset));
  } else {
    snapBack();
  }
}

cardEl.addEventListener('pointerup', endDrag);
cardEl.addEventListener('pointercancel', endDrag);
cardEl.addEventListener('lostpointercapture', endDrag);

for (const [side, button] of Object.entries(buttons)) {
  button.addEventListener('click', () => choose(side));
}

document.addEventListener('keydown', (event) => {
  if (event.altKey || event.ctrlKey || event.metaKey || event.shiftKey) {
    return;
  }
  const side = KEY_SIDES.get(event.key);
  if (!side) {
    return;
  }
  event.preventDefault();
  if (event.repeat || busy) {
    return;
  }
  press(side);
  choose(side);
});

renderStats(false);
card = makeCard(KIND, Math.random);
renderCard();
