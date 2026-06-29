import {
  minutesUntil,
  formatCountdown,
  clockTime,
  secondsAgo,
  freshness,
  pluralize,
} from '../src/format.js';

const NOW_MS = 1700000000000;
const NOW_SEC = NOW_MS / 1000;

describe('minutesUntil / formatCountdown', () => {
  test('minutesUntil is fractional minutes from now', () => {
    expect(minutesUntil(NOW_SEC + 300, NOW_MS)).toBe(5);
    expect(minutesUntil(NOW_SEC - 60, NOW_MS)).toBe(-1);
  });

  test('formatCountdown shows "Now" within ~30s', () => {
    expect(formatCountdown(NOW_SEC + 10, NOW_MS)).toBe('Now');
    expect(formatCountdown(NOW_SEC, NOW_MS)).toBe('Now');
  });

  test('formatCountdown rounds to whole minutes', () => {
    expect(formatCountdown(NOW_SEC + 300, NOW_MS)).toBe('5 min');
    expect(formatCountdown(NOW_SEC + 90, NOW_MS)).toBe('2 min');
  });
});

describe('clockTime', () => {
  test('formats in a given timezone', () => {
    // 1700000000s = 2023-11-14T22:13:20Z
    expect(clockTime(NOW_SEC, { timeZone: 'UTC' })).toMatch(/10:13/);
  });

  test('non-finite input -> empty', () => {
    expect(clockTime(undefined)).toBe('');
  });
});

describe('freshness', () => {
  test('buckets recent times sensibly', () => {
    expect(freshness(NOW_SEC - 5, NOW_MS)).toBe('just now');
    expect(freshness(NOW_SEC - 42, NOW_MS)).toBe('42s ago');
    expect(freshness(NOW_SEC - 120, NOW_MS)).toBe('2 min ago');
    expect(freshness(NOW_SEC - 7200, NOW_MS)).toBe('2 hr ago');
  });

  test('secondsAgo is whole seconds', () => {
    expect(secondsAgo(NOW_SEC - 30, NOW_MS)).toBe(30);
  });
});

describe('pluralize', () => {
  test('default plural', () => {
    expect(pluralize(1, 'train')).toBe('train');
    expect(pluralize(2, 'train')).toBe('trains');
  });

  test('explicit plural', () => {
    expect(pluralize(2, 'bus', 'buses')).toBe('buses');
  });
});
