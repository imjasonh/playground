/**
 * @jest-environment jsdom
 */
import {
  TAP_MOVE_THRESHOLD,
  TAP_TIME_THRESHOLD,
  DRAG_START_THRESHOLD,
  createPointerSession,
  interactionHint,
  isTap,
  pointerMovedEnough,
  prefersTapPlacement,
} from '../src/input.js';

describe('input gestures', () => {
  test('detects tap when movement and duration are small', () => {
    const session = {
      dragging: false,
      startX: 100,
      startY: 200,
      startTime: Date.now() - 100,
    };
    expect(isTap(session, { clientX: 105, clientY: 203 })).toBe(true);
  });

  test('rejects tap when pointer moved too far', () => {
    const session = {
      dragging: false,
      startX: 100,
      startY: 200,
      startTime: Date.now() - 100,
    };
    expect(isTap(session, { clientX: 130, clientY: 200 })).toBe(false);
  });

  test('rejects tap after drag mode started', () => {
    const session = {
      dragging: true,
      startX: 100,
      startY: 200,
      startTime: Date.now() - 100,
    };
    expect(isTap(session, { clientX: 101, clientY: 201 })).toBe(false);
  });

  test('pointerMovedEnough respects drag threshold', () => {
    const session = createPointerSession({ pointerId: 1, clientX: 0, clientY: 0 });
    expect(pointerMovedEnough(session, { clientX: 3, clientY: 0 }, DRAG_START_THRESHOLD)).toBe(false);
    expect(pointerMovedEnough(session, { clientX: 10, clientY: 0 }, DRAG_START_THRESHOLD)).toBe(true);
  });

  test('interactionHint describes tap flow on touch devices', () => {
    expect(interactionHint(true)).toMatch(/Tap a piece/i);
    expect(interactionHint(false)).toMatch(/drag/i);
  });

  test('threshold constants are touch-friendly', () => {
    expect(TAP_MOVE_THRESHOLD).toBeGreaterThanOrEqual(8);
    expect(TAP_TIME_THRESHOLD).toBeGreaterThanOrEqual(300);
  });
});

describe('prefersTapPlacement', () => {
  const originalMatchMedia = window.matchMedia;

  afterEach(() => {
    window.matchMedia = originalMatchMedia;
  });

  test('returns true for coarse pointer', () => {
    window.matchMedia = (query) => ({
      matches: query === '(pointer: coarse)',
      addEventListener: () => {},
    });
    expect(prefersTapPlacement()).toBe(true);
  });

  test('returns true when hover is unavailable', () => {
    window.matchMedia = (query) => ({
      matches: query === '(hover: none)',
      addEventListener: () => {},
    });
    expect(prefersTapPlacement()).toBe(true);
  });
});
