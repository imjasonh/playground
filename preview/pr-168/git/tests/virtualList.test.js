import { computeWindow } from '../src/ui/virtualList.js';

describe('computeWindow', () => {
  test('empty list renders nothing', () => {
    expect(computeWindow({ total: 0, rowHeight: 20, viewportHeight: 100 })).toEqual({
      start: 0,
      end: 0,
      padTop: 0,
      padBottom: 0,
    });
  });

  test('renders everything when the row height is unknown', () => {
    // Not laid out yet: never hide content, just render it all.
    expect(computeWindow({ total: 1000, rowHeight: 0, viewportHeight: 400 })).toEqual({
      start: 0,
      end: 1000,
      padTop: 0,
      padBottom: 0,
    });
  });

  test('renders everything when the viewport is unmeasured', () => {
    expect(computeWindow({ total: 1000, rowHeight: 20, viewportHeight: 0 })).toEqual({
      start: 0,
      end: 1000,
      padTop: 0,
      padBottom: 0,
    });
  });

  test('a list that fits the viewport renders fully with no padding', () => {
    const w = computeWindow({ total: 10, rowHeight: 20, viewportHeight: 400, overscan: 4 });
    expect(w.start).toBe(0);
    expect(w.end).toBe(10);
    expect(w.padTop).toBe(0);
    expect(w.padBottom).toBe(0);
  });

  test('at the top of a long list, start is clamped and the bottom is padded', () => {
    const total = 10000;
    const rowHeight = 20;
    const viewportHeight = 400; // 20 rows visible
    const w = computeWindow({ scrollTop: 0, viewportHeight, rowHeight, total, overscan: 5 });
    expect(w.start).toBe(0);
    expect(w.end).toBe(25); // 20 visible + 5 overscan (top overscan clamped to 0)
    expect(w.padTop).toBe(0);
    expect(w.padBottom).toBe((total - w.end) * rowHeight);
  });

  test('scrolled into the middle, both paddings are set around the window', () => {
    const total = 10000;
    const rowHeight = 20;
    const viewportHeight = 400;
    const overscan = 5;
    const scrollTop = 4000; // first visible row = 200
    const w = computeWindow({ scrollTop, viewportHeight, rowHeight, total, overscan });
    expect(w.start).toBe(195); // 200 - overscan
    expect(w.end).toBe(225); // 200 + 20 + overscan
    expect(w.padTop).toBe(195 * rowHeight);
    expect(w.padBottom).toBe((total - 225) * rowHeight);
    // Padding + windowed rows always reconstruct the full virtual height.
    const windowed = (w.end - w.start) * rowHeight;
    expect(w.padTop + windowed + w.padBottom).toBe(total * rowHeight);
  });

  test('scrolled to the end, the window reaches the last row with no bottom pad', () => {
    const total = 1000;
    const rowHeight = 20;
    const viewportHeight = 400;
    const scrollTop = total * rowHeight - viewportHeight; // bottom
    const w = computeWindow({ scrollTop, viewportHeight, rowHeight, total, overscan: 5 });
    expect(w.end).toBe(total);
    expect(w.padBottom).toBe(0);
  });

  test('a negative scrollTop is treated as the top', () => {
    const w = computeWindow({ scrollTop: -50, viewportHeight: 400, rowHeight: 20, total: 1000 });
    expect(w.start).toBe(0);
    expect(w.padTop).toBe(0);
  });
});
