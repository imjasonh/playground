import {
  storageEstimate,
  describeStorage,
  isLowOnStorage,
  LOW_STORAGE_BYTES,
} from '../src/quota.js';

const MB = 1024 * 1024;

function navWith(estimate) {
  return { storage: { estimate } };
}

describe('storageEstimate', () => {
  test('returns null when the StorageManager API is unavailable', async () => {
    expect(await storageEstimate(undefined)).toBeNull();
    expect(await storageEstimate({})).toBeNull();
    expect(await storageEstimate({ storage: {} })).toBeNull();
  });

  test('computes usage / quota / available / ratio', async () => {
    const nav = navWith(async () => ({ usage: 25 * MB, quota: 100 * MB }));
    const est = await storageEstimate(nav);
    expect(est).toEqual({
      usage: 25 * MB,
      quota: 100 * MB,
      available: 75 * MB,
      ratio: 0.25,
    });
  });

  test('never reports negative available space, and ratio is 0 without a quota', async () => {
    const nav = navWith(async () => ({ usage: 10 * MB, quota: 0 }));
    const est = await storageEstimate(nav);
    expect(est.available).toBe(0);
    expect(est.ratio).toBe(0);
  });

  test('returns null when estimate() rejects', async () => {
    const nav = navWith(async () => {
      throw new Error('nope');
    });
    expect(await storageEstimate(nav)).toBeNull();
  });
});

describe('describeStorage', () => {
  test('formats a usage label', () => {
    expect(describeStorage({ usage: 25 * MB, quota: 100 * MB, available: 75 * MB, ratio: 0.25 })).toBe(
      '25 MB of 100 MB used (25%)'
    );
  });

  test('returns an empty string when there is nothing to show', () => {
    expect(describeStorage(null)).toBe('');
    expect(describeStorage({ usage: 0, quota: 0, available: 0, ratio: 0 })).toBe('');
  });
});

describe('isLowOnStorage', () => {
  test('true only when free space is under the threshold and a quota is known', () => {
    expect(isLowOnStorage({ quota: 100 * MB, available: 10 * MB })).toBe(true);
    expect(isLowOnStorage({ quota: 100 * MB, available: 60 * MB })).toBe(false);
    expect(isLowOnStorage(null)).toBe(false);
    expect(isLowOnStorage({ quota: 0, available: 0 })).toBe(false);
  });

  test('honors a custom threshold', () => {
    expect(isLowOnStorage({ quota: 100 * MB, available: 30 * MB }, 20 * MB)).toBe(false);
    expect(isLowOnStorage({ quota: 100 * MB, available: 10 * MB }, 20 * MB)).toBe(true);
  });

  test('default threshold is ~50 MB', () => {
    expect(LOW_STORAGE_BYTES).toBe(50 * MB);
  });
});
