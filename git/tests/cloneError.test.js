import { cloneErrorMessage, classifyCloneError } from '../src/cloneError.js';

describe('classifyCloneError', () => {
  test('classifies a QuotaExceededError by name', () => {
    const err = Object.assign(new Error('whatever'), { name: 'QuotaExceededError' });
    expect(classifyCloneError(err)).toMatchObject({ kind: 'quota', name: 'QuotaExceededError' });
  });

  test('classifies quota problems by message text', () => {
    expect(classifyCloneError(new Error('insufficient storage')).kind).toBe('quota');
    expect(classifyCloneError(new Error('exceeded the quota for this origin')).kind).toBe('quota');
  });

  test('classifies auth failures (401/403/cancel) before network', () => {
    expect(classifyCloneError(new Error('HTTP Error: 401 Unauthorized')).kind).toBe('auth');
    expect(classifyCloneError(new Error('403 Forbidden')).kind).toBe('auth');
    expect(
      classifyCloneError(Object.assign(new Error('x'), { name: 'UserCanceledError' })).kind
    ).toBe('auth');
  });

  test('classifies transport failures as network', () => {
    expect(classifyCloneError(new Error('Failed to fetch')).kind).toBe('network');
    expect(classifyCloneError(new Error('NetworkError when attempting to fetch')).kind).toBe(
      'network'
    );
    expect(classifyCloneError(new Error('getaddrinfo ENOTFOUND host')).kind).toBe('network');
  });

  test('classifies missing repos/refs as not-found', () => {
    expect(classifyCloneError(new Error('HTTP 404: Not Found')).kind).toBe('not-found');
    expect(classifyCloneError(new Error('Could not find ref')).kind).toBe('not-found');
  });

  test('falls back to unknown and preserves the original message', () => {
    expect(classifyCloneError(new Error('weird internal thing'))).toEqual({
      kind: 'unknown',
      name: 'Error',
      message: 'weird internal thing',
    });
  });

  test('tolerates a non-Error value', () => {
    expect(classifyCloneError('boom')).toMatchObject({ kind: 'unknown', message: 'boom' });
  });
});

describe('cloneErrorMessage', () => {
  test('detects a QuotaExceededError by name', () => {
    const err = Object.assign(new Error('The quota has been exceeded.'), {
      name: 'QuotaExceededError',
    });
    const msg = cloneErrorMessage(err, '');
    expect(msg).toMatch(/Out of browser storage/i);
    expect(msg).toMatch(/Remove a stored repository/i);
  });

  test('detects quota problems by message text', () => {
    expect(cloneErrorMessage(new Error('insufficient storage on device'))).toMatch(
      /Out of browser storage/i
    );
  });

  test('network failures suggest a CORS proxy only when none is set', () => {
    const withProxy = cloneErrorMessage(new Error('Failed to fetch'), 'https://proxy');
    expect(withProxy).toMatch(/proxy may be down/i);

    const noProxy = cloneErrorMessage(new Error('Failed to fetch'), '');
    expect(noProxy).toMatch(/need a CORS proxy/i);
  });

  test('maps 401/403 to an add-a-token hint for private repos', () => {
    expect(cloneErrorMessage(new Error('HTTP Error: 401 Unauthorized'))).toMatch(
      /access token in Advanced options/i
    );
    expect(cloneErrorMessage(new Error('403 Forbidden'))).toMatch(/Authentication required/i);
    expect(
      cloneErrorMessage(new Error('HTTP Basic: Access denied for fetch'))
    ).toMatch(/private/i);
  });

  test('maps 404 / not-found to a check-the-URL hint', () => {
    expect(cloneErrorMessage(new Error('HTTP 404: Not Found'))).toMatch(/not found/i);
    expect(cloneErrorMessage(new Error('Could not find ref'))).toMatch(/Check the URL/i);
  });

  test('falls back to a generic message and includes the cause', () => {
    expect(cloneErrorMessage(new Error('weird internal thing'))).toBe(
      'Clone failed: weird internal thing'
    );
  });

  test('tolerates a non-Error value', () => {
    expect(cloneErrorMessage('boom')).toMatch(/Clone failed: boom/);
  });
});
