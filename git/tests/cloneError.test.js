import { cloneErrorMessage } from '../src/cloneError.js';

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
