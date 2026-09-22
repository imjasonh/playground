import {
  imageMimeType,
  isBinaryExtension,
  isImagePath,
  languageForPath,
  looksBinary,
} from '../src/language.js';

describe('languageForPath', () => {
  test('maps known extensions', () => {
    expect(languageForPath('src/app.js')).toBe('JavaScript');
    expect(languageForPath('main.css')).toBe('CSS');
    expect(languageForPath('README.md')).toBe('Markdown');
    expect(languageForPath('data.json')).toBe('JSON');
  });

  test('recognizes special filenames', () => {
    expect(languageForPath('Dockerfile')).toBe('Dockerfile');
    expect(languageForPath('.gitignore')).toBe('Git Config');
  });

  test('falls back to plain text', () => {
    expect(languageForPath('mystery.qwerty')).toBe('Plain Text');
  });
});

describe('image helpers', () => {
  test('isImagePath detects images including svg', () => {
    expect(isImagePath('a/b/logo.svg')).toBe(true);
    expect(isImagePath('photo.PNG')).toBe(true);
    expect(isImagePath('src/app.js')).toBe(false);
  });

  test('imageMimeType returns sensible types', () => {
    expect(imageMimeType('a.svg')).toBe('image/svg+xml');
    expect(imageMimeType('a.jpg')).toBe('image/jpeg');
    expect(imageMimeType('a.png')).toBe('image/png');
  });
});

describe('binary detection', () => {
  test('isBinaryExtension flags known binary types', () => {
    expect(isBinaryExtension('app.wasm')).toBe(true);
    expect(isBinaryExtension('font.woff2')).toBe(true);
    expect(isBinaryExtension('notes.txt')).toBe(false);
  });

  test('looksBinary detects NUL bytes', () => {
    expect(looksBinary(new Uint8Array([72, 105, 0, 1]))).toBe(true);
  });

  test('looksBinary treats normal text as text', () => {
    const text = new TextEncoder().encode('hello\nworld\t!');
    expect(looksBinary(text)).toBe(false);
  });

  test('looksBinary handles empty input', () => {
    expect(looksBinary(new Uint8Array([]))).toBe(false);
  });
});
