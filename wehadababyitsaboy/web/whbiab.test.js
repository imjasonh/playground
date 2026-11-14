const test = require('node:test');
const assert = require('node:assert/strict');
const { shouldTrack, pingUrl, track } = require('./whbiab.js');

function makeEnv(overrides = {}) {
  const media = overrides.media || {};
  return {
    app: 'queens',
    location: { protocol: 'https:', hostname: 'imjasonh.github.io', pathname: '/playground/queens/' },
    navigator: { language: 'en-US', doNotTrack: null, globalPrivacyControl: undefined, webdriver: false },
    matchMedia: (query) => ({ matches: Boolean(media[query]) }),
    innerWidth: 1280,
    ...overrides,
  };
}

test('the production site is tracked', () => {
  assert.equal(shouldTrack(makeEnv()), true);
});

test('other hosts and schemes are not tracked', () => {
  for (const location of [
    { protocol: 'http:', hostname: 'localhost', pathname: '/' },
    { protocol: 'https:', hostname: 'localhost', pathname: '/' },
    { protocol: 'file:', hostname: '', pathname: '/tmp/index.html' },
    { protocol: 'https:', hostname: 'example.com', pathname: '/playground/queens/' },
  ]) {
    assert.equal(shouldTrack(makeEnv({ location })), false, location.hostname || location.protocol);
  }
});

test('a PR preview is not tracked', () => {
  const location = { protocol: 'https:', hostname: 'imjasonh.github.io', pathname: '/playground/preview/pr-12/queens/' };
  assert.equal(shouldTrack(makeEnv({ location })), false);
});

test('a browser that asks not to be tracked is not tracked', () => {
  const base = { language: 'en-US', webdriver: false };
  assert.equal(shouldTrack(makeEnv({ navigator: { ...base, doNotTrack: '1' } })), false);
  assert.equal(shouldTrack(makeEnv({ navigator: { ...base, globalPrivacyControl: true } })), false);
  assert.equal(shouldTrack(makeEnv({ navigator: { ...base, webdriver: true } })), false);
});

test('the ping names the app and the context', () => {
  const url = new URL(pingUrl(makeEnv()));
  assert.equal(url.origin + url.pathname, 'https://storage.googleapis.com/wehadababyitsaboy/queens/web.mouse.light.desktop');
  assert.equal(url.searchParams.get('lang'), 'en');
  assert.match(url.search, /^\?bob=wehadababyitsaboy(&|$)/, 'bob comes first');
});

test('the ping describes a phone', () => {
  const env = makeEnv({
    innerWidth: 390,
    media: { '(pointer: coarse)': true, '(prefers-color-scheme: dark)': true, '(display-mode: standalone)': true },
  });
  assert.equal(new URL(pingUrl(env)).pathname, '/wehadababyitsaboy/queens/web.touch.dark.standalone.phone');
});

test('the ping describes a tablet', () => {
  assert.equal(new URL(pingUrl(makeEnv({ innerWidth: 800 }))).pathname, '/wehadababyitsaboy/queens/web.mouse.light.tablet');
});

test('an app name and a language are sanitized', () => {
  const env = makeEnv({ app: 'My App/../x', navigator: { language: 'zz@evil', webdriver: false } });
  const url = new URL(pingUrl(env));
  assert.equal(url.pathname.split('/')[2], 'my-app----x');
  assert.equal(url.searchParams.get('lang'), 'zz-evil');
});

test('a missing language leaves out the lang parameter', () => {
  const env = makeEnv({ navigator: { language: '', webdriver: false } });
  assert.equal(new URL(pingUrl(env)).searchParams.has('lang'), false);
});

test('track requests the image without a referrer', () => {
  const img = {};
  track(makeEnv(), () => img);
  assert.equal(img.referrerPolicy, 'no-referrer');
  assert.equal(img.fetchPriority, 'low');
  assert.match(img.src, /^https:\/\/storage\.googleapis\.com\/wehadababyitsaboy\/queens\/web\./);
});

test('track sends nothing without an app or on an untracked page', () => {
  let made = 0;
  const newImage = () => {
    made++;
    return {};
  };
  track(makeEnv({ app: undefined }), newImage);
  track(makeEnv({ location: { protocol: 'http:', hostname: 'localhost', pathname: '/' } }), newImage);
  assert.equal(made, 0);
});
