// Records one visit to a browser app in the wehadababyitsaboy usage bucket.
//
// Each browser app links this file into its directory as whbiab.js and loads
// it from index.html:
//
//   <script src="whbiab.js" data-app="my-app"></script>
//
// The script requests an image that does not exist, once per page load:
//
//   https://storage.googleapis.com/wehadababyitsaboy/my-app/web.touch.dark.phone?bob=wehadababyitsaboy&lang=en
//
// The bucket answers 403 and its usage log keeps the request. The path is the
// app, then the dot-separated context: the pointer (touch or mouse), the color
// scheme (dark or light), standalone for an installed app, and the screen
// class (phone, tablet, or desktop). The query holds the primary language.
// A PR preview on the production host adds preview=pr-<N>. Nothing else
// leaves the page, and the request sends no referrer.
//
// A visit is not counted for a browser that asks not to be tracked, a
// browser under automation, or a page that is not the production site.
// Tests and local servers therefore send nothing.
(() => {
  'use strict';

  const ENDPOINT = 'https://storage.googleapis.com/wehadababyitsaboy';
  const PRODUCTION_HOST = 'imjasonh.github.io';
  const PHONE_MAX_WIDTH = 600;
  const TABLET_MAX_WIDTH = 1024;

  function shouldTrack(env) {
    const { location, navigator } = env;
    if (location.protocol !== 'https:' || location.hostname !== PRODUCTION_HOST) {
      return false;
    }
    if (navigator.doNotTrack === '1' || navigator.globalPrivacyControl === true) {
      return false;
    }
    return navigator.webdriver !== true;
  }

  function clean(value) {
    return String(value).toLowerCase().replace(/[^a-z0-9_-]/g, '-').slice(0, 64);
  }

  function pingUrl(env) {
    const matches = (query) => env.matchMedia(query).matches;
    const parts = [
      'web',
      matches('(pointer: coarse)') ? 'touch' : 'mouse',
      matches('(prefers-color-scheme: dark)') ? 'dark' : 'light',
    ];
    if (matches('(display-mode: standalone)')) {
      parts.push('standalone');
    }
    if (env.innerWidth < PHONE_MAX_WIDTH) {
      parts.push('phone');
    } else if (env.innerWidth < TABLET_MAX_WIDTH) {
      parts.push('tablet');
    } else {
      parts.push('desktop');
    }
    const query = new URLSearchParams({ bob: 'wehadababyitsaboy' });
    const lang = clean((env.navigator.language || '').split('-')[0]);
    if (lang) {
      query.set('lang', lang);
    }
    const preview = /^\/[^/]+\/preview\/(pr-\d+)\//.exec(env.location.pathname);
    if (preview) {
      query.set('preview', preview[1]);
    }
    return `${ENDPOINT}/${clean(env.app)}/${parts.join('.')}?${query}`;
  }

  function track(env, newImage) {
    if (!env.app || !shouldTrack(env)) {
      return;
    }
    const img = newImage();
    img.referrerPolicy = 'no-referrer';
    img.fetchPriority = 'low';
    img.alt = '';
    img.src = pingUrl(env);
  }

  if (typeof window === 'undefined') {
    module.exports = { shouldTrack, pingUrl, track };
    return;
  }

  const script = document.currentScript;
  const env = {
    app: script && script.dataset.app,
    location: window.location,
    navigator: window.navigator,
    matchMedia: window.matchMedia.bind(window),
    innerWidth: window.innerWidth,
  };
  const send = () => track(env, () => new Image());
  if (document.readyState === 'complete') {
    send();
  } else {
    window.addEventListener('load', send, { once: true });
  }
})();
