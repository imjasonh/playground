import { buildFetchUrl, isDirect, PROXY_PRESETS, DIRECT } from '../src/proxy.js';

const FEED = 'https://api-endpoint.mta.info/Dataservice/mtagtfsfeeds/nyct%2Fgtfs-ace';

describe('buildFetchUrl', () => {
  test('empty template is a direct request', () => {
    expect(buildFetchUrl('', FEED)).toBe(FEED);
    expect(buildFetchUrl(DIRECT, FEED)).toBe(FEED);
  });

  test('{url} is replaced with the encoded feed url', () => {
    expect(buildFetchUrl('https://p/?url={url}', FEED)).toBe(`https://p/?url=${encodeURIComponent(FEED)}`);
  });

  test('{rawurl} is replaced with the raw feed url', () => {
    expect(buildFetchUrl('https://p/?q={rawurl}', FEED)).toBe(`https://p/?q=${FEED}`);
  });

  test('trailing "=" appends an encoded url', () => {
    expect(buildFetchUrl('https://p/?url=', FEED)).toBe(`https://p/?url=${encodeURIComponent(FEED)}`);
  });

  test('trailing "/" appends a raw url', () => {
    expect(buildFetchUrl('https://p/fetch/', FEED)).toBe(`https://p/fetch/${FEED}`);
  });

  test('otherwise appends an encoded url', () => {
    expect(buildFetchUrl('https://p/get', FEED)).toBe(`https://p/get${encodeURIComponent(FEED)}`);
  });
});

describe('isDirect / presets', () => {
  test('isDirect reflects emptiness', () => {
    expect(isDirect('')).toBe(true);
    expect(isDirect('  ')).toBe(true);
    expect(isDirect('https://p/?url={url}')).toBe(false);
  });

  test('every preset builds a usable URL containing the feed', () => {
    for (const preset of PROXY_PRESETS) {
      const built = buildFetchUrl(preset.template, FEED);
      expect(typeof built).toBe('string');
      // Either the raw or encoded host of the feed shows up in the result.
      expect(built.includes('mta.info') || built.includes(encodeURIComponent(FEED))).toBe(true);
    }
  });
});
