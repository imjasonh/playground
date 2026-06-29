import { fetchFeed, FeedError } from '../src/client.js';
import { encodeFeedMessage } from '../src/sampleFeed.js';
import { VEHICLE_STATUS } from '../src/gtfsRealtime.js';

const bytes = encodeFeedMessage({
  header: { timestamp: 1700000000 },
  entities: [{ id: 'v', vehicle: { trip: { routeId: 'A' }, stopId: 'A27N', currentStatus: VEHICLE_STATUS.STOPPED_AT } }],
});

function okFetch(captured) {
  return async (url, opts) => {
    captured.url = url;
    captured.opts = opts;
    return { ok: true, status: 200, arrayBuffer: async () => bytes.buffer };
  };
}

describe('fetchFeed', () => {
  test('builds the proxied URL and decodes the body', async () => {
    const captured = {};
    const result = await fetchFeed({
      url: 'https://feed',
      proxyTemplate: 'https://p/?url={url}',
      fetchImpl: okFetch(captured),
    });
    expect(captured.url).toBe(`https://p/?url=${encodeURIComponent('https://feed')}`);
    expect(result.message.entities[0].vehicle.stopId).toBe('A27N');
    expect(result.byteLength).toBe(bytes.length);
    expect(result.requestUrl).toBe(captured.url);
  });

  test('non-200 -> FeedError(kind=http)', async () => {
    const fetchImpl = async () => ({ ok: false, status: 404 });
    await expect(fetchFeed({ url: 'u', fetchImpl })).rejects.toMatchObject({ kind: 'http' });
  });

  test('transport failure -> FeedError(kind=network)', async () => {
    const fetchImpl = async () => {
      throw new Error('connection reset');
    };
    const error = await fetchFeed({ url: 'u', fetchImpl }).catch((e) => e);
    expect(error).toBeInstanceOf(FeedError);
    expect(error.kind).toBe('network');
  });

  test('AbortError propagates unchanged', async () => {
    const fetchImpl = async () => {
      const err = new Error('aborted');
      err.name = 'AbortError';
      throw err;
    };
    await expect(fetchFeed({ url: 'u', fetchImpl })).rejects.toMatchObject({ name: 'AbortError' });
  });

  test('undecodable bytes -> FeedError(kind=decode)', async () => {
    const bad = Uint8Array.from([0x0a, 0xff, 0xff, 0xff, 0x0f]);
    const fetchImpl = async () => ({ ok: true, status: 200, arrayBuffer: async () => bad.buffer });
    await expect(fetchFeed({ url: 'u', fetchImpl })).rejects.toMatchObject({ kind: 'decode' });
  });
});
