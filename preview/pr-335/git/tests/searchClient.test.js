import { createSearchClient } from '../src/searchClient.js';

/**
 * Controllable stand-in for a Web Worker: records what the client posts and lets
 * the test drive replies/errors deterministically, so we can assert the protocol
 * and the concurrency/epoch handling without spawning a real worker.
 */
class FakeWorker {
  constructor() {
    this.posted = [];
    this.terminated = false;
    this.onmessage = null;
    this.onerror = null;
    this.onmessageerror = null;
  }

  postMessage(msg) {
    this.posted.push(msg);
  }

  terminate() {
    this.terminated = true;
  }

  /** Simulate a `result` message coming back from the worker. */
  reply(msg) {
    if (this.onmessage) this.onmessage({ data: msg });
  }

  /** Simulate the worker throwing / failing to load. */
  fail() {
    if (this.onerror) this.onerror(new Error('boom'));
  }

  queries() {
    return this.posted.filter((m) => m.type === 'query');
  }
}

const result = (item) => ({ item, score: 1, positions: [0], target: item });

describe('createSearchClient — synchronous fallback', () => {
  test('reports it is not using a worker and still searches', async () => {
    const client = createSearchClient({ useWorker: false });
    expect(client.usingWorker).toBe(false);

    client.setFiles(['src/app.js', 'src/ui/render.js', 'README.md']);
    const results = await client.search('app');
    expect(results.map((r) => r.item)).toContain('src/app.js');
    expect(results[0].item).toBe('src/app.js');
  });

  test('respects the limit option', async () => {
    const client = createSearchClient({ useWorker: false });
    client.setFiles(['a', 'b', 'c', 'd']);
    const results = await client.search('', { limit: 2 });
    expect(results).toHaveLength(2);
  });

  test('reflects an updated corpus', async () => {
    const client = createSearchClient({ useWorker: false });
    client.setFiles(['old.js']);
    client.setFiles(['new.js']);
    const results = await client.search('new');
    expect(results.map((r) => r.item)).toEqual(['new.js']);
  });
});

describe('createSearchClient — worker backend', () => {
  test('posts the initial corpus on startup', () => {
    const fake = new FakeWorker();
    const client = createSearchClient({ createWorker: () => fake });
    expect(client.usingWorker).toBe(true);
    expect(fake.posted[0]).toMatchObject({ type: 'setFiles', epoch: 0, files: [] });
  });

  test('posts setFiles + query and resolves the correlated reply', async () => {
    const fake = new FakeWorker();
    const client = createSearchClient({ createWorker: () => fake });

    client.setFiles(['x.js']);
    expect(fake.posted.at(-1)).toMatchObject({ type: 'setFiles', epoch: 1, files: ['x.js'] });

    const pending = client.search('x', { limit: 5 });
    const query = fake.queries().at(-1);
    expect(query).toMatchObject({ type: 'query', query: 'x', limit: 5 });

    fake.reply({ type: 'result', id: query.id, epoch: 1, results: [result('x.js')] });
    expect((await pending).map((r) => r.item)).toEqual(['x.js']);
  });

  test('resolves null for a reply from a superseded corpus (epoch mismatch)', async () => {
    const fake = new FakeWorker();
    const client = createSearchClient({ createWorker: () => fake });

    client.setFiles(['a.js']); // epoch 1
    const pending = client.search('a');
    const query = fake.queries().at(-1);

    client.setFiles(['b.js']); // epoch 2 — corpus replaced while the query is in flight
    fake.reply({ type: 'result', id: query.id, epoch: 1, results: [result('a.js')] });

    await expect(pending).resolves.toBeNull();
  });

  test('correlates by id so concurrent searches never cross', async () => {
    const fake = new FakeWorker();
    const client = createSearchClient({ createWorker: () => fake });
    client.setFiles(['a.js', 'b.js']);

    const pa = client.search('a');
    const pb = client.search('b');
    const [qa, qb] = fake.queries();

    // Reply out of order; each promise must still get its own result.
    fake.reply({ type: 'result', id: qb.id, epoch: 1, results: [result('b.js')] });
    fake.reply({ type: 'result', id: qa.id, epoch: 1, results: [result('a.js')] });

    expect((await pa).map((r) => r.item)).toEqual(['a.js']);
    expect((await pb).map((r) => r.item)).toEqual(['b.js']);
  });

  test('ignores an unknown/duplicate reply id', async () => {
    const fake = new FakeWorker();
    const client = createSearchClient({ createWorker: () => fake });
    client.setFiles(['a.js']);
    const pending = client.search('a');
    const query = fake.queries().at(-1);

    fake.reply({ type: 'result', id: 9999, epoch: 1, results: [result('nope.js')] });
    fake.reply({ type: 'result', id: query.id, epoch: 1, results: [result('a.js')] });
    // A second reply for the same (now-settled) id is a no-op, not a throw.
    fake.reply({ type: 'result', id: query.id, epoch: 1, results: [result('a.js')] });

    expect((await pending).map((r) => r.item)).toEqual(['a.js']);
  });

  test('degrades to synchronous search when the worker errors', async () => {
    const fake = new FakeWorker();
    const client = createSearchClient({ createWorker: () => fake });
    client.setFiles(['src/app.js', 'README.md']);

    const pending = client.search('app'); // in flight when the worker dies
    fake.fail();

    expect(client.usingWorker).toBe(false);
    expect(fake.terminated).toBe(true);

    // The in-flight promise is resolved from the main-thread index…
    expect((await pending).map((r) => r.item)).toContain('src/app.js');
    // …and later searches keep working synchronously.
    const later = await client.search('read');
    expect(later.map((r) => r.item)).toContain('README.md');
  });

  test('dispose terminates the worker', () => {
    const fake = new FakeWorker();
    const client = createSearchClient({ createWorker: () => fake });
    client.dispose();
    expect(fake.terminated).toBe(true);
    expect(client.usingWorker).toBe(false);
  });

  test('dispose resolves an in-flight query (null) instead of hanging', async () => {
    const fake = new FakeWorker();
    const client = createSearchClient({ createWorker: () => fake });
    client.setFiles(['a.js']);
    const pending = client.search('a'); // worker will never reply
    client.dispose();
    await expect(pending).resolves.toBeNull();
  });
});
