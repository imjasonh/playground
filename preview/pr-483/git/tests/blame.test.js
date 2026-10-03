import { blameLines } from '../src/blame.js';

const enc = (s) => new TextEncoder().encode(s);

// Build a version list (newest first) from [oid, content] pairs, tagging each
// commit so we can assert which one a line is attributed to by oid.
function versions(...pairs) {
  return pairs.map(([oid, content]) => ({ commit: { oid, message: `c ${oid}` }, content }));
}

/** The oid attributed to each line, for compact assertions. */
function oids(rows) {
  return rows.map((r) => r.commit.oid);
}

describe('blameLines', () => {
  test('returns one row per line of the newest version, in order', () => {
    const rows = blameLines(versions(['v1', 'a\nb\nc\n']));
    expect(rows.map((r) => r.line)).toEqual(['a', 'b', 'c']);
  });

  test('a single version attributes every line to that one commit', () => {
    const rows = blameLines(versions(['only', 'one\ntwo\nthree\n']));
    expect(oids(rows)).toEqual(['only', 'only', 'only']);
  });

  test('attributes added lines to the commit that introduced them', () => {
    // Oldest had two lines; the newer commit inserted a middle line.
    const rows = blameLines(
      versions(
        ['new', 'first\nMIDDLE\nlast\n'],
        ['old', 'first\nlast\n']
      )
    );
    expect(oids(rows)).toEqual(['old', 'new', 'old']);
  });

  test('a changed line is attributed to the commit that changed it', () => {
    const rows = blameLines(
      versions(
        ['v2', 'keep\nchanged-now\n'],
        ['v1', 'keep\nchanged-before\n']
      )
    );
    expect(oids(rows)).toEqual(['v1', 'v2']);
  });

  test('attributes across three versions with mixed authorship', () => {
    // v1: skeleton; v2: adds a render call; v3: adds persistence + a header.
    const v1 = 'const list = [];\nfunction toggle() {}\n';
    const v2 = 'const list = [];\nfunction toggle() {}\nrender(list);\n';
    const v3 = "import store from './store';\nconst list = [];\nfunction toggle() {}\nrender(list);\n";
    const rows = blameLines(versions(['v3', v3], ['v2', v2], ['v1', v1]));
    expect(oids(rows)).toEqual([
      'v3', // the new import line
      'v1', // const list — present since the start
      'v1', // function toggle — present since the start
      'v2', // render(list) — added in v2
    ]);
  });

  test('lines surviving to the oldest known version blame the oldest commit', () => {
    // "base" never changes, so it should fall through to the earliest commit.
    const rows = blameLines(
      versions(
        ['c3', 'base\nthree\n'],
        ['c2', 'base\ntwo\n'],
        ['c1', 'base\none\n']
      )
    );
    expect(rows[0]).toMatchObject({ line: 'base', commit: { oid: 'c1' } });
    expect(rows[1]).toMatchObject({ line: 'three', commit: { oid: 'c3' } });
  });

  test('accepts Uint8Array content (decodes bytes to text)', () => {
    const rows = blameLines(
      versions(
        ['new', enc('alpha\nbeta\n')],
        ['old', enc('alpha\n')]
      )
    );
    expect(rows.map((r) => r.line)).toEqual(['alpha', 'beta']);
    expect(oids(rows)).toEqual(['old', 'new']);
  });

  test('is empty for no versions or an empty newest version', () => {
    expect(blameLines([])).toEqual([]);
    expect(blameLines(undefined)).toEqual([]);
    expect(blameLines(versions(['v1', '']))).toEqual([]);
  });

  test('ignores versions without a commit', () => {
    const rows = blameLines([
      { content: 'x\n' }, // no commit — skipped, so the next is "newest"
      { commit: { oid: 'real' }, content: 'x\n' },
    ]);
    expect(oids(rows)).toEqual(['real']);
  });

  test('handles a full rewrite (no common lines) by blaming the newest', () => {
    const rows = blameLines(
      versions(
        ['rewrite', 'totally\ndifferent\n'],
        ['orig', 'old\ncontent\nhere\n']
      )
    );
    expect(oids(rows)).toEqual(['rewrite', 'rewrite']);
  });

  // diff.js refuses to build its LCS table past a cell cap (~4M = ~2000² lines),
  // which is far below the viewer's line limit. Blame must cope: a file that big
  // can't be diffed, and silently blaming every line on the oldest commit would
  // be confidently wrong for the whole file.
  const bigFile = (tag) => `${Array.from({ length: 2100 }, (_, i) => `${tag}${i}`).join('\n')}\n`;

  test('reports no blame when the newest pair is too large to diff', () => {
    // Two large, entirely different versions: the very first diff is declined,
    // so there is no real attribution — return empty rather than blame it all on
    // the oldest commit. The controller treats empty as "blame unavailable".
    const rows = blameLines(versions(['new', bigFile('a')], ['old', bigFile('b')]));
    expect(rows).toEqual([]);
  });

  test('keeps partial blame when only a deeper pair is too large to diff', () => {
    // Newest is tiny (one carried-over line + one new line), so its diff against
    // the large predecessor is cheap; only the predecessor-vs-oldest diff is too
    // large. The new line is still attributed; the survivor falls back to oldest.
    const rows = blameLines(
      versions(
        ['new', 'a0\nEXTRA\n'], // shares "a0" with the large predecessor
        ['mid', bigFile('a')],
        ['old', bigFile('b')]
      )
    );
    expect(rows.map((r) => r.line)).toEqual(['a0', 'EXTRA']);
    expect(oids(rows)).toEqual(['old', 'new']);
  });
});
