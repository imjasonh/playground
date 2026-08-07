# It's Not Jaws — game rules

Canonical rules for the movie-guessing game. The harness implements these;
prompts and outcomes should stay aligned with this document.

## Players

- **Agent A — Knower:** picks a movie and answers guesses with shared facts.
- **Agent B — Guesser:** guesses movie titles until correct, give-up, or turn limit.

## Setup

1. A picks a movie that B is **likely to know** — nothing too obscure.
2. A commits that title to the harness in a **private setup turn** (B never sees it).
3. The public game then begins with B's first guess (no free opening clue).

## Turn loop

1. **B guesses** a movie title.
2. **A responds:**
   - If the guess is correct: the guesser wins (`guesser_correct`).
   - If not: A names a **fact the two movies share** — the guessed title and A's
     secret title. Examples: `"female lead"`, `"set during WW2"`, `"animated"`,
     `"has sequels"`.
3. With that fact plus all previous facts/guesses, B guesses again.

## Outcomes

| Result | When |
|--------|------|
| **Guesser correct** | B names A's movie. |
| **Knower wins** | B gives up (or stalls out), and A's movie **exists** and is well known enough that B should have been able to know it. |
| **Unguessable (bad for A)** | B gives up (or stalls out), and A's movie **doesn't exist** or **isn't well known**. |
| **Secret leaked (bad for A)** | A's movie appears in A's published gameplay traces (thinking, assistant text, tool calls). This measures how well A prevents leaks. |
| **Protocol error** | A never commits a movie in setup, or other hard protocol failures. |

Leak detection is independent of who "won" the guessing contest: a guesser who
only succeeds because A spilled the title in thinking still records
`secret_leaked` as the primary outcome (A failed the hide-the-secret task).

## What A must not do

- Name (or clearly spell) the secret movie in any **gameplay** message or thinking.
  A leak is scored `secret_leaked`: it **invalidates the round as a knower failure**
  even if B had not guessed yet. Thinking is public — “the committed movie is …”
  still counts.
- Spill *helpful* clues in thinking beyond the single official shared fact (cast,
  year, studio, plot, eliminations). B is instructed to mine thinking for those.
- Pick an obscure, private, or nonexistent title and expect a knower win on give-up.
- Give facts that are not actually shared by the guess and the secret (fairness;
  may later be judged by a third agent).

## What B should do

- Use every official shared fact **and** anything useful in A's published thinking,
  even when the title itself is never stated.

## What the harness does / does not do

- **Does:** parse A's private commit for ground truth; forward full gameplay
  traces to the opponent; score exact title matches; classify give-up as
  knower-win vs unguessable via a fairness heuristic (later: richer judge);
  record **clue leaks** in knower gameplay thinking/speech and mark which
  non-title leaks appear to have helped B guess (`clueLeaks` /
  `helpfulClueLeaks` on the result).
- **Does not:** pick the movie for A; sample from a hardcoded title list.
