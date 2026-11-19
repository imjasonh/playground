# Math Cards

Addition flash cards for kids. Each card shows a problem, such as
`23 + 45 = ?`, and two answers. One answer is right. Pick it by swiping the
card toward it on a phone, or by clicking it or pressing the Left or Right
arrow key on a computer.

A right answer fills in the card and sends it flying. A wrong answer shakes
the card and shows the right answer for a moment before the next card.
Every 10 right answers in a row bursts digits and plus signs across the
screen.

Sums go up to 100, and both numbers are at least 1. The page picks the sum
first, so small and large sums come up equally often. The wrong answer is a
mistake a child might make: off by one or two, off by ten from a missed or
extra carry, or the digits swapped.

The page keeps the number of cards answered, the number right, the current
streak, and the best streak in `localStorage` under `math-cards:v1`.

## Adding problem kinds

`src/problems.js` keeps the problem kinds in `KINDS`. A kind has defaults,
`generate(rng, options)`, which returns the operands, operator, and answer,
and `distractors(problem, options)`, which lists believable wrong answers.
Subtraction, multiplication, division, three or more addends, or larger
sums are each a new kind, or new options to `addition` such as a larger
`max`. The card and the stats don't depend on the kind.

## Run locally

```bash
npm start
```

Open http://localhost:3000. Tests:

```bash
npm test
```
