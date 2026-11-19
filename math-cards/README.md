# Math Cards

Math flash cards for kids. Each card shows a problem, such as
`23 + 45 = ?`, and two answers. One answer is right. Pick it by swiping the
card toward it on a phone, or by clicking it or pressing the Left or Right
arrow key on a computer.

A right answer fills in the card and sends it flying. A wrong answer shakes
the card and shows the right answer for a moment before the next card.
Every 10 right answers in a row bursts digits and that card's operator
across the screen.

## Modes

The buttons at the top pick the problems. The page remembers the choice in
`localStorage` under `math-cards:mode`. The problems stay at first- and
second-grade level:

- **+** adds two numbers, each at least 1, with sums up to 100. The page
  picks the sum first, so small and large sums come up equally often.
- **−** subtracts within 100. The answer is at least 1.
- **× ÷** mixes multiplication and division about evenly, with factors from
  1 to 5. Division always comes out even.

The wrong answer is a mistake a child might make. For addition and
subtraction, it is off by one or two, off by ten from a missed carry or
borrow, the digits swapped, or, for subtraction, the two numbers added. For
multiplication, it is one group too many or too few, off by one, or the two
numbers added. For division, it is off by one, the divisor, or the two
numbers subtracted.

Each mode keeps its own number of cards answered, number right, current
streak, and best streak in `localStorage` under `math-cards:v1:<mode>`.
Addition also reads `math-cards:v1`, where the page kept its stats before it
had modes.

## Adding problem kinds

`src/problems.js` keeps the problem kinds in `KINDS`. A kind has defaults,
`generate(rng, options)`, which returns the operands, operator, and answer,
and `distractors(problem, options)`, which lists believable wrong answers.
`MODES` maps each mode to the kinds it deals from, picking one at random for
each card. Three or more addends, larger sums, or bigger times tables are
each a new kind, or new options to an existing kind such as a larger `max`
or `maxFactor`. A new mode also needs a button with its `data-mode` in
`index.html`. The card and the stats don't depend on the kind.

## Run locally

```bash
npm start
```

Open http://localhost:3000. Tests:

```bash
npm test
```
