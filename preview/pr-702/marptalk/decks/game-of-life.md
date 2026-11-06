---
marp: true
title: Conway's Game of Life
theme: gaia
class: invert
paginate: true
lang: en-US
style: |
  section {
    font-size: 32px;
  }
  pre {
    font-size: 30px;
    line-height: 1.1;
    background: transparent;
    border: 0;
  }
  pre code {
    background: transparent;
    color: var(--color-foreground);
  }
  .row {
    display: flex;
    justify-content: center;
    gap: 64px;
    align-items: flex-start;
  }
  .row > div {
    flex: 0 0 300px;
  }
  .row pre code {
    font-size: 40px;
    line-height: 1.1;
  }
  .row p {
    margin: 8px 0 0;
    font-size: 26px;
    text-align: center;
  }
  .split {
    display: grid;
    grid-template-columns: 1fr auto;
    gap: 48px;
    align-items: center;
  }
  svg {
    display: block;
    margin: 32px auto 0;
  }
  table {
    font-size: 32px;
  }
---

<!-- _class: lead invert -->
<!-- _paginate: false -->

# Conway's Game of Life

A grid, two states, and four rules

<!--
In 1970 the mathematician John Conway invented a game with no players. You set up a pattern of cells on a grid, press go, and watch. Martin Gardner wrote about it in Scientific American that October, and people have been finding new patterns ever since. Here's how it works, and why something so simple turned out to be as powerful as a computer.
-->

---

# The board

<div class="split">
<div>

- An endless grid of square cells
- Each cell is alive or dead
- Each cell has eight neighbors
- Every cell updates at once, each generation

</div>

<svg viewBox="0 0 320 320" width="320" role="img" aria-label="A cell and the eight cells around it">
  <rect x="3" y="3" width="58" height="58" rx="6" fill="currentColor" fill-opacity="0.12" />
  <rect x="67" y="3" width="58" height="58" rx="6" fill="currentColor" fill-opacity="0.12" />
  <rect x="131" y="3" width="58" height="58" rx="6" fill="currentColor" fill-opacity="0.12" />
  <rect x="195" y="3" width="58" height="58" rx="6" fill="currentColor" fill-opacity="0.12" />
  <rect x="259" y="3" width="58" height="58" rx="6" fill="currentColor" fill-opacity="0.12" />
  <rect x="3" y="67" width="58" height="58" rx="6" fill="currentColor" fill-opacity="0.12" />
  <rect x="67" y="67" width="58" height="58" rx="6" fill="#ffca28" fill-opacity="0.85" />
  <rect x="131" y="67" width="58" height="58" rx="6" fill="#ffca28" fill-opacity="0.85" />
  <rect x="195" y="67" width="58" height="58" rx="6" fill="#ffca28" fill-opacity="0.85" />
  <rect x="259" y="67" width="58" height="58" rx="6" fill="currentColor" fill-opacity="0.12" />
  <rect x="3" y="131" width="58" height="58" rx="6" fill="currentColor" fill-opacity="0.12" />
  <rect x="67" y="131" width="58" height="58" rx="6" fill="#ffca28" fill-opacity="0.85" />
  <rect x="131" y="131" width="58" height="58" rx="6" fill="currentColor" />
  <rect x="195" y="131" width="58" height="58" rx="6" fill="#ffca28" fill-opacity="0.85" />
  <rect x="259" y="131" width="58" height="58" rx="6" fill="currentColor" fill-opacity="0.12" />
  <rect x="3" y="195" width="58" height="58" rx="6" fill="currentColor" fill-opacity="0.12" />
  <rect x="67" y="195" width="58" height="58" rx="6" fill="#ffca28" fill-opacity="0.85" />
  <rect x="131" y="195" width="58" height="58" rx="6" fill="#ffca28" fill-opacity="0.85" />
  <rect x="195" y="195" width="58" height="58" rx="6" fill="#ffca28" fill-opacity="0.85" />
  <rect x="259" y="195" width="58" height="58" rx="6" fill="currentColor" fill-opacity="0.12" />
  <rect x="3" y="259" width="58" height="58" rx="6" fill="currentColor" fill-opacity="0.12" />
  <rect x="67" y="259" width="58" height="58" rx="6" fill="currentColor" fill-opacity="0.12" />
  <rect x="131" y="259" width="58" height="58" rx="6" fill="currentColor" fill-opacity="0.12" />
  <rect x="195" y="259" width="58" height="58" rx="6" fill="currentColor" fill-opacity="0.12" />
  <rect x="259" y="259" width="58" height="58" rx="6" fill="currentColor" fill-opacity="0.12" />
</svg>

</div>

<!--
The board is a grid that goes on forever in every direction. Each square is a cell, and each cell is either alive or dead. A cell's neighbors are the eight cells that touch it, including the diagonals, like the yellow ring around the cell in the picture. Time moves in steps called generations, and on each step every cell on the board updates at the same moment.
-->

---

# The rules

| A cell that is | with this many live neighbors | becomes |
| --- | :---: | --- |
| alive | 0 or 1 | dead |
| alive | 2 or 3 | alive |
| alive | 4 or more | dead |
| dead | exactly 3 | alive |

<!--
Here are all the rules. A live cell with fewer than two live neighbors dies, as if from loneliness. A live cell with two or three neighbors survives. A live cell with four or more dies of overcrowding. And a dead cell with exactly three live neighbors comes to life. That's it. Fans write it as B three slash S two three: born on three, survive on two or three.
-->

---

# Still lifes never change

<div class="row">
<div>

```text
. . . .
. # # .
. # # .
. . . .
```

Block

</div>
<div>

```text
. . . . . .
. . # # . .
. # . . # .
. . # # . .
. . . . . .
```

Beehive

</div>
</div>

<!--
Some patterns settle down and stop. These are still lifes. In the block, every live cell has exactly three live neighbors, so all four survive, and no dead cell has exactly three, so nothing is born. The beehive is stable for the same reason. Most random starting patterns end up as a scatter of blocks, beehives, and a few other still lifes.
-->

---

# Oscillators repeat

<div class="row">
<div>

```text
. . . . .
. . # . .
. . # . .
. . # . .
. . . . .
```

Generation 1

</div>
<div>

```text
. . . . .
. . . . .
. # # # .
. . . . .
. . . . .
```

Generation 2

</div>
</div>

<!--
Other patterns cycle forever. This one is the blinker. The middle cell always has two neighbors, so it survives. The two end cells have only one neighbor each, so they die. Meanwhile the cells to the left and right of the middle each see three live neighbors, so they're born. The line flips from vertical to horizontal and back, with a period of two generations.
-->

---

# The glider travels

<svg viewBox="0 0 1088 274" width="1088" role="img" aria-label="Four generations of a glider, each shifted toward the lower right">
  <rect x="2" y="2" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="58" y="2" width="52" height="52" rx="4" fill="currentColor" />
  <rect x="114" y="2" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="170" y="2" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="2" y="58" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="58" y="58" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="114" y="58" width="52" height="52" rx="4" fill="currentColor" />
  <rect x="170" y="58" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="2" y="114" width="52" height="52" rx="4" fill="currentColor" />
  <rect x="58" y="114" width="52" height="52" rx="4" fill="currentColor" />
  <rect x="114" y="114" width="52" height="52" rx="4" fill="currentColor" />
  <rect x="170" y="114" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="2" y="170" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="58" y="170" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="114" y="170" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="170" y="170" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <text x="112" y="262" text-anchor="middle" font-size="26" fill="currentColor">generation 0</text>
  <polygon points="242,100 272,112 242,124" fill="currentColor" fill-opacity="0.6" />
  <rect x="290" y="2" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="346" y="2" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="402" y="2" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="458" y="2" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="290" y="58" width="52" height="52" rx="4" fill="currentColor" />
  <rect x="346" y="58" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="402" y="58" width="52" height="52" rx="4" fill="currentColor" />
  <rect x="458" y="58" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="290" y="114" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="346" y="114" width="52" height="52" rx="4" fill="currentColor" />
  <rect x="402" y="114" width="52" height="52" rx="4" fill="currentColor" />
  <rect x="458" y="114" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="290" y="170" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="346" y="170" width="52" height="52" rx="4" fill="currentColor" />
  <rect x="402" y="170" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="458" y="170" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <text x="400" y="262" text-anchor="middle" font-size="26" fill="currentColor">generation 1</text>
  <polygon points="530,100 560,112 530,124" fill="currentColor" fill-opacity="0.6" />
  <rect x="578" y="2" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="634" y="2" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="690" y="2" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="746" y="2" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="578" y="58" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="634" y="58" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="690" y="58" width="52" height="52" rx="4" fill="currentColor" />
  <rect x="746" y="58" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="578" y="114" width="52" height="52" rx="4" fill="currentColor" />
  <rect x="634" y="114" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="690" y="114" width="52" height="52" rx="4" fill="currentColor" />
  <rect x="746" y="114" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="578" y="170" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="634" y="170" width="52" height="52" rx="4" fill="currentColor" />
  <rect x="690" y="170" width="52" height="52" rx="4" fill="currentColor" />
  <rect x="746" y="170" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <text x="688" y="262" text-anchor="middle" font-size="26" fill="currentColor">generation 2</text>
  <polygon points="818,100 848,112 818,124" fill="currentColor" fill-opacity="0.6" />
  <rect x="866" y="2" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="922" y="2" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="978" y="2" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="1034" y="2" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="866" y="58" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="922" y="58" width="52" height="52" rx="4" fill="currentColor" />
  <rect x="978" y="58" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="1034" y="58" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="866" y="114" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="922" y="114" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="978" y="114" width="52" height="52" rx="4" fill="currentColor" />
  <rect x="1034" y="114" width="52" height="52" rx="4" fill="currentColor" />
  <rect x="866" y="170" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <rect x="922" y="170" width="52" height="52" rx="4" fill="currentColor" />
  <rect x="978" y="170" width="52" height="52" rx="4" fill="currentColor" />
  <rect x="1034" y="170" width="52" height="52" rx="4" fill="currentColor" fill-opacity="0.12" />
  <text x="976" y="262" text-anchor="middle" font-size="26" fill="currentColor">generation 3</text>
</svg>

<!--
Then there are spaceships, which move. The smallest is the glider: five cells that cycle through four shapes. After four generations it looks exactly like it did at the start, shifted one cell down and one cell to the right. So it crawls diagonally across the board forever, at a quarter of the fastest speed anything in Life can go.
-->

---

# Guns make gliders

- Conway offered $50 for a pattern that grows forever
- Bill Gosper's team at MIT won it in November 1970
- The Gosper glider gun fires a new glider every 30 generations

<!--
Conway guessed that no pattern could grow without limit, and offered a fifty dollar prize to anyone who could prove him right or wrong. A month after Gardner's column, Bill Gosper and a group at M I T found a pattern that fires a new glider every thirty generations. It runs forever, and the number of live cells keeps growing. Conway paid up.
-->

---

# Life can compute anything

- Gliders carry signals
- Colliding streams of gliders act as logic gates
- Gates combine into memory and a processor

<!--
That gun was the key to something bigger. A stream of gliders can carry a signal, where a glider means one and a gap means zero. Aim two streams at each other and the collisions behave like logic gates. From gates you can build memory, counters, and eventually a whole computer. Conway showed that Life is universal: given a big enough board, it can compute anything a laptop can.
-->

---

# Some questions have no answer

- Will this pattern ever die out?
- No algorithm can decide that for every pattern
- The only general method is to run it and watch

<!--
Being universal has a strange consequence. Because Life can simulate any computer, asking whether a pattern eventually dies out is as hard as asking whether a program eventually stops, and Alan Turing proved that no algorithm can answer that in general. For four rules on a grid of squares, that is a remarkable amount of depth.
-->

---

<!-- _class: lead invert -->

# Try it

Draw a pattern in **life-lab** in this playground and print its history in 3D

<!--
The best way to understand Life is to play with it. Draw a pattern, step it forward, and see whether it dies, settles, or flies away. The life lab app in this playground lets you draw a starting pattern and turn its history into a 3D printable sculpture, with time running up the vertical axis. Gliders become little diagonal staircases.
-->
